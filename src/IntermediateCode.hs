{-# OPTIONS_HADDOCK ignore-exports #-}
{-# LANGUAGE MultiWayIf #-}
{-|
  Module      : IntermediateCode
  Description : Builds an intermediate code representation from an abstract
                syntax tree.
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
                2016, Philip Schmiel
  License     : GPL-3
-}
module IntermediateCode (
  IntermediateCode.process
) where
import Prelude (
    Int,
    show,
    (+), ($), (++), (==),
    (||), (/=), (!!), (&&), (>), not,
    String, Bool (..), Maybe (..), error, putStrLn,
    fst, head, last, length, takeWhile, drop, concat
  )
import Control.Monad.State (
    State,
    runState, get, put, return
  )
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe (
    fromJust, isNothing, isJust
  )
import Data.String.Utils (
    split, endswith
  )

import Data.Int (
    Int64
  )

import qualified Interface.Token as T
import qualified Interface.AST as AST
import qualified Interface.TAC as TAC
import GarbageCollection.GarbageCollection (
    dealloc
  )
-- $| The generator state has to track two counters, one for the temporary
-- variables and one for the labels, the mapping from variable to data type,
-- return type. Function signatures, function labels and variable location names,
-- for each is a map required too.
type GenState = (TempCounter, LabelCounter, Environment, ReturnType, FunctionScopes, UDFLabels, Locations, DataLabelScopes)
-- | This is just a number.
type TempCounter = Int
-- | This is just a number.
type LabelCounter = Int
-- $| This is a mapping from variable to data type.
type Environment = [Map String String]
-- $| This is just a string.
type Type = String
-- $| This is just a string.
type ReturnType = String
-- $| This is a list of maps representing scopes of user-defined functions.
type FunctionScopes = [Map String String]
-- TODO docu| This is a Map of frontend label names to a tupel of
type DataLabelScopes = Map String [AST.Command]
-- $| This is a map of reserved labels for user-defined functions.
type UDFLabels = Map String [String]
-- $| This is a list of UDF names and TACs.
type TACstream = [(TAC.Label, TAC.TAC)]
-- $| This is a map of reserved locations.
type Locations = Map String [String]

--TODO docu
getType:: AST.Command -> String
getType (AST.Declaration t n) = show t

-- $| Given an abstract syntax tree it generates and intermediate representation
-- in three address code and an appendix with user-defined functions for later use.
process :: AST.AST -> TACstream -- $ modified
process ast = ("",directives):("",intermediateCode):appendix
  where
    ((directives,intermediateCode,appendix), _) = runState (program ast) (0,0,[Map.empty], "void", [Map.singleton "length" "length_:int:any[]"], Map.empty, Map.singleton "length" ["length_"],Map.empty)

-- | Generates a new label and increments the internal label counter.
newLabel :: State GenState TAC.Label
newLabel = do
  (t,l,s,r,f,u,a,d) <- get         -- $ modified
  put (t,l+1,s,r,f,u,a,d)          -- $ modified
  return $ "label" ++ show (l+1)

-- | Generates a new temporary variable and increments the internal variable
-- counter.
newTemp :: State GenState TAC.Variable
newTemp = do
  (t,l,s,r,f,u,a,d) <- get     -- $ modified
  put (t+1,l,s,r,f,u,a,d)      -- $ modified
  return $ "#" ++ show (t+1)

-- | Returns the variable given as parameter. To be used in 'expressionInto'.
fixedVar :: TAC.Variable -> State GenState TAC.Variable
fixedVar = return

-- $| Looks up type of variable.
lookup :: String -> Bool -> State GenState (Maybe String)
lookup i u = do
  (_,_,s,_,f,_,_,_) <- get
  let type_ = if u then scopes i f else scopes i s
  return type_
  where
    scopes :: String -> Environment -> Maybe String
    scopes _ [] = Nothing
    scopes i (m:_)
          | isJust _type = _type
        where 
          _type = Map.lookup i m
    scopes i (_:mm) = scopes i mm

lookupLabel :: String -> State GenState (Maybe [AST.Command])
lookupLabel str = do
  (_,_,_,_,_,_,_,labelMap) <- get
  return $ Map.lookup str labelMap

-- $| Changes the unique ID of a variable which correspond to a machine location.
insert :: String -> String -> Environment -> Environment
insert i v (m:mm)
  | isJust type_ = (Map.insert i v m):mm
  where type_ = Map.lookup i m
insert i v (m:mm) = m:(insert i v mm)

-- $| Assigns a unique ID to a variable which correspond to a machine location.
newAlt :: String -> Locations -> (String, Locations)
newAlt i m = (name, a')
  where
    names = Map.lookup i m
    (name, a') = if isNothing names then (i ++ "_", Map.insert i [name] m) else (i ++ "_" ++ (show $ length $ fromJust names), Map.insert i ((fromJust names) ++ [name]) m)

-- $| Generates three address code for a complete program and an appendix with user-defined functions for later use.
program :: AST.AST -> State GenState (TAC.TAC, TAC.TAC, TACstream) -- $ modified
program prog = do
  next <- newLabel
  (directives,tac, udf, rt1) <- command prog next
  (_,_,_,r,_,_,_,_) <- get
  let (function, rt2) = let list = split ":" r in (head list, last list)
  if r == "void" || rt1 == rt2
    then return (directives, tac ++ [TAC.Label next], udf)
  else error $ "UDF " ++ function ++ " has no return value."

-- $| Generates three address code for one specific command in the AST,
-- an appendix with user-defined functions for later use and
-- checks the existence of a return statement.
command :: AST.Command -> TAC.Label -> State GenState (TAC.TAC, TAC.TAC, TACstream, ReturnType) -- $ modified
command cmd next = case cmd of
  AST.Output e -> do -- $ modified
    (directive,tac,data_,type_) <- expression e
    if type_ == "int"
          then return (directive,tac ++ [TAC.Output data_], [], "")
        else if type_ == "double"
          then return (directive,tac ++ [TAC.FOutput data_], [], "")
        else if type_ == "char"
          then return (directive,tac ++ [TAC.COutput data_], [], "")
        else error "No native support for outputting arrays."
  AST.Return e -> do -- $ added
    (directive,tac,data_,type_) <- expression e
    (_,_,_,r,_,_,_,_) <- get
    let (function, rt) = let list = split ":" r in (head list, last list)
    if r == "void"
          then return (directive,[], [], "")
    else if type_ /= rt
          then error $ "A return instruction in UDF " ++ function ++ " delivers a value of wrong type."
    else if type_ == "double"
          then return (directive,tac ++ [TAC.FReturn data_], [], type_)
        else return (directive,tac ++ [TAC.Return data_], [], type_)
  AST.Read i -> do -- $ modified
    type_ <- lookup i False
    if endswith "]" $ fromJust type_
      then error $ "No native support for inputting arrays, i.e. to array " ++ i ++ "."
    else if endswith "int" $ fromJust type_
          then return ([],[TAC.Read $ fromJust type_], [], "")
        else if endswith "double" $ fromJust type_
          then return ([],[TAC.FRead $ fromJust type_], [], "")
        else if endswith "char" $ fromJust type_
          then return ([],[TAC.CRead $ fromJust type_], [], "")
        else error $ "Variable " ++ i ++ " has not been declared."
  AST.Skip -> return ([],[], [], "")
  AST.Sequence c1 c2 -> do -- $ modified
    next1 <- newLabel
    (directives1,tac1,udf1,rt1)  <- command c1 next1
    (directives2,tac2,udf2,rt2)  <- command c2 next
    return (directives1++directives2, tac1 ++ [TAC.Label next1] ++ tac2, udf1 ++ udf2, if rt1 /= "" then rt1 else rt2)
  AST.IfThen b c -> do
    true <- newLabel
    (direxp, btac) <- boolExpression b true next
    (directive,tac,udf,rt) <- command c next -- $ modified
    return (direxp++directive,btac ++ [TAC.Label true] ++ tac, udf, rt) -- $ modified
  AST.IfThenElse b c1 c2 ->do
    true <- newLabel
    false <- newLabel
    (direxp, btac) <- boolExpression b true false
    (directive1, tac1,udf1,rt1) <- command c1 next -- $ modified
    (directive2, tac2,udf2,rt2) <- command c2 next -- $ modified
    return (direxp++directive1 ++ directive2, btac ++ [TAC.Label true] ++ tac1 ++ [TAC.Goto next, TAC.Label false] ++ tac2, udf1 ++ udf2, if rt1 /= "" then rt1 else rt2) -- $ modified
  AST.While b c -> do
    true <- newLabel
    (direxp,btac) <- boolExpression b true next
    begin <- newLabel
    (directive, tac,udf,rt) <- command c begin -- $ modified
    return (direxp++directive,[TAC.Label begin] ++ btac ++ [TAC.Label true] ++ tac ++ [TAC.Goto begin], udf, rt) -- $ modified
  AST.Assign i e -> do -- $ modified
    type1 <- lookup i False
    (directive,tac,data_,type2) <- expressionInto (fixedVar i) e
    if isNothing type1
      then error $ "Variable " ++ i ++ " has not been declared."
    else if not $ endswith type2 (fromJust type1)
          then error $ "Assignment of an expression to Variable " ++ i
        ++ " not possible due to type conflict."++(type2)++"/"++(show $ fromJust type1) --TODO remove debug
    else if not $ endswith "[]" (fromJust type1)
      then return (directive, tac ++ if data_ == TAC.Variable (fromJust type1) then [] else [TAC.Copy (fromJust type1) data_], [], "")
    else do
      (t,l,env@(s:_),r,f,u,a,dataLabel) <- get
      let env' = insert i (show data_) env
      put (t,l,env',r,f,u,a,dataLabel)
      if isNothing $ Map.lookup i s
        then return (directive, tac ++ [TAC.ArrayCopy (show data_) data_], [], "")
      else return (directive, tac ++ if data_ == TAC.Variable (fromJust type1) || r /= "void" then [] else [TAC.ArrayCopy (fromJust type1) data_], [], "")
  AST.ToArray i e1 e2 -> do -- $ added
    type_ <- lookup i False
    if isNothing type_
          then error $ "Array " ++ i ++ " has not been declared."
    else if not $ endswith "]" $ fromJust type_
          then error $ "Name " ++ i ++ " does not denote an array."
        else do
      (directive1,tac1,data1,type1) <- expression e1
      if type1 /= "int"
        then error $ "Elements of array " ++ i ++ " only accessible via int indices."
      else do
        let signature = split ":" $ fromJust type_
        (directive2, tac2,data2,type2) <- expression e2
        if type2 /= (takeWhile (/= '[') $ last signature)
          then error $ "Assignment of an expression to array " ++ i ++ " not possible due to type conflict."
        else return (directive1++directive2,tac1 ++ tac2 ++ [TAC.ToArray (fromJust type_) data1 data2], [], "")
  AST.Declaration _type i -> do -- $$ added
    (t,l,s:ss,r,f,u,a,dataLabel) <- get
    let type_ = Map.lookup i s
    if isJust type_
      then error $ "Name " ++ i ++ " is already used."
    else do
      let (name, a') = newAlt i a
      put (t,l,(Map.insert i (name ++ ":" ++ show _type) s):ss,r,f,u,a',dataLabel)
      return ([],[], [], "")
  AST.ArrayDecl _type i -> do -- $$ added
    (t,l,s:ss,r,f,u,a,dataLabel) <- get
    let type_ = Map.lookup i s
    if isJust type_
      then error $ "Name " ++ i ++ " is already used."
    else do
      let (name, a') = newAlt i a
      put (t,l,(Map.insert i (name ++ ":" ++ show _type ++ "[]") s):ss,r,f,u,a',dataLabel)
      return ([],[], [], "")
  AST.ArrayAlloc _type e i -> do -- $$ added
    (t,l,s:ss,r,f,u,a,dataLabel) <- get
    let type_ = Map.lookup i s
    if isJust type_
      then error $ "Name " ++ i ++ " is already used."
    else do
      (directive, tac,data_,type1) <- expression e
      if type1 /= "int"
        then error $ "Array " ++ i ++ "must be declared with int size."
      else do
        let type_ = case data_ of
              TAC.ImmediateInteger n | n > -1 -> show _type ++ "[]"
              TAC.Variable _ -> show _type ++ "[]"
              _ -> error $ "Array " ++ i ++ "must be declared with int size >= 0."
        let (name, a') = newAlt i a
        let signature = name ++ ":" ++ type_
        put (t,l,(Map.insert i signature s):ss,r,f,u,a',dataLabel)
        return (directive, tac ++ [TAC.ArrayAlloc signature data_] ++ [TAC.Push $ TAC.Variable signature], [], "")
  AST.Environment c -> do -- $$ added
    (t,l,s,r,f,u,a,dataLabel) <- get
    put (t,l,Map.empty:s,r,Map.empty:f,u,a,dataLabel)
    (directive, tac,udf,rt) <- command c next
    put (t,l,s,r,f,u,a,dataLabel)
    return (directive, tac ++ (dealloc tac), udf, rt)
  AST.Function d p c -> do -- $$ added
    (t,l,s,r,f:ff,u,a,dataLabel) <- get
    let i = case d of
          AST.Declaration _type i -> i
          AST.ArrayDecl _type i -> i
    let signature = Map.lookup i f
    if isJust signature
          then error $ "User-defined function " ++ i ++ " already defined."
    else do
      let state = (0,0,[Map.empty],"",f:ff,u,Map.empty,dataLabel)
      let (directive, f',u',udf) = function d p c state
      put (t,l,s,r,f',u',Map.empty,dataLabel)
      return (directive, [], udf, "")
  AST.LabelEnvironment name labels -> do
    (t,l,s,r,f:ff,u,a,dataLabel) <- get
    let cmdList = Map.lookup (name++":") dataLabel
    let cmdList' = if isNothing cmdList then [] else (fromJust cmdList)
    let dataLabel' = Map.insert (name++":") (labels:cmdList') dataLabel
    let (dataLabel'',tac) = labelenvironment name labels (t,l,s,r,f:ff,u,a,dataLabel') 
    put (t,l,s,r,f:ff,u,a,dataLabel'')
    return (tac,[],[],"")
  
-- $| Generates three address code for one expression in the AST (possibly
-- generating code for subexpressions first) and determines its type.
expression :: AST.Expression -> State GenState (TAC.TAC,TAC.TAC,TAC.Data,Type)
expression = expressionInto newTemp

-- | Generates three address code for one expression in the AST (possibly
-- generating code for subexpressions first). The additional parameter will be
-- evaluated if code for something other than number or identifier is generated
-- and the returned variable will be used for the result.
-- $ Determines also its type.
expressionInto :: State GenState TAC.Variable -> AST.Expression
               -> State GenState (TAC.TAC,TAC.TAC,TAC.Data,Type) -- $ modified
expressionInto varFunc expr = case expr of
  AST.Calculation op e1 e2 -> do -- $ modified
    (dir1, tac1,data1,type1) <- expression e1
    (dir2, tac2,data2,type2) <- expression e2
    if endswith "]" type1 || endswith "]" type2
      then error "Cannot use an array as a whole in a calculation."
    else do
      let tacCommand1 = case op of
                T.Mod   -> \_ -> error "Modulo only applicable to Integers"
                T.Plus  -> TAC.FAdd
                T.Minus -> TAC.FSub
                T.Times -> TAC.FMul
                T.DivBy -> TAC.FDiv
      let tacCommand2 = case op of
                T.Mod   -> TAC.Mod
                T.Plus  -> TAC.Add
                T.Minus -> TAC.Sub
                T.Times -> TAC.Mul
                T.DivBy -> TAC.Div
      var2 <- newTemp
      let var2' = var2 ++ ":double"
      let varInt' = var2 ++ ":int"
      let (type_, tacCommand, coercion, data', data1', data2') = case (type1, type2) of
             ("int", "int")       -> ("int", tacCommand2, [], data1, data1, data2)
             ("double", "double") -> ("double", tacCommand1, [], data1, data1, data2)
             ("char", "char") -> ("char",tacCommand2, [], data1, data1,data2)
             ("double", "int")        -> case data2 of
               TAC.Variable _ -> ("double", tacCommand1, [TAC.Convert var2' data'], data2, data1, TAC.Variable var2')
               _ -> ("double", tacCommand1, [], data1, data1, data2)
             ("int", "double")        -> case data1 of
               TAC.Variable _ -> ("double", tacCommand1, [TAC.Convert var2' data'], data1, TAC.Variable var2', data2)
               _ -> ("double", tacCommand1, [], data1, data1, data2)
             ("int","char") -> case data2 of
               TAC.Variable _ -> ("int", tacCommand2, [TAC.ConvertInt varInt' data'], data2, data1, TAC.Variable varInt')
               _ -> ("int", tacCommand2, [], data1, data1, data2)
             ("char","int") -> case data1 of
               TAC.Variable _ -> ("int", tacCommand2, [TAC.ConvertInt varInt' data'], data1, TAC.Variable varInt', data2)
               _ -> ("int", tacCommand2, [], data1, data1, data2)
      var1 <- varFunc
      type3 <- lookup var1 False
      let var1' = if isNothing type3 then var1 ++ ":" ++ type_ else fromJust type3
      return (dir1++dir2,tac1 ++ tac2 ++ coercion ++ [tacCommand var1' data1' data2'], TAC.Variable var1', type_)
  AST.Negate e -> do
    (directive, tac,data_,type1) <- expression e -- $ modified
    if endswith "]" type1 -- $ added
      then error "Cannot use an array as a whole in a negation."
    else do
      var <- varFunc
      type2 <- lookup var False
      let var' = if isNothing type2 then var ++ ":" ++ type1 else fromJust type2
      return (directive, tac ++ [if type1 == "double" then TAC.FNeg var' data_ else TAC.Neg var' data_], TAC.Variable var', type1) -- $ modified
  AST.Identifier i -> do -- $ modified
    type_ <- lookup i False
    if isNothing type_
        then do
            funcType <- lookup i True
            if isNothing funcType
              then error $ "Variable " ++ i ++ " has not been declared."
            else do
              --Identifier is a function
              let returnType = concat $ drop 1 $ split ":" $ fromJust funcType
              let funcName = head $ split ":" $ fromJust funcType
              return ([],[], TAC.ImmediateReference [] funcName, returnType)
        else do
          --Identifier is a variable
          let returnType = last $ split ":" $ fromJust type_
          return ([],[], TAC.Variable $ fromJust type_, returnType)
  AST.FromArray i e -> do -- $ added
    type1 <- lookup i False
    if isNothing type1
          then error $ "Array " ++ i ++ " has not been declared."
    else if not $ endswith "]" $ fromJust type1
          then error $ "Name " ++ i ++ " does not denote an array."
        else do
      (directive, tac,data_,type2) <- expression e
      if type2 /= "int"
        then error $ "Elements of array " ++ i ++ " only accessible via int indices."
      else do
        let signature = split ":" $ fromJust type1
        var <- varFunc
        type3 <- lookup var False
        let returnType = (takeWhile (/= '[') $ last signature)
        let var' = if isNothing type3 then var ++ ":" ++ returnType else fromJust type3
        return (directive, tac ++ [TAC.FromArray var' (fromJust type1) data_], TAC.Variable var', returnType)
  AST.Parameter e -> do -- $ added
    (directive, tac,data_,type_) <- expression e
    return (directive, tac ++ [TAC.Push data_], data_, type_)
  AST.Parameters e1 e2 -> do -- $ added
    (directive1, tac1,_,type1) <- expression e1
    (directive2, tac2,data_,type2) <- expression e2
    return (directive1++directive2,tac1 ++ tac2, data_, type1 ++";"++ type2)
  AST.Func i p -> do -- $ added
    ftype <- lookup i True
    vtype <- lookup i False
    let type_ = if isNothing ftype then vtype else ftype
    if isNothing type_
      then error $ "User-defined function " ++ i ++ " not in scope."
    else do
      (directive, tac,_,params1') <- expression p
      let params1 = "("++params1'++")"
      let signature = split ":" $ fromJust type_
      let name = head signature
      let params2 = last signature
      if (name == "length_" && not(endswith "]" params2)) || (not(endswith params1 params2) && name /= "length_")
          then error $ "User-defined function " ++ i ++ " call incompatible with given parameters. "++params1++"/"++params2 --TODO remove debug
      else do
          var <- varFunc
          type3 <- lookup var False
          if isNothing ftype
            then do
              let returnType = head $ split "(" $ signature!!1
              let var' = if isNothing type3 || (endswith "]" $ fromJust type3) then var ++ ":" ++ returnType else fromJust type3
              return (directive, tac ++ [TAC.VCall var' $ fromJust type_], TAC.Variable var', returnType)
            else do
              let returnType = signature!!1
              let var' = if isNothing type3 || (endswith "]" $ fromJust type3) then var ++ ":" ++ returnType else fromJust type3
              return (directive, tac ++ [TAC.Call var' $ head signature], TAC.Variable var', returnType)
  AST.ToClass labelspec -> do
    (t,l,s,r,f:ff,u,a,dataLabel) <- get
    let (dataLabel', directives) = toClassDirective labelspec dataLabel
    put (t,l,s,r,f:ff,u,a,dataLabel')
    return (directives, [], (TAC.ImmediateReference [] ("class_from_label_envionment_"++labelspec)),"")
  AST.Integer n -> return ([],[], TAC.ImmediateInteger n, "int")  -- $ modified
  AST.Double n -> return ([],[], TAC.ImmediateDouble n, "double") -- $ added
  AST.Character c -> return ([],[], TAC.ImmediateChar c, "char")
  AST.Reference n l -> do
    type_ <- lookupLabel (n++":"++l)
    if isNothing type_
          then error $ "Label " ++n++":"++l++ " has not been declared."
        else do
          return ([],[], TAC.ImmediateReference n l, "ref")
  AST.SolveReference (AST.Identifier i) (AST.Reference ns l) -> do
    (directives,tac,type1,retType) <- expression (AST.Identifier i)
    type2 <- lookupLabel $ ns ++ ":" ++ l
    let labelName = if ns == [] then "label_default_"++l else "label_"++ns++"_"++l
    if not $ endswith "ref" (retType ) 
    then error $ "Dot operator is only supported for references. Actual type: "++(retType)
    else if isNothing type2
    then error $ "Label "++ns++":"++l++" has not been declared."
    else do
      let resultType = getType $ head $ fromJust type2
      var <- newTemp
      let var' = var ++ ":"++resultType
      return (directives,tac++[TAC.Solve var' (type1) (labelName)],TAC.Variable var',resultType)
  AST.SolveReference (AST.Reference ns1 l1) (AST.Reference ns2 l2) -> do
    type1 <- lookupLabel $ ns1++":"++l1
    type2 <- lookupLabel $ ns2++":"++l2
    if (isNothing type1)  || (isNothing type2)
    then error $ "Label "++ns1++":"++l1++" and/or "++ns2++":"++l2++" has not been declared."
    else do
      return ([],[],TAC.ImmediateReference ns1 l2,"")  --TODO this is wrong CHANGE!!!!!



-- | Generates three address code for one boolean expression in the AST
-- (possibly generating code for boolean subexpressions first).
boolExpression :: AST.BoolExpression -> TAC.Label -> TAC.Label
               -> State GenState (TAC.TAC, TAC.TAC)
boolExpression bexpr lTrue lFalse = case bexpr of
  AST.LogOp op b1 b2 -> case op of
    T.And -> do
      b1True <- newLabel
      (dir1,tac1) <- boolExpression b1 b1True lFalse
      (dir2,tac2) <- boolExpression b2 lTrue lFalse
      return $ (dir1++dir2,tac1 ++ [TAC.Label b1True] ++ tac2)
    T.Or -> do
      b1False <- newLabel
      (dir1,tac1) <- boolExpression b1 lTrue b1False
      (dir2, tac2) <- boolExpression b2 lTrue lFalse
      return $ (dir1++dir2, tac1 ++ [TAC.Label b1False] ++ tac2)
  AST.Comparison op e1 e2 -> do
    (dir1, tac1,data1,type1) <- expression e1  -- $ modified
    (dir2, tac2,data2,type2) <- expression e2  -- $ modified
    if endswith "]" type1 || endswith "]" type2 -- $ added
      then error "Cannot use an array in a comparison."
    else do
      let jump1 = case op of
                T.Eq -> \l -> TAC.GotoCond2 l TAC.FEqual data1 data2
                T.Neq -> \l -> TAC.GotoCond2 l TAC.FNotEqual data1 data2
                T.Lt -> \l -> TAC.GotoCond2 l TAC.FLess data1 data2
                T.Lte -> \l -> TAC.GotoCond2 l TAC.FLessEqual data1 data2
                T.Gt -> \l -> TAC.GotoCond2 l TAC.FGreater data1 data2
                T.Gte -> \l -> TAC.GotoCond2 l TAC.FGreaterEqual data1 data2
      let jump2 = case op of
            T.Eq -> \l -> TAC.GotoCond2 l TAC.Equal data1 data2
            T.Neq -> \l -> TAC.GotoCond2 l TAC.NotEqual data1 data2
            T.Lt -> \l -> TAC.GotoCond2 l TAC.Less data1 data2
            T.Lte -> \l -> TAC.GotoCond2 l TAC.LessEqual data1 data2
            T.Gt -> \l -> TAC.GotoCond2 l TAC.Greater data1 data2
            T.Gte -> \l -> TAC.GotoCond2 l TAC.GreaterEqual data1 data2
      let jump = if type1 == "double" || type2 == "double" then jump1 else jump2
      return $ (dir1++dir2, tac1 ++ tac2 ++ [jump lTrue] ++ [TAC.Goto lFalse])
  AST.Not b -> boolExpression b lFalse lTrue
  AST.Boolean b -> return ([],[TAC.Goto (if b then lTrue else lFalse)])
  AST.Eof -> return ([],[ TAC.GotoCond1 lTrue TAC.IsTrue (TAC.Variable "%eof%")
                    , TAC.Goto lFalse
                    ])

-- $| Given an abstract syntax tree for parameters and code each it generates an appendix with user-defined functions for later use.
function :: AST.Command -> AST.Command -> AST.AST -> GenState -> (TAC.TAC, FunctionScopes, UDFLabels, TACstream)
function d p c (t,l,s,_,f:ff,u,a,dataLabel) = (directive,f':ff, u'', (name, intermediateCode'):_TACstream)
  where
      (f', r', i) = case d of
        AST.Declaration _type i -> (Map.insert i (r' ++ ":(" ++ params p++")") f, name ++ ":" ++ show _type, i)
        AST.ArrayDecl _type i -> (Map.insert i (r' ++ ":(" ++ params p++")") f, name ++ ":" ++ show _type ++ "[]", i)
      names = Map.lookup i u
      (name, u') = if isNothing names then (i ++ "_", Map.insert i [name] u) else (i ++ "_" ++ (show $ length $ fromJust names), Map.insert i ((fromJust names) ++ [name]) u)
      ((directive,intermediateCode,_TACstream), (_,_,_,_,_,u'',_,dataLabel')) = runState (program $ AST.Sequence p c) (t,l,s,r',f':ff,u',a,dataLabel)          
      intermediateCode' = fst (allocateParameters p a) ++ [TAC.Call "dummy:double" "dummy"] ++ intermediateCode

-- $| Given a list of parameters it generates a string representing the signature.
params :: AST.Command -> String
params (AST.Sequence decls decl) = params decls ++";"++ param decl
params decl = param decl

-- $| Given a parameter it generates a string representing the signature.
param :: AST.Command -> String
param (AST.Declaration _type _) = show _type
param (AST.ArrayDecl _type _) = show _type ++ "[]"

-- $| Generates three address code for a sequence of parameters in the AST.
allocateParameters :: AST.Command -> Locations -> (TAC.TAC, Locations)
allocateParameters params alts = case params of
  AST.Sequence p1 p2 -> (tac2 ++ tac1, alts2)
    where
    (tac1, alts1) = allocateParameters p1 alts
    (tac2, alts2) = allocateParameters p2 alts1
  AST.Declaration _type i -> let (name, alts') = newAlt i alts in ([TAC.Pop $ name ++ ":" ++ show _type], alts')
  AST.ArrayDecl _type i -> let (name, alts') = newAlt i alts in ([TAC.Pop $ name ++ ":" ++ show _type ++ "[]"], alts')

-- TODO documentation
labelenvironment :: String -> AST.Command -> GenState -> (DataLabelScopes, TAC.TAC)
labelenvironment name labels (_,_,_,_,_,_,_,labelMap) = (labelMap', tac')
  where
    (labelMap', tac', _) = getLabels name labels 1 labelMap

-- TODO documentation
getLabels :: String -> AST.Command -> Int64 -> DataLabelScopes -> (DataLabelScopes, TAC.TAC, Int64)
getLabels labelSpec labels index labelMap = case labels of
  AST.Sequence c1 c2 -> (labelMap2, tac1++tac2, index2)
    where
      (labelMap1, tac1, index1) = getLabels labelSpec c1 (index) labelMap
      (labelMap2, tac2, index2) = getLabels labelSpec c2 (index1) labelMap1
  AST.Declaration _type name -> (labelMap',tac, index+1)
    where
      labelMap' = 
        if isNothing $ Map.lookup labelName labelMap 
        then Map.insert labelName [AST.Declaration _type name] labelMap 
        else error $ "Label "++labelName++" defined twice."
      labelID = "label_"++labelSpec++"_"++name
      labelName = (labelSpec++":"++name)
      tac = [TAC.DatLabel labelID index (mapType _type False) labelName]
  AST.ArrayDecl _type name ->(labelMap',tac, index+1)
    where
      labelMap' = 
        if isNothing $ Map.lookup labelName labelMap 
        then Map.insert labelName [AST.ArrayDecl _type name] labelMap 
        else error $ "Label "++labelName++" defined twice."
      labelID = "label_"++labelSpec++"_"++name
      labelName = (labelSpec++":"++name)
      tac = [TAC.DatLabel labelID index (mapType _type True) labelName]

mapType :: T.Type -> Bool -> Int64
mapType T.TDouble False = 1
mapType T.TDouble True = 254
mapType T.TInt False = 2
mapType T.TInt True = 253
mapType T.TChar False = 3
mapType T.TChar True = 252

-- TODO
toClassDirective :: String -> DataLabelScopes -> (DataLabelScopes, TAC.TAC)
toClassDirective name labelMap = if isNothing $ Map.lookup labelName labelMap 
                then (labelMap', tac')
                else (labelMap, [])
  where
    labelName = "class_from_label_envionment_"++name
    refArrayName = labelName++"_references"
    offsetArrayName = labelName++"_offsets"
    labelMap' = Map.insert labelName [] labelMap
    cmds = Map.lookup (name++":") labelMap
    tac' = if isNothing cmds 
           then error ("Label envionment "++name++" has not been declared.")
           else (TAC.CustomLabel labelName): 
                (TAC.DATA $ TAC.ImmediateReference [] "env_class_class"):
                (TAC.DATA $ TAC.ImmediateReference [] refArrayName):
                (TAC.DATA $ TAC.ImmediateReference [] offsetArrayName):
                (TAC.CustomLabel refArrayName):
                (TAC.DATA $ TAC.ImmediateReference [] "label_env_parent"):[] ++
                (references $ fromJust cmds) ++
                (TAC.CustomLabel offsetArrayName):
                (TAC.DATA $ TAC.ImmediateInteger 0):[]++
                (offsets $ fromJust cmds)
    references :: [AST.Command] -> TAC.TAC
    references [] = []
    references (c:rest) = references' c ++ references rest 
      where 
        references' c = case c of
          AST.Sequence c1 c2 -> references' c1 ++ references' c2
          AST.Declaration decType decName -> [TAC.DATA $ TAC.ImmediateReference [] ("label_"++name++"_"++decName)]
          AST.ArrayDecl decType decName -> [TAC.DATA $ TAC.ImmediateReference [] ("label_"++name++"_"++decName)]
    offsets :: [AST.Command] -> TAC.TAC
    offsets c = offsetsCount c 8
      where
        offsetsCount :: [AST.Command] -> Int64 -> TAC.TAC 
        offsetsCount [] _ = []
        offsetsCount (c:rest) index =  tac1 ++ tac2
          where        
            (index', tac1) = offsets' c index
            (tac2) = offsetsCount rest index'
        offsets' :: AST.Command -> Int64 -> (Int64, TAC.TAC)
        offsets' c index = case c of
          AST.Sequence c1 c2 -> (index2, tac1++tac2)
            where
              (index1,tac1) = offsets' c1 index
              (index2, tac2 ) = offsets' c2 index1
          AST.Declaration decType decName -> (index+8, [TAC.DATA $ TAC.ImmediateInteger index])
          AST.ArrayDecl decType decName -> (index+8, [TAC.DATA $ TAC.ImmediateInteger index]) 
