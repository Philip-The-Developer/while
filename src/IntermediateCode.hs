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
    (||), (/=), (!!), (&&), (>),(-), not,
    String, Bool (..), Maybe (..), Int(..), error, putStrLn,
    fst, head, last, length, takeWhile, drop, concat, fromIntegral, otherwise
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
    split, endswith, replace
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
type GenState = (Counter, Environment, ReturnType,DataLabelScopes)
-- This counts temp variables and labels
type Counter = (TempCounter, LabelCounter)
-- | This is just a number.
type TempCounter = Int
-- | This is just a number.
type LabelCounter = Int
-- $| This is a mapping from variable to data type.
type Environment = [Map String (String, T.Type)]
-- $| This is just a string.
type Type = String
-- $| This is just a string.
type ReturnType = T.Type
-- This is a mapping from a label declaration to jump label in NASM
type DataLabelScopes = Map String (String,[AST.Command])
-- $| This is a list of UDF names and TACs.
type TACstream = [(TAC.Label, TAC.TAC)]

-- returns the name of the type of an AST.Declartaion
getType:: AST.Command -> String
getType (AST.Declaration t n) = show t

createVariableMap:: Environment
createVariableMap = [Map.fromList
    [
     ("object_acceptor",("$handle_object$", T.TFunction T.TInt $ T.TypeSequence T.TRef T.TRef)),
     ("class_acceptor", ("$handle_class$", T.TFunction T.TInt $ T.TypeSequence T.TRef T.TRef))
    ]]

createLabelMap:: DataLabelScopes
createLabelMap = Map.fromList 
    [
     ("env:new",("label_env_new", [AST.Declaration (T.TFunction T.TRef T.Void) "new"])),
     ("env:handle",("label_env_handle",[AST.Declaration (T.TFunction T.TInt (T.TypeSequence T.TRef T.TRef)) "handle"])),
     ("env:parent", ("label_env_parent",[AST.Declaration T.TRef "parent"])),
     ("env:length", ("label_env_length",[AST.Declaration T.TInt "length"])),
     ("env:name", ("label_env_name", [AST.Declaration T.TRef "name"])),
     ("env:funcLabels", ("label_env_funcLabels",[AST.Declaration T.TRef "funcLabels"])),
     ("env:funcAddress",("label_env_funcAddress",[AST.Declaration T.TRef "funcAddress"])),
     ("env:attrLabels",("label_env_attrLabels",[AST.Declaration T.TRef "attrLabels"])),
     ("env:attrOffsets",("label_env_attrOffsets",[AST.Declaration T.TRef "attrOffsets"])),
     ("env:type",("label_env_type",[AST.Declaration T.TRef "type"])),
     ("env:index",("label_env_index",[AST.Declaration T.TInt "index"])),
     ("env:key", ("label_env_key",[AST.Declaration T.TRef "key"])),
     ("env:parameter", ("label_env_parameter",[AST.Declaration T.TRef "parameter"])),
     ("env:callee", ("label_env_callee",[AST.Declaration T.TRef "callee"])),
     ("env:result",("label_env_result",[AST.Declaration T.TRef "result"])),
     ("env:value", ("label_env_value", [AST.Declaration T.TRef "value"])),
     ("env:fparameter",("label_env_fparameter",[AST.Declaration T.TRef "fparameter"]))
    ]

-- $| Given an abstract syntax tree it generates and intermediate representation
-- in three address code and an appendix with user-defined functions for later use.
process :: AST.AST -> TACstream -- $ modified
process ast = ("",directives):("",intermediateCode):appendix
  where
    ((directives,intermediateCode,appendix), _) = runState (program ast) ((0,0),createVariableMap, T.Void, createLabelMap)

-- | Generates a new label and increments the internal label counter.
newLabel :: State GenState (TAC.Label)
newLabel = do
  ((t,l),env,r,labels) <- get         -- $ modified
  put ((t,l+1),env,r,labels)          -- $ modified
  return $ "label" ++ show (l+1)

-- | Generates a new temporary variable and increments the internal variable
-- counter.
newTemp :: State GenState (TAC.Variable)
newTemp = do
  ((t,l),env,r,labels) <- get         -- $ modified
  put ((t+1,l),env,r,labels)          -- $ modified
  return $ "#" ++ show (t+1)

-- | Returns the variable given as parameter. To be used in 'expressionInto'.
fixedVar :: TAC.Variable -> State GenState TAC.Variable
fixedVar = return

-- $| Looks up type of variable.
lookup :: String -> State GenState (Maybe (String, T.Type))
lookup i = do
  (_,s,_,_) <- get
  let type_ = scopes i s
  return type_
  where
    scopes :: String -> Environment -> Maybe (String, T.Type)
    scopes _ [] = Nothing
    scopes i (m:_)
          | isJust _type = _type
        where 
          _type = Map.lookup i m
    scopes i (_:mm) = scopes i mm

lookupLabel :: String -> State GenState (Maybe (String,[AST.Command]))
lookupLabel str = do
  (_,_,_,labelMap) <- get
  return $ Map.lookup str labelMap

-- $| Changes the unique ID of a variable which correspond to a machine location.
insert :: String -> (String, T.Type) -> State GenState ()
insert i v =do
    (c,(h:t),r,labels) <- get
    let h' = Map.insert i v h
    put (c, (h':t),r,labels)
    return ()

-- $| Assigns a unique ID to a variable which correspond to a machine location.
{-newAlt :: String -> Locations -> (String, Locations)
newAlt i m = (name, a')
  where
    names = Map.lookup i m
    (name, a') = if isNothing names then (i ++ "_", Map.insert i [name] m) else (i ++ "_" ++ (show $ length $ fromJust names), Map.insert i ((fromJust names) ++ [name]) m) -}

-- $| Generates three address code for a complete program and an appendix with user-defined functions for later use.
program :: AST.AST -> State GenState (TAC.TAC, TAC.TAC, TACstream) -- $ modified
program prog = do
  next <- newLabel
  (directives,tac, udf, rt1) <- command prog next
  (_,_,r,_) <- get
  if r == T.Void || rt1 == r
    then return (directives, tac ++ [TAC.Label next], udf)
  else error $ "UDF has no return value."

-- $| Generates three address code for one specific command in the AST,
-- an appendix with user-defined functions for later use and
-- checks the existence of a return statement.
command :: AST.Command -> TAC.Label -> State GenState (TAC.TAC, TAC.TAC, TACstream, ReturnType) -- $ modified
command cmd next = case cmd of
  (AST.Sequence c1 c2) -> do
    (dir1, tac1, stream1, type1) <- command c1 next
    (dir2, tac2, stream2, type2) <- command c2 next
    return (dir1++dir2, tac1++tac2, stream1++stream2, if type1 == T.Void then type2 else type1)
 
  (AST.Declaration typ id) -> do
    declaredType <- lookup id
    if not $ isNothing declaredType
      then error $ "Variable \""++id++"\" has been declared twice."
      else do
        insert id (id,typ)
        return ([],[],[],T.Void)

  (AST.Assign addr expr) -> do
    (dir1, tac1, dat1, type1) <- expression expr
    (dir2, tac2, var2, type2) <- addressInto addr Nothing (Just dat1)
    return (dir1++dir2, tac1++tac2,[],T.Void)
 
  (AST.While bex cmd) -> do
    labelLoop <- newLabel
    labelTrue <- newLabel
    labelFalse <- newLabel
    (dir1, tac1) <- boolExpression bex labelTrue labelFalse
    (dir2, tac2, stream, type_) <- command cmd labelFalse
    return (dir1++dir2, [TAC.Label labelLoop]++ tac1++[TAC.Label labelTrue]++tac2++[TAC.Goto labelLoop]++[TAC.Label labelFalse], stream, type_)

  (AST.Environment cmd) -> do
    (c,env,r,lm) <- get
    put (c, Map.empty:env,r,lm)
    (dir,tac,stream,type_) <- command cmd next
    (c', (h:t), r', lm') <- get
    put (c', t , r', lm')
    return (dir, tac++(dealloc tac), stream, type_)

  (AST.IfThen bexpr cmd) -> do
    labelTrue <- newLabel
    labelFalse <- newLabel
    (dir1, tac1) <- boolExpression bexpr labelTrue labelFalse
    (dir2, tac2, stream, type_) <- command cmd next
    return (dir1++dir2, tac1++[TAC.Label labelTrue]++tac2++[TAC.Label labelFalse], stream, type_)

  (AST.IfThenElse bexpr cmd1 cmd2) -> do
    labelTrue <- newLabel
    labelFalse <- newLabel
    labelEnd <- newLabel
    (dir1, tac1) <- boolExpression bexpr labelTrue labelFalse
    (dir2, tac2, stream2, type2) <- command cmd1 next
    (dir3, tac3, stream3, type3) <- command cmd2 next
    return (dir1++dir2++dir3, tac1++[TAC.Label labelTrue]++tac2++[TAC.Goto labelEnd, TAC.Label labelFalse]++tac3++[TAC.Label labelEnd], stream2++stream3, if type2 == T.Void then type3 else type2)
    
  (AST.Output expr) ->do
    (dir1, tac1, var1, type1) <- expression expr
    case type1 of
      (T.TInt) -> return (dir1,tac1++[TAC.Output var1], [], T.Void)
      (T.TChar) -> return (dir1, tac1++ [TAC.COutput var1], [], T.Void)
      (T.TDouble) -> return (dir1, tac1++ [TAC.FOutput var1], [], T.Void)
      (T.TRuntimeType t) -> do
        labelInt <- newLabel
        labelChar <- newLabel
        labelDouble <- newLabel
        labelEnd <- newLabel
        vdouble' <- newTemp
        let vdouble = vdouble'++":double"
        let tac = [TAC.GotoCond2 labelInt TAC.Equal (TAC.Variable t) (TAC.ImmediateReference [] "class_primitive_int"),
                   TAC.GotoCond2 labelChar TAC.Equal (TAC.Variable t) (TAC.ImmediateReference [] "class_primitive_char"),
                   TAC.GotoCond2 labelDouble TAC.Equal (TAC.Variable t) (TAC.ImmediateReference [] "class_primitive_double"),
                   TAC.ShowError "index_error",
                   TAC.Label labelInt,
                   TAC.Output var1,
                   TAC.Goto labelEnd,
                   TAC.Label labelChar,
                   TAC.COutput var1,
                   TAC.Goto labelEnd,
                   TAC.Label labelDouble,
                   TAC.Copy vdouble var1,
                   TAC.FOutput (TAC.Variable vdouble),
                   TAC.Label labelEnd,
                   TAC.Comment "finish Output"]
        return (dir1, tac1++ tac, [], T.Void)
      otherwise -> error $ "output is only suported for int, char and double outputs.\n The expression \""++show expr++"\" has returns type \""++show type1++"\"."

  (AST.Read addr) -> do
    (dir1, tac1, var1, type1) <- address addr
    if T.isPointer type1
    then do
      let typeI = T.innerType type1
      tvar' <- newTemp
      let tvar = tvar'++":"++(show typeI)
      cmd <- case typeI of
        (T.TInt) -> return $ TAC.Read tvar
        (T.TChar) -> return $ TAC.CRead tvar
        (T.TDouble) -> return $ TAC.FRead tvar
        otherwise -> error $ "read is only supported for int, char and double inputs."
      return (dir1, tac1++[cmd]++[TAC.ToMemory (TAC.Variable var1) (TAC.Variable tvar)],[], T.Void);
    else do
      case type1 of
        (T.TInt) -> return (dir1,tac1++[TAC.Read var1], [], T.Void)
        (T.TChar) -> return (dir1, tac1++ [TAC.CRead var1], [], T.Void)
        (T.TDouble) -> return (dir1, tac1++ [TAC.FRead var1], [], T.Void)
        otherwise -> error $ "read is only suported for int, char and double outputs.\n The expression \""++show addr++"\" has returns type \""++show type1++"\"."
      
  (AST.Function typ id params cmd) -> do
    declared <- lookup id
    label <- newLabel
    if not $ isNothing declared
      then error $ "Identifier for function \""++show id++"\" declared twice."
      else do
        let func_type = T.TFunction typ (params2Type params)
        insert id ("$"++id++"$", func_type)
        (c,env,ret,labelMap) <- get
        let (tacP,envMap) = allociateParameter params Map.empty
        let ((dir1,tac1, tacStream1),(_,_,_,labelMap')) = runState (program cmd) ((0,0),[envMap]++env, typ, labelMap)
        put (c,env,ret,labelMap')
        return (dir1,[],("$"++id++"$",tacP++[TAC.Call "dummy:double" "dummy"]++tac1): tacStream1, T.Void)

  (AST.ArrayAlloc typ expr addr) -> do
    
    (dir1, tac1, data1,type1) <- case addr of
      AST.Identifier id -> do
        insert id (id, T.TArray typ)
        expression expr
      otherwise -> expression expr
    if (type1 /= T.TInt)
    then error $ "Array index is not an int."
    else do
      arrayVar' <- newTemp
      let arrayVar = arrayVar'++":ref"
      let tacAlloc = [TAC.ArrayAlloc arrayVar data1]
      (dir2, tac2, data2, type2) <- addressInto addr Nothing (Just $TAC.Variable arrayVar)
      return (dir1++dir2,tac1++tacAlloc++tac2,[],T.Void)
 
  (AST.Return expr) ->do
    (dir1, tac1, data1, type1) <- expression expr
    return (dir1, tac1++[TAC.Return data1], [],type1)

  AST.LabelEnvironment name labels -> do
    (c,e,r,dataLabel) <- get
    let cmdList = Map.lookup (name++":") dataLabel
    let (_,cmdList') = if isNothing cmdList then ("",[]) else (fromJust cmdList)
    let dataLabel' = Map.insert (name++":") ("",(labels:cmdList')) dataLabel
    let (dataLabel'',tac) = labelenvironment name labels (c,e,r,dataLabel') 
    put (c,e,r,dataLabel'')
    return (tac,[],[],T.Void)
  
  AST.Accepts object handler -> do
    (dir1, tac1, data1, type1) <- address object
    (dir2, tac2, data2, type2) <- address handler
    if type1 /= T.TRef
    then error $ "'"++show object++"' is not a ref."
    else if type2 /= T.TFunction T.TInt (T.TypeSequence T.TRef T.TRef)
      then error $ "'"++ show handler++"' is not a int(ref;ref)"
      else return (dir1++dir2, tac1++tac2++[TAC.Accept data1 data2],[],T.Void)
     

  _ -> error $ "Command \""++show cmd++"\" can not be compiled into immediate code."  
-- $| Generates three address code for one expression in the AST (possibly
-- generating code for subexpressions first) and determines its type.
expression :: AST.Expression -> State GenState (TAC.TAC,TAC.TAC,TAC.Data,T.Type)
expression = expressionInto newTemp

-- | Generates three address code for one expression in the AST (possibly
-- generating code for subexpressions first). The additional parameter will be
-- evaluated if code for something other than number or identifier is generated
-- and the returned variable will be used for the result.
-- $ Determines also its type.
expressionInto :: State GenState TAC.Variable -> AST.Expression
               -> State GenState (TAC.TAC,TAC.TAC,TAC.Data,T.Type) -- $ modified
expressionInto varFunc expr = case expr of
  (AST.Integer i) -> return ([],[],TAC.ImmediateInteger i,T.TInt)
  (AST.Double d) -> return ([],[],TAC.ImmediateDouble d, T.TDouble)
  (AST.Reference s r) -> return ([],[],TAC.ImmediateReference s r, T.TRef)
  (AST.Character c) -> return ([],[],TAC.ImmediateChar c, T.TChar)

  (AST.Variable addr) -> do
    (dir, tac1, var1, type1) <- address addr
    (tac2,var2,type2) <- solvePointer var1 type1
    return (dir,tac1++tac2, TAC.Variable var2,type2)

  (AST.Calculation op expr1 expr2) -> do
    (dir1, tac1, dat1, type1) <- expression expr1
    (dir2, tac2, dat2, type2) <- expression expr2
    (conv, dat1', dat2', type') <-  convert dat1 type1 dat2 type2
    var' <- newTemp
    let var = var' ++":"++show type'
    return (dir1++dir2, tac1++tac2++conv++[TAC.getCalculation op type' var dat1' dat2'], TAC.Variable var, type')

  (AST.Parameters expr1 expr2) -> do
    (dir1, tac1, dat1, type1) <- expression expr1
    (dir2, tac2, dat2, type2) <- expression expr2
    return (dir1++dir2, tac1++tac2, dat2, T.TypeSequence type1 type2)

  (AST.Parameter expr) -> do
    (dir1, tac1, dat1, type1) <- expression expr
    return (dir1, tac1++[TAC.Push dat1], dat1, type1)
 
  (AST.Void) -> return ([],[],TAC.Variable "void",T.Void)
 
  (AST.ToClass id) -> do
    (c,e,r,labelMap) <- get
    let (labelMap', dir) = toClassDirective id labelMap
    put (c,e,r,labelMap')
    return (dir,[],(TAC.ImmediateReference [] ("class_from_label_environment_"++id)),T.TRef)
  _ -> error $ "Expression \""++show expr++"\" can not be compiled into immediate code."

address:: AST.Address -> State GenState (TAC.TAC, TAC.TAC, String, T.Type)
address addr = addressInto addr Nothing Nothing

addressInto :: AST.Address -> Maybe String -> Maybe TAC.Data -> State GenState (TAC.TAC, TAC.TAC, String, T.Type)

addressInto (AST.Identifier "INT") Nothing Nothing = do
  res' <- newTemp
  let res = res'++":ref"
  return ([],[TAC.Copy res (TAC.ImmediateReference [] "class_primitive_int")],res,T.TRef)

addressInto (AST.Identifier "DOUBLE") Nothing Nothing = do
  res' <- newTemp
  let res = res'++":ref"
  return ([],[TAC.Copy res (TAC.ImmediateReference [] "class_primitive_double")],res,T.TRef)

addressInto (AST.Identifier "CHAR") Nothing Nothing = do
  res' <- newTemp
  let res = res'++":ref"
  return ([],[TAC.Copy res (TAC.ImmediateReference [] "class_primitive_char")],res, T.TRef)

addressInto (AST.Identifier "REF") Nothing Nothing = do
  res' <- newTemp
  let res = res'++":ref"
  return ([],[TAC.Copy res (TAC.ImmediateReference [] "class_primitive_ref")],res, T.TRef)

addressInto (AST.Identifier "GET") Nothing Nothing = do
  res' <- newTemp
  let res = res'++":ref"
  return ([],[TAC.Copy res (TAC.ImmediateReference [] "class_message_get")],res, T.TRef)

addressInto (AST.Identifier "CLASSCLASS") Nothing Nothing = do
  res' <- newTemp
  let res = res'++":ref"
  return ([],[TAC.Copy res (TAC.ImmediateReference [] "class_class")],res, T.TRef)

addressInto (AST.Identifier "SET") Nothing Nothing = do
  res' <- newTemp
  let res = res'++":ref"
  return ([],[TAC.Copy res (TAC.ImmediateReference [] "class_message_set")],res, T.TRef)

addressInto (AST.Identifier "METHOD") Nothing Nothing = do
  res' <- newTemp
  let res = res'++":ref"
  return ([],[TAC.Copy res (TAC.ImmediateReference [] "class_message_function")],res, T.TRef)

addressInto (AST.Identifier "AGET") Nothing Nothing = do
  res' <- newTemp
  let res = res'++":ref"
  return ([],[TAC.Copy res (TAC.ImmediateReference [] "class_message_get_array")],res, T.TRef)

addressInto (AST.Identifier "ASET") Nothing Nothing = do
  res' <- newTemp
  let res = res'++":ref"
  return ([],[TAC.Copy res (TAC.ImmediateReference [] "class_message_set_array")],res, T.TRef)

addressInto (AST.Identifier i) prevVar value =do
  vt <- lookup i
  if isNothing vt
  then do
    dl <- lookupLabel ("default:"++i)
    if isNothing $ dl
    then error $ "Variable \""++i++"\" has not been declaret."
    else addressInto (AST.Label "default" i) prevVar value
  else do
    let (var, varType_) = fromJust vt
    if isNothing prevVar
    then do
      if isNothing value 
      then do
        case varType_ of
          T.TFunction _ _ -> do
            if endswith "$" var
            then do
              vref' <- newTemp
              let vref = vref'++":"++(show varType_) 
              return ([], [TAC.Copy vref (TAC.ImmediateReference [] var)], vref, varType_)
            else do
              return ([],[], var++":"++show varType_,varType_)
          otherwise -> return ([],[], var++":"++show varType_, varType_)
      else do
        let tac = [TAC.Copy (var++":"++show varType_) (fromJust value)]
        return ([],tac,"void", T.Void)
    else do
      let prevVar' = fromJust prevVar
      msg' <- newTemp
      let msg = msg'++":ref"
      if | isNothing value -> do
           classVar' <- newTemp
           let classVar = classVar'++":ref"
           let returnType = T.TRuntimeType classVar
           result' <- newTemp
           let result = result'++":"++(show returnType)
           let tac = [TAC.GET msg (TAC.Variable (var++":"++show varType_)),
                      TAC.Send (TAC.Variable msg) (TAC.Variable prevVar'),
                      TAC.GETResult result classVar msg]
           return ([], tac, result,returnType)
         | True -> do
           let tac = [TAC.SET msg (TAC.Variable (var++":"++show varType_)) (fromJust value),
                      TAC.Send (TAC.Variable msg) (TAC.Variable prevVar')]
           return ([], tac, "void", T.Void)

addressInto (AST.FromArray addr exprIndex) prevVar value = do
  (dir1, tac1, data1', type1') <- addressInto addr prevVar Nothing
  (dir2, tac2, data2, type2) <- expression exprIndex
  (tac3, data1, type1) <- solvePointer data1' type1'
  if type2 /= T.TInt
    then error $ "Array index \""++show exprIndex++"\" is not an int."
    else if not $ T.isArray type1
    then error $ "\""++show addr++"\" is not an array. An array was expected."
    else do
      if | isNothing value -> do
           result' <- newTemp
           let result = result'++":"++(show (T.innerType type1))
           msg' <- newTemp
           let msg = msg'++":ref"
           resultClass' <- newTemp
           let resultClass = resultClass'++":ref"
           let tacArray = [TAC.GETARRAY msg data2, TAC.Send (TAC.Variable msg) (TAC.Variable data1), TAC.GETResult result resultClass msg]
           return (dir1++dir2, tac1++tac2++tac3++tacArray,result,T.innerType type1)
         | True -> do
           msg' <- newTemp
           let msg = msg'++":ref"
           let tacArray = [TAC.SETARRAY msg data2 (fromJust value), TAC.Send (TAC.Variable msg) (TAC.Variable data1)]
           return (dir1++dir2,tac1++tac2++tac3++tacArray, "void", T.Void) 

addressInto (AST.FunctionCall addr params) prevVar value = do
  case addr of
    (AST.Identifier "length") ->do
      (dir, tac, data_, type_) <- expression params
      var' <- newTemp
      let var = var'++":int"
      if(T.isArray type_)
        then return (dir,tac++[TAC.Call var "length_"], var, T.TInt)
        else error $ "length() expects an array as parameter. Actual type is \""++show type_++"\"."++ show (AST.FunctionCall addr params)
    (AST.Identifier id) -> do
      (dir1, tac1, data1, type1) <- expression params
      declared <- lookup id
      if isNothing declared
        then do 
          dl <- lookupLabel ("default:"++id)
          if isNothing $ dl
            then error $ "Variable \""++id++"\" has not been declaret."
            else addressInto (AST.FunctionCall (AST.Label "default" id) params) prevVar value
        else do
          let (label,retType) = fromJust declared
          case retType of
            (T.TFunction ret _) -> do
              if endswith "$" label
              then do
                var' <- newTemp
                let var = var'++":"++show ret
                return (dir1, tac1++[TAC.Call var label], var, ret)
              else do
                var' <- newTemp
                let var = var'++":"++show ret
                return (dir1, tac1++[TAC.VCall var (label++":"++(show retType))],var,ret)
            (T.TRef) -> if isNothing prevVar
              then error $ "Method call does not declare calling object."
              else do
                (dirP, dataArr, tacP) <- calcParameter params
                msg' <- newTemp
                let msg = msg'++":ref"
                resultClass' <- newTemp
                let resultClass = resultClass'++":ref"
                let resultType = T.TRuntimeType resultClass
                result' <- newTemp
                let result = result'++":"++(show resultType)
                let tacCall = [TAC.METHOD msg (TAC.Variable (label++":"++(show retType))) dataArr, 
                               TAC.Send (TAC.Variable msg) (TAC.Variable (fromJust prevVar)),
                               TAC.METHODResult result resultClass msg]
                return (dirP,tacP++tacCall,result,resultType)
            otherwise -> error $ "\""++id++"\" is not a function."
    otherwise -> do
      if | isNothing prevVar -> do
             classRef' <- newTemp
             let classRef = classRef'++":ref"
             (dir1, tac1, data1, type1) <- address addr
             (dirP, tacP, dataP, typeP) <-expression params
             case type1 of
               T.TFunction r _ -> do
                 let retType = r
                 result' <- newTemp
                 let result = result'++":"++(show retType)
                 return (dir1++dirP, tac1++tacP++[TAC.VCall result data1], result, retType)
         | True -> do
             (dir1, tac1, data1, type1) <- address addr
             (dirP, dataArr, tacP) <- calcParameter params
             msg' <- newTemp
             let msg = msg'++":ref"
             runtimeType' <- newTemp
             let runtimeType = runtimeType'++":ref"
             let retType = T.TRuntimeType runtimeType;
             result' <- newTemp
             let result = result'++":"++(show retType)
             return (dir1++ dirP,tac1++tacP++[TAC.METHOD msg (TAC.Variable data1) dataArr, TAC.Send (TAC.Variable msg) (TAC.Variable $ fromJust prevVar),
                         TAC.METHODResult result runtimeType msg],result, retType)
            
  where
    calcParameter:: AST.Expression -> State GenState (TAC.TAC, [TAC.Data], TAC.TAC)
    calcParameter (AST.Parameters p1 p2) = do
      (dir1, dat1,tac1) <- calcParameter p1
      (dir2, dat2, tac2)  <- calcParameter p2
      return ( dir1++dir2, dat1++dat2, tac1++tac2)
    calcParameter (AST.Parameter expr) = do
      (dir,tac, dat,_) <- expression expr
      return (dir, [dat], tac)
    calcParameter AST.Void = return ([],[],[])
    calcParameter expr = error $"Could not solve "++show expr++"."

addressInto (AST.Label envName attrName) prevVar value
  |isNothing prevVar = do
    vt <- lookupLabel $ envName++":"++attrName
    if isNothing vt
    then error $ envName++":"++attrName++" is not declared."
    else do
      let (labelStr,_) = fromJust vt
      var' <- newTemp
      let var = var'++ ":ref"
      return ([], [TAC.Copy var $TAC.ImmediateReference [] labelStr], var, T.TRef)  
  |otherwise = do
    let prevVar'= fromJust prevVar
    vt <- lookupLabel $ envName++":"++attrName
    if isNothing vt
    then error $ envName++":"++attrName++" is not declared."
    else do
      let (labelStr, (decl:_)) = fromJust vt
      type_ <- case decl of
        AST.Declaration t id ->return t
        otherwise -> error $ (show decl)++" is not a declaration."
      case type_ of
        otherwise -> do
          msg' <- newTemp
          let msg = msg'++":ref"
          result' <- newTemp
          let result = result'++":"++(show type_)
          classVar' <- newTemp
          let classVar = classVar'++":ref"
          let tac = if | isNothing value -> [TAC.GET msg (TAC.ImmediateReference [] labelStr),
                                             TAC.Send (TAC.Variable msg) (TAC.Variable prevVar'),
                                             TAC.GETResult result classVar msg]
                       | True ->            [TAC.SET msg (TAC.ImmediateReference [] labelStr) (fromJust value),
                                             TAC.Send (TAC.Variable msg) (TAC.Variable prevVar')]
          return ([],tac,result,type_) 
       

addressInto (AST.Structure addr1 addr2) prevVar value = do
  (dir1, tac1, var1, type1) <- addressInto addr1 prevVar Nothing
  (tacRef, varRef, typeRef) <- solvePointer var1 type1
  if typeRef /= T.TRef 
    then error $ (show addr1)++" is not a reference."
    else do
      (dir2, tac2, var2, type2) <- addressInto addr2 (Just varRef) value
      return (dir1++dir2, tac1++tacRef++tac2, var2, type2)
  

addressInto adr _ _ = error $ "Address \""++show adr++"\" can not be compiled into immediate code." 

methodCall:: String -> TAC.Data -> String ->State GenState TAC.TAC
methodCall refToClass label resultVariable = do
  vlabelOP' <- newTemp
  let vlabelOP = vlabelOP'++":ref"
  multipl' <- newTemp
  let multipl = multipl'++":int"
  vIndex' <- newTemp
  let vIndex = vIndex'++":int"
  vOffsetArray' <- newTemp
  let vOffsetArray = vOffsetArray'++":ref"
  vOffset' <- newTemp
  let vOffset = vOffset'++":int"
  let tac = [TAC.Copy vlabelOP label,
             TAC.Add vlabelOP (TAC.Variable vlabelOP) (TAC.ImmediateInteger 16),
             TAC.FromMemory vIndex $ TAC.Variable vlabelOP,
             TAC.Add vlabelOP (TAC.Variable refToClass) (TAC.ImmediateInteger 32),
             TAC.FromMemory vOffsetArray $ TAC.Variable vlabelOP,
             TAC.Copy vlabelOP $ TAC.Variable vOffsetArray,
             TAC.Add vlabelOP (TAC.Variable vlabelOP) $ TAC.ImmediateInteger 8,
             TAC.Mul multipl (TAC.Variable vIndex) (TAC.ImmediateInteger 8),
             TAC.Add vlabelOP (TAC.Variable vlabelOP) (TAC.Variable multipl),
             TAC.Copy resultVariable $ TAC.Variable vlabelOP]
  return tac


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
    if T.isArray type1 || T.isArray type2 -- $ added
      then error $ "Cannot use an array in a comparison. At Comparison \""++show (AST.Comparison op e1 e2)++"\". DEBUG "++show type1++"/"++show type2
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
      let jump = if type1 == T.TDouble || type2 == T.TDouble then jump1 else jump2
      return $ (dir1++dir2, tac1 ++ tac2 ++ [jump lTrue] ++ [TAC.Goto lFalse])
  AST.Not b -> boolExpression b lFalse lTrue
  AST.Boolean b -> return ([],[TAC.Goto (if b then lTrue else lFalse)])
  AST.Eof -> return ([],[ TAC.GotoCond1 lTrue TAC.IsTrue (TAC.Variable "%eof%")
                    , TAC.Goto lFalse
                    ])
convert:: TAC.Data -> T.Type -> TAC.Data -> T.Type -> State GenState (TAC.TAC, TAC.Data, TAC.Data, T.Type)
convert data1 type1 data2 type2 = do
      if (type1 == type2) then return ([], data1, data2, type1)
      else if (type1 == T.TDouble && type2 == T.TInt) then do
        var' <- newTemp
        let var = var'++":double"
        case data2 of
          (TAC.Variable _) -> return ([TAC.Convert var data2], data1, TAC.Variable var, T.TDouble)
          _ -> return ([], data1,data2,T.TDouble)
      else if (type1 == T.TInt && type2 == T.TDouble) then do
        var' <- newTemp
        let var = var'++":double"
        case data1 of
          (TAC.Variable _) -> return ([TAC.Convert var data1], TAC.Variable var, data2, T.TDouble)
          _ -> return ([],data1, data2,T.TDouble)
      else error $ "Can not convert \""++show type1++"\" to \""++show type1++"\" or \""++show type2++"\" to \""++show type1++"\"."

solvePointer:: String -> T.Type -> State GenState (TAC.TAC, String, T.Type)
solvePointer var (T.TPointer t) = do
  res' <- newTemp
  let res = res'++":"++show t
  return ([TAC.FromMemory res (TAC.Variable var)], res, t)
solvePointer var t = return ([], var, t)

params2Type:: AST.Command -> T.Type
params2Type (AST.Sequence cmd1 cmd2) = T.TypeSequence (params2Type cmd1) (params2Type cmd2)
params2Type (AST.Declaration t _) = t

allociateParameter:: AST.Command -> Map String (String, T.Type) -> (TAC.TAC, Map String (String, T.Type))
allociateParameter (AST.Sequence cmd1 cmd2) map = (tac1++tac2, map2)
  where
    (tac2, map1) = allociateParameter cmd1 map
    (tac1, map2) = allociateParameter cmd2 map1
allociateParameter (AST.Declaration t id) map = (tac, map')
  where
    tac = [TAC.Pop $ id++":"++show t]
    map' = Map.insert id (id, t) map 

--reads a labelenvironment and creates TAC for the directive environment
labelenvironment :: String -> AST.Command -> GenState -> (DataLabelScopes, TAC.TAC)
labelenvironment name labels (_,_,_,labelMap) = (labelMap', tac')
  where
    (labelMap', tac', _, _) = getLabels name labels 3 0 labelMap

getLabels :: String -> AST.Command -> Int64 -> Int64 -> DataLabelScopes -> (DataLabelScopes, TAC.TAC, Int64, Int64)
getLabels labelSpec labels attIndex funcIndex labelMap = case labels of
  AST.Sequence c1 c2 -> (labelMap2, tac1++tac2, attIndex2, funcIndex2)
    where
      (labelMap1, tac1, attIndex1, funcIndex1) = getLabels labelSpec c1 (attIndex) funcIndex labelMap
      (labelMap2, tac2, attIndex2, funcIndex2) = getLabels labelSpec c2 (attIndex1) funcIndex1 labelMap1
  AST.Declaration _type name -> (labelMap''',tac, calcAttIndex attIndex _type, calcFuncIndex funcIndex _type)
    where
      labelMap' = 
        if isNothing $ Map.lookup labelName labelMap 
        then Map.insert labelName ("label_"++labelSpec++"_"++name, [AST.Declaration _type name]) labelMap 
        else error $ "Label "++labelName++" defined twice."
      labelMap'' = if isNothing $ Map.lookup ("default:"++name) labelMap'
                   then Map.insert ("default:"++name) ("label_"++labelSpec++"_"++name, [AST.Declaration _type name]) labelMap'
                   else Map.insert ("default:"++name) ("",[AST.NONE]) labelMap'
      labelID = "label_"++labelSpec++"_"++name
      labelName = (labelSpec++":"++name)
      (dataType, labelMap''', directive) = if T.isArray _type then mapType (T.innerType _type) True labelMap'' else mapType _type False labelMap''
      tac = directive++(calcDatLabel labelID dataType labelName _type)
  where
    calcAttIndex:: Int64 -> T.Type -> Int64
    calcAttIndex index _type = case _type of
      (T.TFunction _ _) -> index
      otherwise -> index+1
    calcFuncIndex:: Int64 -> T.Type -> Int64
    calcFuncIndex index _type = case _type of
      (T.TFunction _ _) -> index+1
      otherwise -> index
    calcDatLabel labelID dataType labelName _type = case _type of
      (T.TFunction _ _) -> [TAC.DatLabel labelID funcIndex dataType labelName]
      otherwise -> [TAC.DatLabel labelID attIndex dataType labelName]


mapType :: T.Type -> Bool -> DataLabelScopes -> (TAC.Data, DataLabelScopes, TAC.TAC)
mapType (T.TFunction type1 type2) isArray labelMap = (label', labelMap', dirResult++directives')
  where
    labelName = T.getLabel (T.TFunction type1 type2)
    label' = TAC.ImmediateReference [] labelName
    rolledOut = T.rollout (T.TFunction type1 type2)
    (dataResult, labelMapResult, dirResult) = mapType type1 False labelMap
    (datas, labelMapR, dirR) = functionType2Directive rolledOut labelMapResult
    directives' = if isNothing $Map.lookup labelName labelMapR
                    then dirR++[TAC.CustomLabel labelName,
                          TAC.DATA $ TAC.ImmediateReference [] "$handle_object$",
                          TAC.DATA $ TAC.ImmediateReference [] "class_function",
                          TAC.DATA $ TAC.ImmediateInteger 1,
                          TAC.DATA $ TAC.ImmediateReference [] (labelName++"_parameter"),
                          TAC.DATA $ dataResult,
                          TAC.CustomLabel $ labelName++"_parameter",
                          TAC.DATA $ TAC.ImmediateReference [] "$handle_object$",
                          TAC.DATA $ TAC.ImmediateReference [] "class_primitive_ref",
                          TAC.DATA $ TAC.ImmediateInteger $ fromIntegral $ length rolledOut]++datas
                    else []
    labelMap' = Map.insert labelName ("",[AST.NONE]) labelMapR
mapType _type isArray labelMap = (TAC.ImmediateReference [] $ T.getLabel _type, labelMap, [])

functionType2Directive:: [T.Type]-> DataLabelScopes -> (TAC.TAC, DataLabelScopes, TAC.TAC) -- data type, label map, directive
functionType2Directive [] labelMap = ([],labelMap, [])
functionType2Directive (t:tt) labelMap = case t of
                                    (T.TFunction type1 type2) -> ([TAC.DATA data1]++dataR, labelMapR, dir1++dirR)
                                      where
                                        (data1,labelMap1, dir1) = mapType (T.TFunction type1 type2) False labelMap
                                        (dataR, labelMapR, dirR) = functionType2Directive tt labelMap1
                                    (T.TypeSequence type1 type2) -> ([TAC.DATA data1]++dataR, labelMapR, dir1++dirR)
                                      where
                                        (data1,labelMap1, dir1) = mapType (T.TFunction type1 type2) False labelMap
                                        (dataR, labelMapR, dirR) = functionType2Directive tt labelMap1
                                    (_) -> ([TAC.DATA $ TAC.ImmediateReference [] $ T.getLabel t]++dataR, labelMapR, []++dirR)
                                      where
                                        (dataR, labelMapR, dirR) = functionType2Directive tt labelMap
    
                    

-- writes TAC to construct a class
toClassDirective :: String -> DataLabelScopes -> (DataLabelScopes, TAC.TAC)
toClassDirective name labelMap = if isNothing $ Map.lookup labelName labelMap 
                then (labelMap', tac')
                else (labelMap, [])
  where
    labelName = "class_from_label_environment_"++name
    refArrayName = labelName++"_references"
    offsetArrayName = labelName++"_offsets"
    funcArrayName = labelName ++"_functions"
    functionMapName = labelName ++ "_functins_Map"
    refArray =references cmds False
    offsetArray = offsets cmds False
    funcArray = references cmds True
    labelMap' = Map.insert labelName (labelName,[]) labelMap
    cmds' = Map.lookup (name++":") labelMap
    (_,cmds) = if isNothing cmds'
               then error $ "Label environment "++name++" has not been declared."
               else fromJust cmds'
    tac' =      (TAC.CustomLabel labelName): 
                (TAC.DATA $ TAC.ImmediateReference [] "$handle_class$"):
                (TAC.DATA $ TAC.ImmediateReference [] "class_class"):
                (TAC.DATA $ TAC.ImmediateInteger 1 ):
                (TAC.DATA $ TAC.ImmediateReference [] "class_class_str"):
                (TAC.DATA $ TAC.ImmediateReference [] funcArrayName):
                (TAC.DATA $ TAC.ImmediateReference [] functionMapName):
                (TAC.DATA $ TAC.ImmediateReference [] refArrayName):
                (TAC.DATA $ TAC.ImmediateReference [] offsetArrayName):
                (TAC.CustomLabel refArrayName):
                (TAC.DATA $ TAC.ImmediateReference [] "$handle_object$"):
                (TAC.DATA $ TAC.ImmediateReference [] "class_primitive_ref"):
		(TAC.DATA $ TAC.ImmediateInteger $ fromIntegral $ (length refArray) +3):
                (TAC.DATA $ TAC.ImmediateReference [] "label_env_handle"):
                (TAC.DATA $ TAC.ImmediateReference [] "label_env_parent"):
                (TAC.DATA $ TAC.ImmediateReference [] "label_env_length"):[] ++
                (refArray) ++
                (TAC.CustomLabel offsetArrayName):
                (TAC.DATA $ TAC.ImmediateReference [] "$handle_object$"):
                (TAC.DATA $ TAC.ImmediateReference [] "class_primitive_int"):
                (TAC.DATA $ TAC.ImmediateInteger $ fromIntegral $ (length offsetArray)+3):
                (TAC.DATA $ TAC.ImmediateInteger 0):
                (TAC.DATA $ TAC.ImmediateInteger 8):
                (TAC.DATA $ TAC.ImmediateInteger 16):[] ++
                (offsetArray)++
		[TAC.CustomLabel funcArrayName]++
                (TAC.DATA $ TAC.ImmediateReference [] "$handle_object$"):
                (TAC.DATA $ TAC.ImmediateReference [] "class_primitive_ref"):[]++
		[TAC.DATA $ TAC.ImmediateInteger $ fromIntegral $ length funcArray]++
                (funcArray)++
                [TAC.CustomLabel functionMapName]++
                [TAC.DATA $ TAC.ImmediateReference [] "$handle_object$"]++
                [TAC.DATA $ TAC.ImmediateReference [] "class_primitive_int"]++
                [TAC.DATA $ TAC.ImmediateInteger $ fromIntegral $ length funcArray]++
                (funcMap $ length funcArray)
    references :: [AST.Command] -> Bool -> TAC.TAC
    references [] _ = []
    references (c:rest) functionRef = references' c ++ references rest functionRef 
      where 
        references' c = case c of
          AST.Sequence c1 c2 -> references' c1 ++ references' c2
          AST.Declaration decType decName -> solveDecl decType decName
	solveDecl decType decName = case decType of
		(T.TFunction _ _) -> if functionRef then [TAC.DATA $ TAC.ImmediateReference [] ("label_"++name++"_"++decName)] else []
		otherwise -> if not $ functionRef then [TAC.DATA $ TAC.ImmediateReference [] ("label_"++name++"_"++decName)] else []
    offsets :: [AST.Command] -> Bool -> TAC.TAC
    offsets c functionCount =if functionCount then offsetsCount c 0 else offsetsCount c 24
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
          AST.Declaration decType decName -> countDecl decType index 
	countDecl decType index = case decType of
		(T.TFunction _ _) -> if not $ functionCount then (index, []) else (index+8, [TAC.DATA $ TAC.ImmediateInteger index])
		otherwise -> if not $ functionCount then (index+8, [TAC.DATA $ TAC.ImmediateInteger index]) else (index, [])
    funcMap:: Int -> TAC.TAC
    funcMap 0 = []
    funcMap n = [TAC.DATA $ TAC.ImmediateInteger 0]++(funcMap $ n - 1)
