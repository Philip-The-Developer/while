{-|
  Module      : Interface.Nasm
  Description :
  Copyright   : 2014, Jonas Cleve
                2015, Tay Phuong Ho
                2016, Philip Schmiel
  License     : GPL-3
-}
module Interface.Nasm (
  NasmCode (..),
  Register (..), FRegister (..), Location (..), Operand (..), Immediate (..),
  Instruction (..),
  locationIsRegister, locationIsStackLocation, operandIsImmediate, operandIsImmediateDouble,
  operandIsLocation, operandIsRegister, operandIsFRegister, operandIsStackLocation,
  mov, add, sub, imul, imul', idiv, cmp, neg, push, pop, shl, sar, instr,
  mov', fmov, fadd, fsub, fmul, fdiv, fcmp, fneg
) where

import Prelude (
    Eq, Show, Ord,
    String, Int, Bool (..), Maybe (..),
    show, otherwise, not,
    (++), (*), (||), (&&),
    Double, Char, error, ($)
  )
import Data.Int (
    Int64
  )
import Data.Char (
    toLower
  )
import Data.Functor (
    (<$>)
  )
import Data.List (
    intercalate
  )

-- | A class for nasm code.
class NasmCode c where
  toCode :: c -> String

-- | The sixteen registers available on 64bit x86 processors minus the two stack
--   registers RBP and RSP.
data Register
  = RAX
  | RBX
  | RCX
  | RDX
  | RSI
  | RDI
  | R8
  | R9
  | R10
  | R11
  | R12
  | R13
  | R14
  | R15
  deriving (Eq, Ord, Show)

-- | Show
instance NasmCode Register where
  toCode r = toLower <$> show r

-- $| The 16 floating point registers available on 64bit x86 processors.
data FRegister
  = XMM0
  | XMM1
  | XMM2
  | XMM3
  | XMM4
  | XMM5
  | XMM6
  | XMM7
  | XMM8
  | XMM9
  | XMM10
  | XMM11
  | XMM12
  | XMM13
  | XMM14
  | XMM15
  deriving (Eq, Ord, Show)

-- $| Show
instance NasmCode FRegister where
  toCode r = toLower <$> show r


-- | A data location (either register or memory)-
data Location
  = Register Register   -- ^ A processor register
  | FRegister FRegister -- $ A floating point register
  | StackLocation Int   -- ^ A memory location on the stack relative to the base
                        --   pointer.
  deriving (Eq, Ord, Show)

-- | Print the location so it can be used directly in the code.
instance NasmCode Location where
  toCode (Register r) = toCode r
  toCode (FRegister r) = toCode r -- $ added
  toCode (StackLocation i) = "[rbp-" ++ show (i*8) ++ "]"

-- | Immediate Values as operands.
data Immediate 
  = ImmediateInt Int64     -- $ modified
  | ImmediateDouble Double -- $ added
  | ImmediateChar Char
  | ImmediateReference String
  deriving (Eq, Ord, Show)

-- $| Show the immediate.
instance NasmCode Immediate where
  toCode (ImmediateInt i) = show i     -- $ modified
  toCode (ImmediateDouble i) = show i  -- $ added
  toCode (ImmediateChar c) = show c
  toCode (ImmediateReference s) = s

-- | General operands for assembly instructions.
data Operand
  = Location Location
  | Immediate Immediate
  deriving (Eq, Ord, Show)

-- | Use the respective 'toCode' functions.
instance NasmCode Operand where
  toCode (Location l) = toCode l
  toCode (Immediate i) = toCode i

-- | Returns whether a given location is a register.
locationIsRegister :: Location -> Bool
locationIsRegister (Register _) = True
locationIsRegister (FRegister _) = True -- $ added
locationIsRegister _ = False

-- | Returns whether a given location is a stack location.
locationIsStackLocation :: Location -> Bool
locationIsStackLocation (StackLocation _) = True
locationIsStackLocation _ = False

-- | Returns whether a given operand is a register.
operandIsRegister :: Operand -> Bool
operandIsRegister (Location (Register _)) = True
operandIsRegister (Location (FRegister _)) = True -- $ added
operandIsRegister _ = False

-- $| Returns whether a given operand is a floating point register.
operandIsFRegister :: Operand -> Bool
operandIsFRegister (Location (FRegister _)) = True
operandIsFRegister _ = False

-- | Returns whether a given operand is a stack location.
operandIsStackLocation :: Operand -> Bool
operandIsStackLocation (Location (StackLocation _)) = True
operandIsStackLocation _ = False

-- | Returns whether a given operand is an immediate value.
operandIsImmediate :: Operand -> Bool
operandIsImmediate (Immediate _) = True
operandIsImmediate _ = False

-- $| Returns whether a given operand is an immediate double value.
operandIsImmediateDouble :: Operand -> Bool
operandIsImmediateDouble (Immediate (ImmediateDouble _)) = True
operandIsImmediateDouble _ = False

-- | Returns whether a given operand is a location type.
operandIsLocation :: Operand -> Bool
operandIsLocation (Location _) = True
operandIsLocation _ = False

data Instruction
  = Mov Operand Operand
  | Mov' Operand                  -- $ added
  | FMov Operand Operand          -- $ added
  | Add Operand Operand
  | FAdd Operand Operand          -- $ added
  | Sub Operand Operand
  | FSub Operand Operand          -- $ added
  | IMul Operand Operand
  | IMul' Operand Operand Operand
  | FMul Operand Operand          -- $ added
  | IDiv Operand
  | FDiv Operand Operand          -- $ added
  | Cmp Operand Operand
  | FCmp Operand Operand          -- $ added
  | Neg Operand
  | FNeg Operand                  -- $ added
  | Push Operand
  | Pop Operand
  | Shl Operand Operand
  | Sar Operand Operand
  | Instr String
  | Call String
  | DATA Operand
  | Solve Operand Operand String
  | MCall Operand Operand String

instance NasmCode Instruction where
  toCode (Mov o1 o2)
    | isFR o1 || isFR o2 = "movq " ++ toCode o1 ++ ", " ++ toCode o2            -- $ added
    | isM o1 && not (isR o2) = "mov QWORD " ++ toCode o1 ++ ", " ++ toCode o2
    | otherwise = format "mov" [o1, o2]
  toCode (Mov' o1) -- $ added
    | not (isD o1) = "mov rax, __float64__(" ++ toCode o1 ++ ".0)"
    | otherwise = "mov rax, __float64__(" ++ toCode o1 ++ ")"
  toCode (FMov o1 o2) = "movsd " ++ toCode o1 ++ ", " ++ toCode o2             -- $ added
  toCode (Add o1 o2) = format "add" [o1, o2]
  toCode (FAdd o1 o2) = format "addsd" [o1, o2]                                -- $ added
  toCode (Sub o1 o2) = format "sub" [o1, o2]
  toCode (FSub o1 o2) = format "subsd" [o1, o2]                                -- $ added
  toCode (IMul o1 o2) = format "imul" [o1, o2]
  toCode (IMul' o1 o2 o3) = format "imul" [o1, o2, o3]
  toCode (FMul o1 o2) = format "mulsd" [o1, o2]                                -- $ added
  toCode (IDiv o1)
    | isM o1 = "idiv QWORD " ++ toCode o1
    | otherwise = format "idiv" [o1]
  toCode (FDiv o1 o2) = format "divsd" [o1, o2]                                -- $ added
  toCode (Cmp o1 o2) = format "cmp" [o1, o2]
  toCode (FCmp o1 o2) = format "comisd" [o1, o2]                               -- $ added
  toCode (Neg o1)
    | isM o1 = "neg QWORD " ++ toCode o1
    | otherwise = format "neg" [o1]
  toCode (FNeg o1) = "movsd xmm0, [sign_mask]\npxor " ++ toCode o1 ++ ", xmm0" -- $ added
  toCode (Push o1)                                                             -- $ modified
    | isM o1 = "push QWORD " ++ toCode o1
    | otherwise = "push " ++ toCode o1
  toCode (Pop o1)                                                              -- $ modified
    | isM o1 = "pop QWORD " ++ toCode o1
    | otherwise = "pop " ++ toCode o1
  toCode (Shl o1 o2)
    | isM o1 = format "shl QWORD" [o1, o2]
    | otherwise = format "shl" [o1, o2]
  toCode (Sar o1 o2)
    | isM o1 = format "sar QWORD" [o1, o2]
    | otherwise = format "sar" [o1, o2]
  toCode (Instr s) = s
  toCode (Call s) = "call " ++ s
  toCode (DATA o) = "dq "++ toCode o
  toCode (Solve oTo oFrom label) = "multipush rbx, r8, r9, r10, r11\n"++
                                   ";get Index\n"++
                                   "mov RBX, "++toCode oFrom++"\n"++
                                   "mov R8, [RBX]\n"++
                                   "mov R9, [R8 +8]\n"++
                                   "mov R10, ["++label++" + 16]\n"++
                                   "mov R11, [R9 +8 + R10*8]\n"++
                                   "; TODO check R11 == "++label++"\n"++
                                   "mov R9, [R8 + 16]\n"++
                                   "mov R11, [R9+8+R10 *8]\n"++
                                   "mov RAX, [RBX + R11]\n"++
                                   "multipop rbx, r8, r9, r10, r11\n"++
                                   "mov "++toCode oTo++", RAX\n"

  toCode (MCall oTo oFrom label) = 
                                  "multipush r8, r9, r10, r11\n"++
				  "mov r8, ["++ toCode oFrom++"]\n"++
				  "add r8, 24\n"++
				  "mov r9, [r8]\n"++
				  "mov r11, "++label++"\n"++
				  "add r11,16\n"++
				  "mov r10, [r11]\n"++
				  "imul r10, 8\n"++
				  "add r10,8\n"++
				  "mov r11, r9\n"++
				  "add r11, r10\n"++
				  "cmp QWORD [r11], "++label++"\n"++
				  "jne alloc_error ; TODO change error prompt\n"++
				  "add r8, 32\n"++
				  "mov r9, [r8]\n"++
				  "mov r11, r9\n"++
				  "add r11, r10\n"++
				  "mov r8, [r11]\n"++
				  "call r8\n"++
				  "pop rax\n"++
				  "multipop r8,r9,r10,r11\n"++
				  "mov "++ toCode oTo++", rax" 

format :: String -> [Operand] -> String
format ins ops = ins ++ " " ++ intercalate ", " (toCode <$> ops)

isL, isM, isR, isFR, isI, isD :: Operand -> Bool
isL = operandIsLocation
isM = operandIsStackLocation
isR = operandIsRegister
isFR= operandIsFRegister       -- $ added
isI = operandIsImmediate
isD = operandIsImmediateDouble -- $ added

imul' :: Operand -> Operand -> Operand -> Maybe Instruction
mov, fmov, add, fadd, sub, fsub, imul, fmul, fdiv, cmp, fcmp, shl, sar
  :: Operand -> Operand -> Maybe Instruction
mov', idiv, push, pop, neg, fneg :: Operand -> Maybe Instruction
instr :: String -> Maybe Instruction
mov o1 o2
  | isL o1 && not (isM o2) || isR o1 = Just (Mov o1 o2)
  | otherwise = error $ "mov "++show o1++", "++show o2++" is not supported"
mov' o1                                                      -- $ added
  | isI o1 = Just (Mov' o1)
  | otherwise = error $ "mov' "++show o1++" is not supported"
fmov o1 o2                                                   -- $ added
  | isL o1 && isR o2 || isR o1 && isL o2 = Just (FMov o1 o2)
  | otherwise = error $ "fmov "++show o1 ++ " "++show o2++ " is not supported"
add o1 o2
  | isL o1 && not (isM o2) || isR o1 = Just (Add o1 o2)
  | otherwise = error $ "add "++show o1++" "++show o2++ " is not supported"
fadd o1 o2                                                   -- $ added
  | isR o1 && isR o2 = Just (FAdd o1 o2)
  | otherwise = error $ "fadd "++ show o1 ++ " "++ show o2++ " is not supported"
sub o1 o2
  | isL o1 && not (isM o2) || isR o1 = Just (Sub o1 o2)
  | otherwise = error $ "sub "++ show o1 ++ " " ++ show o2++ " is not supported" 
fsub o1 o2                                                   -- $ added
  | isR o1 && isR o2 = Just (FSub o1 o2)
  | otherwise = error $ "fsub "++ show o1 ++" "++ show o2 ++ " is not supported"
imul o1 o2
  | isR o1 && isL o2 = Just (IMul o1 o2)
  | otherwise = error $ "imul "++ show o1 ++ " "++ show o2++ " is not supported"
imul' o1 o2 o3
  | isR o1 && isL o2 && isI o3 = Just (IMul' o1 o2 o3)
  | otherwise = error $ "imul' "++ show o1 ++ " "++ show o2++ " " ++ show o3++ " is not supported"
fmul o1 o2                                                   -- $ added
  | isR o1 && isR o2 = Just (FMul o1 o2)
  | otherwise = error $ "fmul "++ show o1 ++ " " ++ show o2 ++ " is not supported"
idiv o1
  | isL o1 = Just (IDiv o1)
  | otherwise = error $ "idiv "++ show o1++ " is not supported" 
fdiv o1 o2                                                   -- $ added
  | isR o1 && isR o2 = Just (FDiv o1 o2)
  | otherwise = error $ "fdiv "++ show o1 ++ " "++ show o2++ " is not supported"
cmp o1 o2
  | isR o1 || isL o1 && not (isM o2) = Just (Cmp o1 o2)
  | otherwise = error $ "cmp "++ show o1 ++ " "++ show o2++ " is not supported"
fcmp o1 o2                                                   -- $ added
  | isR o1 && isL o2 = Just (FCmp o1 o2)
  | otherwise = error $ "fcmp "++ show o1 ++ " "++show o2++" is not supported"
neg o1
  | isL o1 = Just (Neg o1)
  | otherwise = error $"neg "++ show o1++" is not supported"
fneg o1                                                      -- $ added
  | isFR o1 = Just (FNeg o1)
  | otherwise = error $ "fneg "++ show o1++" is not supported" 
push o1
  | not (isFR o1) = Just (Push o1)
  | otherwise = error $ "push "++ show o1++ "is not supported"
pop o1
  | isL o1 && not (isFR o1) = Just (Pop o1)                  -- $ modified
  | otherwise = error $ "pop "++ show o1 ++" is not supported" 
shl o1 o2
  | isL o1 && isI o2 = Just (Shl o1 o2)
  | otherwise = error $ "shl "++ show o1 ++" "++ show o2++" is not supported"
sar o1 o2
  | isL o1 && isI o2 = Just (Sar o1 o2)
  | otherwise =error $ "sar "++show o1 ++" "++show o2++ "is not supported" 
instr i = Just (Instr i)

{-

Argument types for the various assembler instructions:

MOV   1 = 2
      reg64/mem64 , reg64
      reg64       , reg64/mem64
      reg64       , imm64
      reg64/mem64 , imm32

ADD   1 = 1 + 2
      reg64/mem64 , imm32
      reg64/mem64 , imm8
      reg64/mem64 , reg64
      reg64       , reg64/mem64

SUB   1 = 1 - 2
      reg64/mem64 , imm32
      reg64/mem64 , imm8
      reg64/mem64 , reg64
      reg64       , reg64/mem64

IMUL  1 = 1 * 2
      reg64       , reg64/mem64
      1 = 2 * 3
      reg64       , reg64/mem64 , imm32

IDIV  RAX = RDX:RAX / 1 ; RDX = RDX:RAX % 1
      reg64/mem64

CMP
      reg64/mem64 , imm32
      reg64/mem64 , reg64
      reg64       , reg64/mem64

--------------------------------------------------------------------------------

18 POSSIBLE COMBINATIONS FROM TAC

R = R + R
R = R + M
R = R + I
R = M + R
R = M + M
R = M + I
R = I + R
R = I + M
M = R + R
M = R + M
M = R + I
M = M + R
M = M + M
M = M + I
M = I + R
M = I + M

REMOVED BY PRIOR OPTIMIZATION:

R = I + I
M = I + I

-}
