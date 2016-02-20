{-|
  Module      : GarbageCollection.GarbageCollection
  Description :
  Copyright   : 2015, Tay Phuong Ho
  License     : GPL-3
-}
module GarbageCollection.GarbageCollection (
  dealloc, returnSequence
) where

import Prelude (
    String, Int, show,
    (/=), (==), 	
	(++), tail, length, zipWith3, filter, ($)
  )
import Data.Foldable (
    foldl'
  )
import Data.List.Split (
    splitOn
  )
import Data.List (
    intercalate
  )

import qualified Interface.TAC as TAC

-- $| Deallocates memory memory which is local to a scope at the end of said scope.
dealloc :: TAC.TAC -> TAC.TAC
dealloc tacs = deallocs
  where
    deallocs = foldl' foldFunc [] tacs
    foldFunc deallocs tac = case tac of
      TAC.ArrayAlloc v _ -> [TAC.Pop v] ++ [TAC.ArrayDealloc v] ++ deallocs
      TAC.ArrayDealloc _ -> tail deallocs
      TAC.ArrayCopy v _ -> filter (/=TAC.ArrayDealloc v) deallocs
      TAC.Pop _ -> tail deallocs
      _ -> deallocs

-- $| Adds the garbage collection routine in front of the regular function-return sequence.
returnSequence :: [String] -> [String] -> [Int] -> [String]
returnSequence names nasmCodes frames = if length names == 1 then []
                                        else zipWith3 (\name nasmCode frame -> "\n"
                                          ++ name ++ ":\n"
                                          ++ "mov rax, rbp\nmov rbp, rsp\nsub rsp, "
                                          ++ show frame ++
                                          "\nmov rdx, rsp\npush rdx\npush rax\nmultipush rbx, rcx, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15\nmultifpush xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7\nmov rax, rsp\nmov rsp, rbp\nadd rsp, 8\n"
                                          ++ (intercalate "\npush qword [rbp]\nmov [rdx-8], rsp\nmov rsp, rax\n" $ splitOn "call dummy\nmovq xmm1, xmm0" nasmCode)
                                            ++ "jmp return_error\n.return_sequence:\nmov rdx, rbp\nsub rdx, "
                                            ++ show frame
                                            ++ "\nsub rdx, 168\n.return_sequence2:\ncmp rsp, rdx\njge .return_sequence3\npop rdi\ncmp rdi, rbx\nje .return_sequence2\ncall free\njmp .return_sequence2\n.return_sequence3:\nmov rax, rbx\nmultifpop xmm1, xmm2, xmm3, xmm4, xmm5, xmm6, xmm7\nmultipop rbx, rcx, rsi, rdi, r8, r9, r10, r11, r12, r13, r14, r15\npop rbp\npop rsp\nret")
                                          (tail names) (tail nasmCodes) (tail frames)