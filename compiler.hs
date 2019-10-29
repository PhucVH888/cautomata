module Main where

import System.Environment
import System.Directory
import System.IO
import System.Exit
import System.Process
import System.Posix.Directory
import Data.List
import Data.Maybe
import Control.Monad
import qualified Data.Map.Strict as Map
import Language.Haskell.TH -- for Template Haskell hackery
import System.FilePath (splitPath, joinPath)

-- data Predicate =
--     Predicate {
--         Body   :: String
--     } deriving(Eq, Show)

data Expr = IfThen {c :: String,
                    t :: Expr,
                    e :: Expr}
          | NewLine {val :: String}
          | Body {val :: String}

newLine :: String
newLine = "\n"

preHeader :: String
preHeader = "predicate group_counter(array[int] of int: a, var int: counter) =" ++ newLine

preFixedDecl :: String
preFixedDecl = "var int: counter;\n\
\\n\
\array[int] of int: a;\n\
\\n\
\a = [0,1,0,1];\n"

preFixedInit :: String
preFixedInit = "  let {\n\
\    int: n = length(a),\n\
\    array[0..n] of var int: c,\n\
\    array[1..n] of var int: s,\n\
\  }\n\
\  in\n\
\  c[0] = 0\n\
\  /\\ \n\
\  s[1] = 1\n\
\\n"

type Idx      = String
type FstS     = String
type Arg      = String
type SndS     = String
type Opr      = String

type C        = String
type T        = String
type E        = String

data State    = State Idx FstS Arg SndS Opr

data If       = If C T E

-- getState :: State -> (Idx, FstS, Arg, SndS, Opr)
-- getState (State i f a s o) = (i,f,a,s,o)
--
-- getIf :: If -> (C,T,E)
-- getIf (If c t f) = (c,t,e)
inc :: String -> String
inc s = show $ (read s :: Int) + 1

dec :: String -> String
dec s = show $ (read s :: Int) - 1

prtOpr :: String -> String -> Int -> String
prtOpr idx "inc" 1  = "c[" ++ idx ++ "] = c[" ++ (dec idx) ++ "] + 1\n"
prtOpr idx "inc" _  = "c" ++ idx ++ " = c" ++ (dec idx) ++ " + 1\n"
prtOpr idx "dec" 1  = "c" ++ idx ++ " = c" ++ (dec idx) ++ " - 1\n"
prtOpr idx "same" 1 = "c[" ++ idx ++ "] = c[" ++ (dec idx) ++ "]\n"
prtOpr idx "same" _ = "c" ++ idx ++ " = c" ++ (dec idx) ++ "\n"
prtOpr idx _ _      = "unknown operation\n"

prtComment :: State -> String
prtComment (State idx fst arg snd opr) =
    do "% s" ++ idx ++ " = " ++ fst ++ ", a " ++ idx ++ " = " ++ arg ++ ", s" ++ (inc idx) ++ " = " ++ snd ++ ", " ++ prtOpr idx opr 0

andSym :: String
andSym = "/\\ "

isFinalState :: String -> Bool
isFinalState idx = "4" == idx

preIfThenElse :: If -> State -> (String, String, String, String) -> String
preIfThenElse (If c t e) (State idx fst arg snd opr) (i1, i2, i3, i4) =
    prtComment (State idx fst arg snd opr) ++
    "% s[" ++ idx ++ "] = 1 \n" ++
    "if (s[" ++ idx ++ "] = " ++ fst ++ ") then\n" ++
    "    if (a[" ++ idx ++ "] = " ++ arg ++ ") \n" ++
    "    then " ++
            (if (isFinalState idx)
            then ""
            else "s[" ++ (inc idx) ++ "] = 1 /\\ ")
            ++ prtOpr idx i1 1 ++
    "    else " ++
            (if (isFinalState idx)
            then ""
            else "s[" ++ (inc idx) ++ "] = 2 /\\ ")
            ++ prtOpr idx i2 1 ++
    "    endif\n" ++
    "% s[" ++ idx ++ "] = 2 \n" ++
    "else \n" ++
    "    if (a[" ++ idx ++ "] = " ++ arg ++ ") \n" ++
    "    then " ++
            (if (isFinalState idx)
            then ""
            else "s[" ++ (inc idx) ++ "] = 1 /\\ ")
            ++ prtOpr idx i3 1 ++
    "    else " ++
            (if (isFinalState idx)
            then ""
            else "s[" ++ (inc idx) ++ "] = 2 /\\ ")
            ++ prtOpr idx i4 1 ++
    "    endif\n" ++
    "endif\n"

getOpr :: (String, String, String, String)
getOpr = ("same", "inc", "same", "same")

cCodeGen :: String
cCodeGen =
    preFixedDecl ++
    preHeader ++
    preFixedInit ++
    andSym
    ++
    preIfThenElse (If "c" "t" "e")
                  (State "1" "1" "0" "1" "same")
                  getOpr
    ++
    andSym
    ++
    preIfThenElse (If "c" "t" "e")
                  (State "2" "1" "1" "2" "inc")
                  getOpr
    ++
    andSym
    ++
    preIfThenElse (If "c" "t" "e")
                  (State "3" "2" "0" "1" "same")
                  getOpr
    ++
    andSym
    ++
    preIfThenElse (If "c" "t" "e")
                  (State "4" "2" "1" "2" "same")
                  getOpr
    ++ andSym ++ newLine ++
    " counter = c[n]\n\
    \;\n" ++
    "constraint group_counter([0,1,0,1], counter);\n\
    \\n\
    \solve satisfy;\n\
    \\n\
    \output [\"Number of group 1: counter = \\(counter) \\n\" ++\n\
    \        \"A = \\(a) \" \n\
    \        ];\n"


main =
    do --putStrLn "== Parsing =="
       --
       -- putStrLn "== Converting strings =="
       -- --
       -- putStrLn "== Desugaring =="
       -- --
       -- putStrLn "== Prechecking =="
       -- --
       -- putStrLn "== Typechecking =="
       -- --
       putStrLn "== Code Generating =="
       writeFile "./out1.mzn" cCodeGen
       --
       putStrLn "== Done =="

selectState :: State -> String
selectState iState = do
   let (State a b c d e) = iState
   a ++ b ++ c ++ d ++ e

testRest :: String
testRest = "  % s1 = 1, a1 = 0, s2 = 1, c1 = c0     : same\n\
        \  /\\ % s1\n\
        \  if (s[1] = 1) then\n\
        \    if (a[1] = 0) \n\
        \    then s[2] = 1 /\\ c[1] = c[0] \n\
        \    else s[2] = 2 /\\ c[1] = c[0] + 1 \n\
        \    endif\n\
        \  % s[1] = 2 \n\
        \  else \n\
        \    if (a[1] = 0) \n\
        \    then s[2] = 1 /\\ c[1] = c[0]\n\
        \    else s[2] = 2 /\\ c[1] = c[0]\n\
        \    endif\n\
        \  endif\n\
        \    \n\
        \  % s2 = 1, a2 = 1, s3 = 2, c2 = c1 + 1 : inc\n\
        \  /\\ % s2\n\
        \  if (s[2] = 1) then\n\
        \    if (a[2] = 0) \n\
        \    then s[3] = 1 /\\ c[2] = c[1]\n\
        \    else s[3] = 2 /\\ c[2] = c[1] + 1 \n\
        \    endif\n\
        \  % s[2] = 2 \n\
        \  else \n\
        \    if (a[2] = 0) \n\
        \    then s[3] = 1 /\\ c[2] = c[1]\n\
        \    else s[3] = 2 /\\ c[2] = c[1]\n\
        \    endif\n\
        \  endif\n\
        \\n\
        \  % s3 = 2, a3 = 0, s4 = 1, c3 = c2     : same\n\
        \  /\\ % s3\n\
        \  if (s[3] = 1) then\n\
        \    if (a[3] = 0) \n\
        \    then s[4] = 1 /\\ c[3] = c[2]\n\
        \    else s[4] = 2 /\\ c[3] = c[2] + 1 \n\
        \    endif\n\
        \  % s[3] = 2 \n\
        \  else \n\
        \    if (a[3] = 0) \n\
        \    then s[4] = 1 /\\ c[3] = c[2]\n\
        \    else s[4] = 2 /\\ c[3] = c[2]\n\
        \    endif\n\
        \  endif\n\
        \\n\
        \  % s4 = q2, a4 = 1, empty , c4 = c3     : same\n\
        \  /\\ % s4\n\
        \  if (s[4] = 1) then\n\
        \    if (a[4] = 1) \n\
        \    then c[4] = c[3] + 1\n\
        \    else c[4] = c[3]\n\
        \    endif\n\
        \  % s[4] = 2 \n\
        \  else \n\
        \    if (a[4] = 0) \n\
        \    then c[4] = c[3]\n\
        \    else c[4] = c[3]\n\
        \    endif\n\
        \  endif\n\
        \\n\
        \  /\\  \n\
        \  counter = c[n]\n\
        \;\n\
        \\n\
        \constraint group_counter([0,1,0,1], counter);\n\
        \\n\
        \solve satisfy;\n\
        \\n\
        \output [\"Number of group 1: counter = \\(counter) \\n\" ++\n\
        \        \"A = \\(a) \" \n\
        \        ];\n"

--iPath <- "input/spec.mzn"
-- oPath = "output/output.mzn"
convert :: String -> String -> IO()
convert iPath oPath =
    do  iTh <- openFile iPath ReadMode
        oTh <- openFile oPath WriteMode
        mainloop iTh oTh
        hClose iTh
        hClose oTh
        res <- readFile oPath
        putStrLn res

mainloop :: Handle -> Handle -> IO()
mainloop iTh oTh =
    do iEOF <- hIsEOF iTh
       if iEOF then return()
       else do  inpStr <- hGetLine iTh
                hPutStrLn oTh ("\\" ++ inpStr ++ "\\n\\")
                mainloop iTh oTh
