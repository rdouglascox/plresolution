module Main where

import Prop
import System.IO
import Clauses 

main :: IO ()
main = do 
    x <- getContents
    case parser x of 
        Nothing -> putStrLn "no parse!"
        Just xs -> rprove xs