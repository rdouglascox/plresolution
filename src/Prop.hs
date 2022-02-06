{-# LANGUAGE FlexibleContexts #-}

module Prop where

import Text.Parsec.Char
import Text.Parsec.Prim

-- data

data Prop = Basic String
    | Top
    | Bot
    | Negation Prop
    | Conjunction Prop Prop
    | Disjunction Prop Prop
    | Conditional Prop Prop
    | Biconditional Prop Prop
    deriving (Eq,Ord)

-- printing

instance Show Prop where
    show p = printProp p

printProp :: Prop -> String
printProp p = case p of
  Basic s -> s
  Top -> "t"
  Bot -> "f"
  Negation pr -> "~" ++ printProp pr
  Conjunction pr pr' -> "(" ++ printProp pr ++ "&" ++ printProp pr' ++ ")"
  Disjunction pr pr' -> "(" ++ printProp pr ++ "v" ++ printProp pr' ++ ")"
  Conditional pr pr' -> "(" ++ printProp pr ++ "->" ++ printProp pr' ++ ")"
  Biconditional pr pr' -> "(" ++ printProp pr ++ "<->" ++ printProp pr' ++ ")"

-- parsing 

lparS :: Stream s m Char => ParsecT s u m String
lparS = string "("
rparS :: Stream s m Char => ParsecT s u m String
rparS = string ")"

basic :: Stream s m Char => ParsecT s u m Prop
basic = do
    x <- upper
    return (Basic [x])

negation :: Stream s m Char => ParsecT s u m Prop
negation = do
    string "~"
    Negation <$> prop

conjunction :: Stream s m Char => ParsecT s u m Prop
conjunction = do
    lparS
    l <- prop
    string "&"
    r <- prop
    rparS
    return (Conjunction l r)

disjunction :: Stream s m Char => ParsecT s u m Prop
disjunction = do
    lparS
    l <- prop
    string "v"
    r <- prop
    rparS
    return (Disjunction l r)

conditional :: Stream s m Char => ParsecT s u m Prop
conditional = do
    lparS
    l <- prop
    string "->"
    r <- prop
    rparS
    return (Conditional l r)

biconditional :: Stream s m Char => ParsecT s u m Prop
biconditional = do
    lparS
    l <- prop
    string "<->"
    r <- prop
    rparS
    return (Biconditional l r)

prop :: Stream s m Char => ParsecT s u m Prop
prop = do
    try basic
    <|> try negation
    <|> try conjunction
    <|> try disjunction
    <|> try conditional
    <|> try biconditional

parser :: String -> Maybe Prop
parser x = case parse prop "" x of
    Left err -> Nothing
    Right xs -> Just xs