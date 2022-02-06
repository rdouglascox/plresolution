module Clauses (rprove) where 

import Prop
import Data.Maybe
import qualified Data.Set as Set

import Data.Tree

import Data.Either
import System.Posix.Internals (c_ftruncate)
import Data.List (intersperse, intercalate)

-- data 

type Clauses = Set.Set (Set.Set Prop)

-- converting props to cnf and then to clauses 

-- implications 

-- COND

imp1 :: Prop -> Prop
imp1 (Conditional pr pr') = Disjunction (Negation pr) pr'
imp1 x =x

-- BCON 
imp2 :: Prop -> Prop
imp2 (Biconditional l r) = Conjunction (Disjunction (Negation l) r) (Disjunction l (Negation r))
imp2 x = x

-- negations

-- DNEG
neg1 :: Prop -> Prop
neg1 (Negation (Negation p)) = p
neg1 x = x

-- NCONJ
neg2 :: Prop -> Prop
neg2 (Negation (Conjunction l r)) = Disjunction (Negation l) (Negation r)
neg2 x = x

-- NDISJ
neg3 :: Prop -> Prop
neg3 (Negation (Disjunction l r)) = Conjunction (Negation l) (Negation r)
neg3 x = x

-- distribution

-- DISTR
dis1 :: Prop -> Prop
dis1 (Disjunction p (Conjunction l r)) = Conjunction (Disjunction p l) (Disjunction p r)
dis1 x = x

-- DISTL
dis2 :: Prop -> Prop
dis2 (Disjunction (Conjunction l r) p) = Conjunction (Disjunction l p) (Disjunction r p)
dis2 x = x

allrules :: Prop -> Prop
allrules = propmap imp1 . propmap imp2 . propmap neg1 . propmap neg2 . propmap neg3 . propmap dis1 . propmap dis2

allrulesloop :: Prop -> Prop
allrulesloop p = if allrules p == p
  then p
  else allrules p


-- | map a function from props to props over a prop
propmap :: (Prop -> Prop) -> Prop -> Prop
propmap r p = case p of
  Negation pr -> r $ Negation (propmap r pr)
  Conjunction pr pr' -> r $ Conjunction (propmap r pr) (propmap r pr')
  Disjunction pr pr' -> r $ Disjunction (propmap r pr) (propmap r pr')
  Conditional pr pr' -> r $ Conditional (propmap r pr) (propmap r pr')
  Biconditional pr pr' -> r $ Biconditional (propmap r pr) (propmap r pr')
  _ -> p

tocnf :: [Prop] -> [Prop]
tocnf [] = []
tocnf x =
  let a = checkapply imp1 x in
  let b = checkapply imp2 a in
  let c = checkapply neg2 b in
  let d = checkapply neg3 c in
  let e = checkapply neg1 d in
  let f = checkapply disloop e in
  let g = checkapply allrulesloop f in
  g

checkapply :: (Prop -> Prop) -> [Prop] -> [Prop]
checkapply r ps =
  let new = propmap r (head ps) in
    if new == head ps
      then ps
      else new : ps

toclauses :: Prop -> Clauses
toclauses (Conjunction (Conjunction l1 r1) (Conjunction l2 r2)) = Set.union (Set.union (toclauses l1) (toclauses r1)) (Set.union (toclauses l2) (toclauses r2))
toclauses (Conjunction l (Conjunction l2 r2)) = Set.insert (toclause l) $ Set.union (toclauses l2) (toclauses r2)
toclauses (Conjunction (Conjunction l1 r1) r) = Set.insert (toclause r) $ Set.union (toclauses l1) (toclauses r1)
toclauses (Conjunction l r) = Set.insert (toclause l) $ Set.singleton (toclause r)
toclauses x = Set.singleton $ toclause x

toclause :: Prop -> Set.Set Prop
toclause (Disjunction (Disjunction l1 r1) (Disjunction l2 r2)) = Set.union (Set.union (toclause l1) (toclause r1)) (Set.union (toclause l2) (toclause r2))
toclause (Disjunction l (Disjunction l2 r2)) = Set.insert l $ Set.union (toclause l2) (toclause r2)
toclause (Disjunction (Disjunction l1 r1) r) = Set.insert r $ Set.union (toclause l1) (toclause r1)
toclause (Disjunction l r) = Set.insert l $ Set.singleton r
toclause x = Set.singleton x


cnftree :: Prop -> Tree String
cnftree (Conjunction l r) = Node "&" [cnftree l, cnftree r]
cnftree (Disjunction l r) = Node "v" [cnftree l, cnftree r]
cnftree (Basic s) = Node s []
cnftree (Negation (Basic s)) = Node "~" [cnftree (Basic s)]
cnftree _ = Node "?" []

printClauses :: Clauses -> String
printClauses s = "{" ++ concatMap printSets s ++ "}"

printSets :: Set.Set Prop -> String
printSets s = "{" ++ intercalate "," (map show (Set.toList s)) ++ "}"

-- resolution

-- at some point, we will want all pairs of clauses 

allpairs :: Clauses -> [(Set.Set Prop,Set.Set Prop)]
allpairs cl = [ (x,y) | x <- Set.toList cl, y <- Set.toList cl, x /= y]

-- then we will want a way of checking if we can resolve on a pair by finding
-- a lit and its neg in a pair. what we want from this function is 
-- (i) the guilty pair of clauses and (ii) the prop to resolve on

negatelit :: Prop -> Prop
negatelit (Basic p) = Negation (Basic p)
negatelit (Negation p) = p
negatelit _ = error "no negated lits for nonlits!"

isneg :: Prop -> Bool
isneg (Negation p) = True
isneg _ = False

isnegpos :: (Set.Set Prop, Set.Set Prop) -> Maybe Prop
isnegpos (x,y) =
  let negpos = Set.filter (isnp (x,y)) x in
    if negpos == Set.empty
      then Nothing
      else Set.lookupMin negpos

-- predicate for filtering negpos

isnp :: (Set.Set Prop, Set.Set Prop) -> Prop -> Bool
isnp (x,y) z = Set.member z x && Set.member (negatelit z) y


-- | go through a list of pairs of clauses and, if and pair has a neg pos
-- then return the pair that needs to be targeted and the prop to target

negposlist :: [(Set.Set Prop, Set.Set Prop)] -> Maybe Prop
negposlist [] = Nothing
negposlist (x:xs) = case isnegpos x of
  Nothing -> negposlist xs
  Just pr -> Just pr

-- | make a new clause from clauses by collecting the 'rest'
-- with respect to a resolvant and its negation

replacements :: [Set.Set Prop] -> Prop -> Set.Set Prop
replacements [] p = Set.empty
replacements (x:xs) p = if Set.member p x || Set.member (negatelit p) x
                      then Set.union (Set.filter (/= negatelit p) $ Set.filter (/= p) x) (replacements xs p)
                      else replacements xs p

removefromclauses :: Prop -> Clauses -> Clauses
removefromclauses p cl = Set.filter (Set.member p) $ Set.filter (Set.member (negatelit p)) cl

resolve' :: Clauses -> (Clauses,Maybe Prop)
resolve' cl =
  let allp = allpairs cl in
  let isngp = negposlist allp in case isngp of
    Nothing -> (cl,Nothing)
    Just pr -> let new = removefromclauses pr cl in
      let add = replacements (Set.toList cl) pr in
        (Set.insert add new,Just pr)

doresolve :: Clauses -> IO Clauses
doresolve x = do
  y <- dotriv x
  let (new,just) = resolve' y
  if new == y
    then return y
    else do
      putStrLn ("---resolve on " ++ show (fromJust just))
      putStrLn (printClauses new)
      doresolve new

rprove :: Prop -> IO ()
rprove p = do
  putStrLn "---[input]"
  print p
  a <- doimp1 p
  b <- doimp2 a
  k <- dneg b
  c <- domorgan k
  d <- dneg c
  e <- distribute d
  let clauses = toclauses e
  putStrLn "---[to clauses]"
  putStrLn (printClauses clauses)
  f <- doresolve clauses
  finalverdict f 
  return ()

finalverdict :: Clauses -> IO ()
finalverdict cl
  | Set.null cl = do putStrLn "---[input a tautology]"
  | cl == Set.singleton Set.empty = do putStrLn "---[input not satisfiable]"
  | otherwise = do putStrLn "---[input satisfiable]"

doimp1 :: Prop -> IO Prop
doimp1 p = do
  let new = propmap imp1 p
  if p == new
    then return p
    else do
       putStrLn "---[remove ->]"
       print new
       return new

doimp2 :: Prop -> IO Prop
doimp2 p = do
  let new = propmap imp2 p
  if p == new
    then return p
    else do
       putStrLn "---[remove <->]"
       print new
       return new

domorgan :: Prop -> IO Prop
domorgan p = do
  let new = snegloop p
  if p == new
    then return p
    else do
       putStrLn "---[de morgan's laws]"
       print new
       return new

snegloop :: Prop -> Prop
snegloop p =
  let new = sneg1 p in
    if p == new
      then p
      else snegloop new

sneg1 :: Prop -> Prop
sneg1 (Negation (Conjunction l r)) = Disjunction (Negation (sneg1 l)) (Negation (sneg1 r))
sneg1 (Negation (Disjunction l r)) = Conjunction (Negation (sneg1 l)) (Negation (sneg1 r))
sneg1 (Negation p) = Negation (sneg1 p)
sneg1 (Conjunction l r) = Conjunction (sneg1 l) (sneg1 r)
sneg1 (Disjunction l r) = Disjunction (sneg1 l) (sneg1 r)
sneg1 (Conditional l r) = Conditional (sneg1 l) (sneg1 r)
sneg1 (Biconditional l r) = Biconditional (sneg1 l) (sneg1 r)
sneg1 x = x

dneg :: Prop -> IO Prop
dneg p = do
  let new = propmap neg1 p
  if p == new
    then return p
    else do
       putStrLn "---[double negation]"
       print new
       return new

distribute :: Prop -> IO Prop
distribute p = do
  let new = disloop p
  if p == new
    then return p
    else do
       putStrLn "---[distribute v]"
       print new
       return new

disloop :: Prop -> Prop
disloop p =
  let new = dis p in
    if new == p
      then p
      else disloop new

dis :: Prop -> Prop
dis (Disjunction p (Conjunction l r)) = Conjunction (Disjunction (dis p) (dis l)) (Disjunction (dis p) (dis r))
dis (Disjunction (Conjunction l r) p) = Conjunction (Disjunction (dis l) (dis p)) (Disjunction (dis r) (dis p))
dis (Negation p) = Negation (dis p)
dis (Conjunction l r) = Conjunction (dis l) (dis r)
dis (Disjunction l r) = Disjunction (dis l) (dis r)
dis (Conditional l r) = Conditional (dis l) (dis r)
dis (Biconditional l r) = Biconditional (dis l) (dis r)
dis x = x


trivial :: Set.Set Prop -> Bool
trivial ps = not $ or $ Set.toList $ Set.map (\x -> Set.member x ps && Set.member (Negation x) ps) ps

dotriv :: Clauses -> IO Clauses
dotriv cl =
  let new = Set.filter trivial cl in
    if new == cl
      then return new
      else do
        putStrLn "---[remove trivials]"
        putStrLn (printClauses new)
        dotriv new

