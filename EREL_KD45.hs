{-
Module that implements the almost-equivalence-relations on KD45-models, which
are defined in my thesis The Logic of Public Lies.
This module is inspired by the module EREL by Jan van Eijck.

author: Tessa Bouws
-}

module EREL_KD45 where

import Data.List
import EREL

{- | Constructing a type synonym for the KD45-equivalent of a partition -}
type InnerRing a = [a]
type OuterRing a = [a]
type KD45block a = (InnerRing a, OuterRing a)
type KD45partition a = [KD45block a]

{- | Checks if two KD45blocks overlap -}
overlapKD45bl :: Ord a => (InnerRing a, OuterRing a) ->
                          (InnerRing a, OuterRing a) -> Bool
overlapKD45bl (as,bs) (xs,ys) = overlap as bs
                                || overlap xs ys
                                || overlap (concat [as,bs]) (concat [xs,ys])

{- | Checks if something of type KD45partition is indeed an almost-partition -}
isKD45part :: (Ord a) => KD45partition a -> Bool
isKD45part [] = True
isKD45part [([],[])]  = True
isKD45part [([],outs)] = False
isKD45part (b:bs) = all (not.overlapKD45bl b) bs &&
                  isKD45part bs

{- | Checks if something of type KD45partition is a K45-partion -}
isK45part :: (Ord a) => KD45partition a -> Bool
isK45part [([],outs)] = True
isK45part bs = isKD45part bs


{- | Go from an almost-partition to its domain -}
domKD45part :: Ord a => KD45partition a -> [a]
domKD45part bs = mergeL [merge (fst b) (snd b) | b <- bs]

{- | Extracts a KD45-block given a world and an agent -}
blKD45 :: Eq a => KD45partition a -> a -> KD45block a
blKD45 [] x = ([],[])
blKD45 [([],[])] x = ([],[])
blKD45 [([y],[])] x | (x == y) = ([y],[])
                    | otherwise = ([],[])
blKD45 [([y],[z])] x | (x == y) || (x == z) = ([y],[z])
                     | otherwise = ([],[])
blKD45 [([y],zs)] x | (x == y) || elem x zs = ([y],zs)
                    | otherwise = ([],[])
blKD45 [([],[z])] x | (x == z) = ([],[z])
                    | otherwise = ([],[])
blKD45 [(ys,[z])] x | (x == z) || elem x ys = (ys,[z])
                    | otherwise = ([],[])
blKD45 (b:bs) x | elem x (fst b) || elem x (snd b) = b
                | otherwise = blKD45 bs x

restrictKD45 :: Ord a => [a] -> KD45partition a -> KD45partition a
restrictKD45 domain [] = []
restrictKD45 domain (b:blocks) =
  filter (/= ([],[])) ((new_ins, new_outs):(restrictKD45 domain blocks))
    where
   new_ins = filter (flip elem domain) (fst b)
   new_outs = filter (flip elem domain) (snd b)
