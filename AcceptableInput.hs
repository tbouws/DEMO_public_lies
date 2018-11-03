{- Module that contains an algorithm to determine the maximal acceptable set
of formulas for an agent in a world. An intuitivy explanation on how the
algorithm works can be found in the thesis.

author: Tessa Bouws
-}
module AcceptableInput where

import Data.List
import EREL
import DEMO_S5
import EREL_KD45
import DEMO_KD45
import DEMO_dyn_KD45

{- | If the conjunction of all the formulas in a set is believable for an
agent in a certain world, then we call this set acceptable for this agent
in this and world. -}
condition_mas_f :: (Eq a, Ord a) =>
                   [Form' a] -> KD45model a -> Agent -> a -> Bool
condition_mas_f fs m@(MoKD45 states ags vals rels actuals) ag1 w =
    let rel_ag1 = relKD45 ag1 m
        bl_ag1 = blKD45 rel_ag1 w
        belief_cell = fst bl_ag1
    in any (\v -> isTrueAt' m v (Conj' fs)) belief_cell

{- | mas_f outputs the maximal acceptable set of formulas for an agent
in a world. -}
mas_f :: (Eq a, Ord a) => [Form' a] -> KD45model a -> Agent -> a -> [Form' a]
mas_f = mas_f_algorithm 0


mas_f_algorithm :: (Eq a, Ord a) =>
     Int -> [Form' a] -> KD45model a -> Agent -> a -> [Form' a]
mas_f_algorithm _ [] _ _ _ = []
mas_f_algorithm k fs m ag1 w
    | condition_mas_f fs m ag1 w = fs
    | otherwise =
        let subsets_fs = subsets (k+1) fs;
            acc_subsets = [sub | sub <- subsets_fs
                           , condition_mas_f sub m ag1 w]
            fs' = [f | f <- fs, elem f (concat acc_subsets)]
        in  mas_f_algorithm (k+1) fs' m ag1 w


subsets :: Int -> [a] -> [[a]]
subsets 0 _ = [[]]
subsets _ [] = []
subsets k (x:xs) = map (x:) (subsets (k - 1) xs) ++ subsets k xs
