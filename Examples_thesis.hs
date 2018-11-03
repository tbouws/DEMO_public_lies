{-
Module containing examples for thesis The Logic of Public Lies.

author: Tessa Bouws
-}

module Examples_thesis where

import Data.List
import EREL
import DEMO_S5
import EREL_KD45
import DEMO_KD45
import DEMO_dyn_KD45
import AcceptableInput

alice,bob,carol :: Agent
alice = Ag 0
bob = Ag 1
carol = Ag 2

example5 :: EpistM Int
example5 = Mo
 [1..4]
 [alice,bob,carol]
 [(1,[P 0]) , (2,[]) , (3,[P 0]) , (4,[])]
 [(alice,[[1],[2],[3],[4]]),
  (bob,[[1,2],[3],[4]]) , (carol,[[1,2,3,4]])]
 [1]

ex5_a_knows = Box alice (Prp (P 0))
ex5_a_knows_whether = Disj [Box alice (Prp (P 0))
                            , Box alice (Ng (Prp (P 0)))]
ex5_bc_dont_know = Conj [Ng (Box bob (Prp (P 0)))
                         , Ng (Box bob (Ng (Prp (P 0))))
                         , Ng (Box carol (Prp (P 0)))
                         , Ng (Box carol (Ng (Prp (P 0))))]
conjunction = Conj [ex5_a_knows_whether, ex5_bc_dont_know]
ex5_ab_know_that = Conj [Box agent conjunction
                           | agent <- [alice,bob]]
ex5_c_dsnt_know = Ng (Box carol conjunction)

example6 :: KD45model Int
example6 = MoKD45
  [1,2]
  [alice,bob]
  [(1,[P 0]),(2,[])]
  [ (alice,[([1],[2])]) , (bob,[([1,2],[])]) ]
  [1]

ex6_a_believes = ex5_a_knows
ex6_b_dsnt_believe = Conj [Ng (Box bob (Prp (P 0)))
                         , Ng (Box bob (Ng (Prp (P 0))))]

example7_1 :: EpistM Int
example7_1 = Mo
  [1,2]
  [alice,bob]
  [(1,[P 0]),(2,[])]
  [(alice,[[1],[2]]),(bob,[[1,2]])]
  [1]

ann_heads :: Form Int
ann_heads = Prp (P 0)

example7_2 :: EpistM Int
example7_2 = upd_pa example7_1 ann_heads

example8_1 :: KD45model Int
example8_1 = MoKD45
  [1,2]
  [alice,bob]
  [(1,[P 0]),(2,[])]
  [ (alice,[([1],[2])]) , (bob,[([2],[1])]) ]
  [1]

example8_2 :: KD45model Int
example8_2 = upd_pa_KD45 example8_1 ann_heads

example9 :: KD45model Int
example9 = upd_pa_arrow example8_1 ann_heads

upd_public_lie :: Ord state =>
            KD45model state -> Form' state -> KD45model state
upd_public_lie = upd_public_statement

ann_tails :: Form' Int
ann_tails = Ng' (Prp' (P 0))

example12 :: KD45model Int
example12 = upd_public_lie example6 ann_tails

example13 :: KD45model Int
example13 = upd_recovery_dynamic example12 (Ng' ann_tails)
