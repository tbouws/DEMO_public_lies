{-
Module containing an epistemic model checker for KD45-models, inspired by the
epistemic model checker DEMO_S5 by Jan van Eijck.
Contains several different functions to update models after public announcements.

author: Tessa Bouws
-}

module DEMO_KD45 where

import Data.List
import EREL
import EREL_KD45
import DEMO_S5

{- | a datatype for epistemic KD45-models -}
data KD45model state = MoKD45
                [state]
                [Agent]
                [(state,[Prp])]
                [(Agent,KD45partition state)]
                [state]  deriving (Eq,Show)

bi_impl :: Form a -> Form a -> Form a
bi_impl form1 form2 = Conj [impl form1 form2, impl form2 form1]

{- | Extract an epistemic relation for 1 agent from a model in the KD45 case -}
relKD45 :: Agent -> KD45model a -> KD45partition a
relKD45 ag (MoKD45 _ _ _ rels _) = apply rels ag

{- | Blissful ignorance in the KD45 case -}
initM_KD45 :: (Ord state) => (Num state, Enum state) =>
         [Agent] -> [Prp] -> KD45model state
initM_KD45 ag prps  = doS5toKD45 $ initM ag prps


{- | Semantic interpretation of the logical form language, KD45 version.
This treats the Boolean connectives as usual, and interprets Kn as
"being convinced", i.e. as truth in all worlds in the current accessible
InnerRing of a KD45block of an agent -}
isTrueAtKD45 :: Ord state =>
            KD45model state -> state -> Form state -> Bool
isTrueAtKD45 m w Top = True
isTrueAtKD45 m w (Info x) = w == x
isTrueAtKD45
  m@(MoKD45 worlds agents val acc points) w (Prp p) = let
   props = apply val w
  in
   elem p props
isTrueAtKD45 m w (Ng f) = not (isTrueAtKD45 m w f)
isTrueAtKD45 m w (Conj fs) = and (map (isTrueAtKD45 m w) fs)
isTrueAtKD45 m w (Disj fs) = or  (map (isTrueAtKD45 m w) fs)
isTrueAtKD45
 m@(MoKD45 worlds agents val acc points) w (Box ag f) = let
    r = relKD45 ag m
    b = blKD45 r w
  in
    and (map (flip (isTrueAtKD45 m) f) (fst b))

{- Truth in a KD45model is defined as truth in all actual worlds of the model. -}
isTrueKD45 :: Ord a => KD45model a -> Form a -> Bool
isTrueKD45 m@(MoKD45 worlds agents val acc points) f =
  all (\w -> isTrueAtKD45 m w f) points

{- | The effect of a public announcement by cutting links phi on an epistemic
model is that all links between phi-worlds and non-phi-worlds get deleted. -}
upd_pa_cut :: Ord state => EpistM state -> Form state -> EpistM state
upd_pa_cut m@(Mo states agents val rels actual) f =
  (Mo states agents val rels' actual)
   where
  states_phi = [ s | s <- states, isTrueAt m s f ]
  states_non_phi = [ s | s <- states, not(isTrueAt m s f) ]
  rels'   = merge [(ag,restrict states_phi r) | (ag,r) <- rels ]
                  [(ag,restrict states_non_phi r) | (ag,r) <- rels]


{- | Public announcement update of a belief model by elemination of states -}
upd_pa_KD45 :: Ord state =>
          KD45model state -> Form state -> KD45model state
upd_pa_KD45 m@(MoKD45 states agents val rels actual) f =
  (MoKD45 states' agents val' rels' actual')
   where
   states' = [ s | s <- states, isTrueAtKD45 m s f ]
   val'    = [ (s, ps) | (s,ps) <- val, s `elem` states' ]
   rels'   = [(ag,restrictKD45 states' r) | (ag,r) <- rels ]
   actual' = [ s | s <- actual, s `elem` states' ]

{- | Public announcement update by arrow elemination -}
upd_pa_arrow :: Ord state =>
    KD45model state -> Form state -> KD45model state
upd_pa_arrow m@(MoKD45 states agents val rels actual) f =
  (MoKD45 states agents val rels' actual)
  where
  rels' = [(ag, [(ins',outs')] ) | (ag, [(ins, outs)]) <- rels,
           let ins' = [s | s <- ins, isTrueAtKD45 m s f],
           let outs' = merge outs [s | s <- ins, not(isTrueAtKD45 m s f)]
          ]

{- | Convert an S5-model to a KD45-model with the same accessibilty relations. -}
doS5toKD45 :: (Ord state) => EpistM state -> KD45model state
doS5toKD45 m@(Mo states agents val rels actual) =
  (MoKD45 states agents val relsKD45 actual)
    where relsKD45 = [( ag, block ) | (ag,bs) <- rels,
                       let block = [(b,[]) | b <- bs] ]

{- | Change the actual worlds in a model -}
actualworldsKD45 :: [a] -> KD45model a -> KD45model a
actualworldsKD45 new_actuals (MoKD45 states agents val rels _) =
  (MoKD45 states agents val rels new_actuals)
