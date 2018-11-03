{-
Module containing an epistemic model checker for KD45-models, inspired by the
epistemic model checker DEMO_S5 by Jan van Eijck.
Contains several different functions to update models after public announcements.

author: Tessa Bouws
-}

module DEMO_dyn_KD45 where

import Data.List
import EREL
import DEMO_S5
import EREL_KD45
import DEMO_KD45

data Form' a = Top'
            | Info' a
            | Prp' Prp
            | Ng' (Form' a)
            | Conj' [Form' a]
            | Disj' [Form' a]
            | Box' Agent (Form' a)
            | Announcement' (Form' a) (Form' a)
            | Lie' (Form' a) (Form' a)
            | Statement' (Form' a) (Form' a)
            | Recovery' (Form' a) (Form' a)
          deriving (Eq,Ord,Show)

impl' :: Form' a -> Form' a -> Form' a
impl' form1 form2 = Disj' [Ng' form1, form2]

bi_impl' :: Form' a -> Form' a -> Form' a
bi_impl' form1 form2 = Conj' [impl' form1 form2, impl' form2 form1]

{- | Semantic interpretation of the logical form language, KD45 version.
This treats the Boolean connectives as usual, and interprets Box as
"being convinced", i.e. as truth in all worlds in the current accessible
InnerRing of a KD45block of an agent.
This function adds to the function in DEMO_KD45 the dynamic clauses, which are
used for checking formulas containing statements, announcements, lies
and recoveries. -}
isTrueAt' :: Ord state =>
           KD45model state -> state -> Form' state -> Bool
isTrueAt' m w Top' = True
isTrueAt' m w (Info' x) = w == x
isTrueAt' m@(MoKD45 worlds ags val acc points) w (Prp' p) =
  let props = apply val w
  in elem p props
isTrueAt' m w (Ng' f) = not (isTrueAt' m w f)
isTrueAt' m w (Conj' fs) = and (map (isTrueAt' m w) fs)
isTrueAt' m w (Disj' fs) = or  (map (isTrueAt' m w) fs)
isTrueAt' m@(MoKD45 worlds ags val acc points) w (Box' ag f) =
  let r = relKD45 ag m ; b = blKD45 r w
  in and (map (flip (isTrueAt' m) f) (fst b))
isTrueAt' m w (Statement' f g) =
  let m_update = upd_public_statement m f
  in isTrueAt' m_update w g
isTrueAt' m w (Announcement' f g) =
  (isTrueAt' m w f) ==> isTrueAt' m w (Statement' f g)
isTrueAt' m w (Lie' f g) =
  not(isTrueAt' m w f) ==> isTrueAt' m w (Statement' f g)
isTrueAt' m w (Recovery' f g) =
  let m_update1 = upd_recovery_dynamic m f
  in (isTrueAt' m_update1 w g)

{- | Function to update KD45-models with both public lies and truthfull
public statements. -}
upd_public_statement :: Ord state =>
            KD45model state -> Form' state -> KD45model state
upd_public_statement m@(MoKD45 states agents val rels actual) f =
  (MoKD45 states agents val rels' actual)
  where
  rels' = [(ag, [(ins',outs')] ) | (ag, [(ins, outs)]) <- rels,
           let condition = any (\v -> isTrueAt' m v f) ins,
           let ins2outs = [s | s <- ins, not(isTrueAt' m s f)],
           let (ins',outs') = if condition
                                then ([s | s <- ins, isTrueAt' m s f],
                                       merge outs ins2outs)
                                else (ins,outs)
          ]


{- | Opening up the mind again after being lied to. -}
upd_recovery_dynamic :: Ord state =>
              KD45model state -> Form' state -> KD45model state
upd_recovery_dynamic m@(MoKD45 states agents val rels actual) g =
  (MoKD45 states agents val rels' actual)
  where
  rels'   = [(ag, [(ins',outs')] ) | (ag, [(ins, outs)]) <- rels,
              let ins' = merge ins [s | s <- outs, isTrueAt' m s g],
              let outs' = [s | s <- outs, not(isTrueAt' m s g)]
            ]
