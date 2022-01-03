/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import LeanMusic.Draft2.Utils

abbrev IntervalsSeq := List Int

namespace IntervalsSeq

@[simp] def allPositive : IntervalsSeq → Prop
  | h :: t => 0 < h ∧ allPositive t
  | _      => True

@[simp] def delta : IntervalsSeq → Int
  | h :: t => h + delta t
  | _      => 0

def invertedAt : IntervalsSeq → Int → IntervalsSeq
  | h :: (t : IntervalsSeq), a => t ++ [a - t.delta]
  | _,                       _ => []

theorem nonNegDeltaOfPos (s : IntervalsSeq) (hp : s.allPositive) :
    s.delta ≥ 0 := by
  induction s with
    | nil         => simp
    | cons h t hi =>
      exact Int.sumGeOfGtGe h (delta t) (hp.1) (hi hp.2)

theorem boundTailOfPosHeadAndBound (h i : Int) (t : IntervalsSeq)
    (hp : 0 < h) (hb : delta (h :: t) < i) : delta t < i := sorry

theorem posOfAppendPos (s s' : IntervalsSeq)
    (hps : s.allPositive) (hps' : s'.allPositive) :
    (s ++ s').allPositive := sorry

theorem posInvOfPosAndBound (s : IntervalsSeq) (i : Int)
    (hp : s.allPositive) (hb : s.delta < i) : (s.invertedAt i).allPositive := by
  cases s with
  | nil      => simp
  | cons h t =>
    have hbt := boundTailOfPosHeadAndBound h i t hp.1 hb
    have hpid : allPositive [(i - (delta t))] := by
      simp [Int.qq (delta t) i hbt]
    exact posOfAppendPos t [(i - (delta t))] hp.2 hpid

theorem boundInvOfPosAndBound (s : IntervalsSeq) (i : Int)
    (hp : s.allPositive) (hb : s.delta < i) : (s.invertedAt i).delta < i := sorry

end IntervalsSeq

structure ScaleShape (n : Nat) where
  intervalsSeq : IntervalsSeq
  allPositive  : intervalsSeq.allPositive         := by simp
  boundedDelta : intervalsSeq.delta < Int.ofNat n := by simp

variable (n : Nat) (s : IntervalsSeq)
  (hp : s.allPositive         := by simp)
  (hd : s.delta < Int.ofNat n := by simp)

namespace ScaleShape

def invert (ss : ScaleShape n) : ScaleShape n :=
  let s := ss.intervalsSeq
  let i := Int.ofNat n
  let invertedS := s.invertedAt i
  have hip : invertedS.allPositive := s.posInvOfPosAndBound i
    ss.allPositive ss.boundedDelta
  have hib : invertedS.delta < i := s.boundInvOfPosAndBound i
    ss.allPositive ss.boundedDelta
  ⟨invertedS,
    s.posInvOfPosAndBound i ss.allPositive ss.boundedDelta,
    s.boundInvOfPosAndBound i ss.allPositive ss.boundedDelta⟩

def new : ScaleShape n := ⟨s, hp, hd⟩

end ScaleShape

structure Scale (n : Nat) extends ScaleShape n where
  base : Int

namespace Scale

def new (base : Int) : Scale n := ⟨⟨s, hp, hd⟩, base⟩

end Scale
