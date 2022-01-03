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
  | h :: (t : IntervalsSeq), a => t ++ [a - delta (h :: t)]
  | _,                       _ => []

theorem posIffAppendPos (s s' : IntervalsSeq) :
    (s ++ s').allPositive ↔ s.allPositive ∧ s'.allPositive := sorry

theorem deltaSumEqSumDeltas (s s' : IntervalsSeq) :
    delta (s ++ s') = delta s + delta s' := sorry

theorem posInvOfPosAndBound (s : IntervalsSeq) (i : Int)
    (hp : s.allPositive) (hb : s.delta < i) :
      (s.invertedAt i).allPositive := by
  cases s with
    | nil      => simp
    | cons h t =>
      let iSubDelta := [(i - (h + delta t))]
      have hpid : allPositive iSubDelta := by
        exact And.trivialRight (Int.zeroLtSubOfLt (h + delta t) i hb)
      simp only [invertedAt, posIffAppendPos]
      exact And.intro hp.2 hpid

theorem boundInvOfPosAndBound (s : IntervalsSeq) (i : Int)
    (hp : s.allPositive) (hb : s.delta < i) :
      (s.invertedAt i).delta < i := by
  cases s with
    | nil => exact hb
    | cons h t =>
      simp only [invertedAt, deltaSumEqSumDeltas]
      exact Int.what (delta t) i h hp.1

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
