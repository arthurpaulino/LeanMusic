/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import LeanMusic.Draft2.Utils

abbrev IntervalsSeq := List Int

namespace IntervalsSeq

-- def tail (s : IntervalsSeq) : IntervalsSeq :=
--   s.tailD []

@[simp] def notLeZero : IntervalsSeq → Prop
  | h :: t => 0 < h ∧ notLeZero t
  | _      => True

@[simp] def delta : IntervalsSeq → Int
  | h :: t => h + delta t
  | _      => 0

-- def shiftedOf : IntervalsSeq → Interval → IntervalsSeq
--   | h::t, of => [h + of] ++ shiftedOf t of
--   | _,    _  => []

def invertedAt : IntervalsSeq → Int → IntervalsSeq
  | h :: (t : IntervalsSeq), a => t ++ [a - t.delta]
  | _,                       _ => []

theorem allPositiveTailOfAllPositive (h : Int) (t : IntervalsSeq)
    (hp : notLeZero (h :: t)) : h > 0 ∧ notLeZero t := by
  cases t with
    | nil      => simp [hp.1]
    | cons _ _ => exact hp

theorem nonNegativeDeltaOfAllPositive (s : IntervalsSeq) (hp : s.notLeZero) :
    s.delta ≥ 0 := by
  induction s with
    | nil         => simp
    | cons h t hi =>
      have hpt := allPositiveTailOfAllPositive h t hp
      exact Int.sumGeOfGtGe h (delta t) hpt.1 (hi hpt.2)

end IntervalsSeq

structure ScaleShape (n : Nat) where
  intervalsSeq : IntervalsSeq
  allPositive  : intervalsSeq.notLeZero           := by simp
  boundedDelta : intervalsSeq.delta < Int.ofNat n := by simp

variable (n : Nat) (s : IntervalsSeq)
  (hp : s.notLeZero           := by simp)
  (hd : s.delta < Int.ofNat n := by simp)

namespace ScaleShape

def new : ScaleShape n := ⟨s, hp, hd⟩

end ScaleShape

structure Scale (n : Nat) extends ScaleShape n where
  base : Int

namespace Scale

def new (base : Int) : Scale n := ⟨⟨s, hp, hd⟩, base⟩

end Scale
