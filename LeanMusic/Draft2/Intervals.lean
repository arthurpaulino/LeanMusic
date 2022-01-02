/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

abbrev IntervalsSeq := List Int

namespace IntervalsSeq

@[simp] def tail (s : IntervalsSeq) : IntervalsSeq :=
  s.tailD []

@[simp] def allPositive : IntervalsSeq → Prop
  | h :: t => h > 0 ∧ allPositive t
  | _      => True

@[simp] def delta : IntervalsSeq → Int
  | h :: t => h + delta t
  | _      => 0

-- def shiftedOf : IntervalsSeq → Interval → IntervalsSeq
--   | h::t, of => [h + of] ++ shiftedOf t of
--   | _,    _  => []

def invertAt : IntervalsSeq → Int → IntervalsSeq
  | h :: (t : IntervalsSeq), a => t ++ [a - t.delta]
  | _,                       _ => []

theorem allPositiveTailOfAllPositive (s : IntervalsSeq)
    (hp : s.allPositive) : allPositive s.tail := sorry

theorem nonNegativeDeltaOfAllPositive (s : IntervalsSeq) (hp : s.allPositive) :
    s.delta ≥ 0 := by
  induction s with
    | nil => simp
    | cons h t hi => sorry

end IntervalsSeq

structure ChordShape (n : Nat) where
  intervalsSeq : IntervalsSeq
  allPositive  : intervalsSeq.allPositive := by simp

structure ScaleShape (n : Nat) extends ChordShape n where
  boundedDelta : intervalsSeq.delta < Int.ofNat n := by simp

structure Chord (n : Nat) extends ChordShape n where
  base : Int

structure Scale (n : Nat) extends ScaleShape n, Chord n

