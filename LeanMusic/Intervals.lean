/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import LeanMusic.Utils

abbrev Intervals := List Int

namespace Intervals

@[simp] def allPositive : Intervals → Prop
  | h :: t => 0 < h ∧ allPositive t
  | _      => True

@[simp] def delta : Intervals → Int
  | h :: t => h + delta t
  | _      => 0

def invertedAt : Intervals → Int → Intervals
  | h :: (t : Intervals), a => t ++ [a - delta (h :: t)]
  | _,                    _ => []

theorem appendPosOfPos (l l' : Intervals)
    (hpl : l.allPositive) (hpl' : l'.allPositive) :
      (l ++ l').allPositive := by
  induction l with
    | nil         => rw [List.nil_append]; exact hpl'
    | cons _ _ hi => exact ⟨hpl.1, hi hpl.2⟩

theorem deltaAppendEqSumDeltas (l l' : Intervals) :
    delta (l ++ l') = delta l + delta l' := by
  induction l with
    | nil         => simp [Int.ZeroAdd]
    | cons _ _ hi =>
      simp only [HAppend.hAppend, Append.append] at hi
      simp [hi, Int.AddAssoc]

theorem posInvOfPosAndBound (l : Intervals) (i : Int)
    (hp : l.allPositive) (hb : l.delta < i) :
      (l.invertedAt i).allPositive := by
  cases l with
    | nil      => simp
    | cons h t =>
      let iSubDelta := [(i - (h + delta t))]
      have hpid : allPositive iSubDelta := by
        exact ⟨Int.zeroLtSubOfLt (h + delta t) i hb, ⟨⟩⟩
      exact appendPosOfPos t iSubDelta hp.2 hpid

theorem boundInvOfPosAndBound (l : Intervals) (i : Int)
    (hp : l.allPositive) (hb : l.delta < i) :
      (l.invertedAt i).delta < i := by
  cases l with
    | nil => exact hb
    | cons h t =>
      simp only [invertedAt, deltaAppendEqSumDeltas]
      exact Int.what (delta t) i h hp.1

end Intervals
