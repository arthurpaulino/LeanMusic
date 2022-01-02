/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import LeanMusic.Draft1.Utils

/-- Semi-*int*ervals are represented with the type `Int` (happy coincidence). -/
abbrev Intervals := List Int

namespace Intervals

def tail (l : Intervals) : Intervals :=
  l.tailD []

-- Characterizations

@[simp] def ascending : Intervals → Prop
  | h::h'::t => h < h' ∧ ascending (h'::t)
  | _        => True

@[simp] def startsPositive : Intervals → Prop
  | h::_ => h > 0
  | _    => True

@[simp] def max (l : Intervals) (ha : l.ascending := by simp) : Int :=
  l.getLastD 0

def shiftedOf : Intervals → Int → Intervals
  | h::t, of => [h + of] ++ shiftedOf t of
  | _,    _  => []

def invertedAt : Intervals → Int → Intervals
  | h::(t : Intervals), a => (t ++ [a]).shiftedOf (-h)
  | _,                  _ => []

-- Proofs

theorem sameLengthOfShifted (l : Intervals) (of : Int) :
    l.length = (l.shiftedOf of).length := by
  induction l with
    | nil         => rfl
    | cons _ _ hi => simp [hi] rfl

theorem sameLengthOfInverted (l : Intervals) (a : Int) :
    l.length = (l.invertedAt a).length := by
  cases l with
    | nil      => rfl
    | cons h t => simp [invertedAt, ← sameLengthOfShifted]

theorem ascendingTailOfAscending (l : Intervals) (ha : l.ascending) :
    l.tail.ascending := by
  cases l with
    | cons _ t =>
      match t with
      | [] => simp
      | _::_ => simp only [tail, List.tailD, ha.2]
    | _ => simp

theorem ascendingOfShifted (l : Intervals) (ha : l.ascending) (of : Int) :
    (l.shiftedOf of).ascending := by
  induction l with
    | nil => simp
    | cons _ t hi =>
      match t with
        | [] => simp
        | th::tt =>
          simp [shiftedOf] at ha hi
          simp [List.append, Int.ltOfPlus ha.1, hi ha.2]

-- Known intervals

def minorTriadInterval : Intervals := [3, 7]
def majorTriadInterval : Intervals := [4, 7]

end Intervals
