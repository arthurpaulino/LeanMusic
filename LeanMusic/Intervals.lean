/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import LeanMusic.Notes

/-- Semi-*int*ervals are represented with the type `Int` (happy coincidence). -/
abbrev Intervals := List Int

namespace Intervals

def tail (l : Intervals) : Intervals :=
  l.tailD []

-- Characterizations

def ascending : Intervals → Prop
  | h::h'::t => h < h' ∧ ascending t
  | _        => True

def startsPositive : Intervals → Prop
  | h::_ => h > 0
  | _    => True

def max (l : Intervals) (h : l.ascending := by simp) : Int :=
  l.getLastD 0

-- Transformations

def shiftOf : Intervals → Int → Intervals
  | h::t, of => [h + of] ++ shiftOf t of
  | _,    _  => []

def invertAt : Intervals → Int → Intervals
  | h::t, a => t ++ [a - h]
  | _, _    => []

def invertAtN : Intervals → Int → Nat → Intervals
  | l, _, Nat.zero    => l
  | l, a, Nat.succ n' => (l.invertAt a).invertAtN a n'

-- Comparisons

def isEquiv (l l' : Intervals) : Prop :=
  ∃ (of : Int), l.shiftOf of = l'

def isEquivIfInverted (l l' : Intervals) (a : Int) : Prop :=
  l.isEquiv l' ∧ ∃ (n : Nat), l.invertAtN a n = l'

-- Proofs

theorem sameLengthOfShifted (l : Intervals) (of : Int) :
    l.length = (l.shiftOf of).length := by
  induction l with
    | nil         => rfl
    | cons _ _ hi => simp [List.length, hi] rfl

theorem sameLengthOfInverted (l : Intervals) (a : Int) :
    l.length = (l.invertAt a).length := by
  cases l with
    | nil      => rfl
    | cons _ _ => simp [invertAt]

theorem ascendingTailOfAscending (l : Intervals) (ha : l.ascending) :
    l.tail.ascending := by
  induction l with
  | nil => simp [ascending]
  | cons h t hi => sorry

theorem shiftOfHeadAndTail (h of : Int) (t : Intervals) :
    shiftOf (h::t) of = (h + of)::(shiftOf t of) :=
  by simp [shiftOf]

theorem ascendingOfShiftedAux (l : Intervals) (of h : Int)
    (ha : ascending (l.shiftOf of)) : ascending ((h + of)::(l.shiftOf of)) := by
  induction l with
  | nil => simp [ascending]
  | cons h t hi => sorry

theorem ascendingOfShifted (l : Intervals) (ha : l.ascending) (of : Int) :
    (l.shiftOf of).ascending := by
  induction l with
    | nil => simp [ascending]
    | cons h t hi =>
      exact ascendingOfShiftedAux t of h $
        hi (ascendingTailOfAscending (h::t) ha)

def ofNotes (head : Note) (tail : List Note) : Intervals :=
  tail.map fun n => n.intervalFromNote head

def toNotes (l : Intervals) (head : Note) : List Note :=
  [head] ++ (l.map fun i => head.plusInterval i)

end Intervals

def minorTriadInterval : Intervals := [3, 7]
def majorTriadInterval : Intervals := [4, 7]

def isMinorTriad (l : Intervals) : Prop := sorry