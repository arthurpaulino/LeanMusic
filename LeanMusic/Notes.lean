/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import LeanMusic.Utils

abbrev Notes := List Int

namespace Notes

-- Transformations

def shiftedOf : Notes → Int → Notes
  | h::t, i => [h + i] ++ shiftedOf t i
  | _, _    => []

def invertedAt : Notes → Int → Notes
  | h::t, a => t ++ [a + h]
  | _, _    => []

def invertedAtTimes : Notes → Int → Nat → Notes
  | l, _, Nat.zero   => l
  | l, a, Nat.succ n => (l.invertedAt a).invertedAtTimes a n

-- Properties

def tail (l : Notes) : Notes :=
  l.tailD []

def ascending : Notes → Prop
  | h::h'::t => h < h' ∧ ascending (h'::t)
  | _        => True

-- Comparisons

def ofSameIntervals (l l' : Notes) : Prop :=
  ∃ (i : Int), l.shiftedOf i = l'

def ofSameIntervalsIfInvertedAt (l l' : Notes) (a : Int) : Prop :=
  l.ofSameIntervals l' ∧ ∃ (n : Nat), l.invertedAtTimes a n = l'

-- Notes ↔ Intervals

def toIntervals : ∀ (l : Notes), l ≠ [] → List Int
  | [],            hn => absurd rfl hn
  | h::(t : Notes), _ => t.shiftedOf (-h)

def ofIntervals : Int → List Int → Notes
  | h,          [] => [h]
  | h, (l : Notes) => l.shiftedOf (h)

-- Proofs

theorem sameLengthOfShifted (l : Notes) (of : Int) :
    l.length = (l.shiftedOf of).length := by
  induction l with
    | nil         => rfl
    | cons _ _ hi => simp [hi] rfl

theorem sameLengthOfInverted (l : Notes) (n : Int) :
    l.length = (l.invertedAt n).length := by
  cases l with
    | nil      => rfl
    | cons _ _ => simp [invertedAt]

theorem shiftOfHeadAndTail (h : Int) (of : Int) (t : Notes) :
    shiftedOf (h::t) of = (h + of)::(shiftedOf t of) := rfl

theorem ascendingTailOfAscending (l : Notes) (ha : l.ascending) :
    l.tail.ascending := by
  cases l with
    | cons _ t =>
      match t with
      | [] => simp [ascending]
      | _::_ => simp only [tail, List.tailD, ha.2]
    | _ => simp [ascending]

theorem ascendingOfShifted (l : Notes) (ha : l.ascending) (of : Int) :
    (l.shiftedOf of).ascending := by
  induction l with
    | nil => simp [ascending]
    | cons _ t hi =>
      match t with
        | [] => simp [ascending]
        | th::tt =>
          simp [shiftedOf] at ha hi
          simp [ascending, List.append, Int.ltOfPlus ha.1, hi ha.2]

end Notes
