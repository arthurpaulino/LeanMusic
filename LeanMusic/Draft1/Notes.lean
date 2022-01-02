/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import LeanMusic.Draft1.Utils

abbrev Notes := List Int

namespace Notes

-- Data extractions

def tail (l : Notes) : Notes :=
  l.tailD []

def first (l : Notes) (hne : l ≠ []) : Int :=
  l.head hne

def last (l : Notes) (he : l ≠ []) : Int :=
  l.getLast he

-- Transformations

def shiftedOf : Notes → Int → Notes
  | h :: t, i => [h + i] ++ shiftedOf t i
  | _,      _ => []

def invertedAt : Notes → Int → Notes
  | h :: t, a => t ++ [a + h]
  | _,      _ => []

def invertedAtTimes : Notes → Int → Nat → Notes
  | l, _, Nat.zero   => l
  | l, a, Nat.succ n => (l.invertedAt a).invertedAtTimes a n

-- Properties

def ascending : Notes → Prop
  | h :: h' :: t => h < h' ∧ ascending (h' :: t)
  | _            => True

def isHighest (l : Notes) (n : Int) : Prop :=
  l.contains n ∧ ∀ n', l.contains n' → n' ≤ n

def isLowest (l : Notes) (n : Int) : Prop :=
  l.contains n ∧ ∀ n', l.contains n' → n ≤ n'

def isMaxInterval (l : Notes) (i : Int) : Prop :=
  ∃ max min, i = max - min ∧ l.isHighest max ∧ l.isLowest min

def isMaxIntervalBound (l : Notes) (b : Int) : Prop :=
  ∀ i, l.isMaxInterval i → i ≤ b

-- Comparisons

def ofSameIntervals (l l' : Notes) : Prop :=
  ∃ i, l.shiftedOf i = l'

def ofSameIntervalsIfInvertedAt (l l' : Notes) (a : Int) : Prop :=
  l.ofSameIntervals l' ∧ ∃ n, l.invertedAtTimes a n = l'

-- Notes ↔ Intervals

def toIntervals : ∀ (l : Notes), l ≠ [] → List Int
  | [],             hne => absurd rfl hne
  | h :: (t : Notes), _ => t.shiftedOf (-h)

def ofIntervals : Int → List Int → Notes
  | h,          [] => [h]
  | h, (l : Notes) => l.shiftedOf h

-- Proofs

variable (l : Notes)

theorem sameLengthOfShifted (of : Int) :
    l.length = (l.shiftedOf of).length := by
  induction l with
    | nil         => rfl
    | cons _ _ hi => simp [hi] rfl

theorem sameLengthOfInverted (n : Int) :
    l.length = (l.invertedAt n).length := by
  cases l with
    | nil      => rfl
    | cons _ _ => simp [invertedAt]

theorem shiftOfHeadAndTail (h : Int) (of : Int) (t : Notes) :
    shiftedOf (h :: t) of = (h + of) :: (shiftedOf t of) := rfl

theorem ascendingTailOfAscending (ha : l.ascending) :
    l.tail.ascending := by
  cases l with
    | cons _ t =>
      match t with
      | []     => simp [ascending]
      | _ :: _ => simp only [tail, List.tailD, ha.2]
    | _ => simp [ascending]

theorem ascendingOfShifted (ha : l.ascending) (of : Int) :
    (l.shiftedOf of).ascending := by
  induction l with
    | nil         => simp [ascending]
    | cons _ t hi =>
      match t with
        | []       => simp [ascending]
        | th :: tt =>
          simp [shiftedOf] at ha hi
          simp [ascending, List.append, Int.ltOfPlus ha.1, hi ha.2]

theorem ascendingOfLtAndAscending {h h' : Int} {t : Notes}
    (ha : h' < h ∧ ascending (h :: t)) : ascending (h' :: t) := sorry

theorem firstIsLowestOfAscending (ha : l.ascending) (hne : l ≠ []) :
    l.isLowest (l.first hne) := by
  have hat := l.ascendingTailOfAscending ha
  cases l with
    | nil => contradiction
    | cons h t =>
      simp [first, List.head, isLowest]
      intro _ hn
      induction t with
        | nil => simp [List.eqOfSingletonContains hn]
        | cons h' t' hi =>
          exact hi (ascendingOfLtAndAscending ha)
            (List.nonEmptyOfHeadAndTail h t')
            (ascendingTailOfAscending (h' :: t') hat)
            (List.tailContainsOfNeqHead hn)

theorem lastIsHighestOfAscending (ha : l.ascending) (hne : l ≠ []) :
    l.isHighest (l.last hne) := sorry

theorem lastMinusFirstIsMaxIntervalOfAscending (ha : l.ascending) (hne : l ≠ []) :
    l.isMaxInterval (l.last hne - l.first hne) := by
  exact ⟨last l hne, first l hne, rfl,
    l.lastIsHighestOfAscending ha hne,
    l.firstIsLowestOfAscending ha hne⟩

@[simp] theorem emptyIsAcending : ascending [] := by simp [ascending]

@[simp] theorem singletonIsAcending : ascending [h] := by simp [ascending]

@[simp] theorem singletonZeroMaxInterval (h : Int) : isMaxInterval [h] 0 := by
  have qq : isHighest [h] h := sorry
  have ww : isLowest [h] h := sorry
  have ee : 0 = h - h := sorry
  exact ⟨h, h, ee, ⟨qq, ww⟩⟩

end Notes