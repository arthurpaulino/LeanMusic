/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

/-- Notes can't be simple integers because operations between notes aren't trivially typed. -/
structure Note where
  val : Int := 0 -- standard C
  deriving DecidableEq

namespace Note

def lt (n n' : Note) : Prop := n.val < n'.val
def le (n n' : Note) : Prop := n.val ≤ n'.val

instance : LT Note := ⟨lt⟩
instance : LE Note := ⟨le⟩

def decLt (n n' : Note) : Decidable (n < n') :=
  match n, n' with
  | ⟨p⟩, ⟨p'⟩ => inferInstanceAs (Decidable (p < p'))

def decLe (n n' : Note) : Decidable (n ≤ n') :=
  match n, n' with
  | ⟨p⟩, ⟨p'⟩ => inferInstanceAs (Decidable (p ≤ p'))

instance (n n' : Note) : Decidable (n < n') := decLt n n'
instance (n n' : Note) : Decidable (n ≤ n') := decLe n n'

def intervalUntilNote (n n' : Note) : Int :=
  n'.val - n.val

def intervalFromNote (n n' : Note) : Int :=
  - n.intervalUntilNote n'

def plusInterval (n : Note) (i : Int) : Note :=
  ⟨n.val + i⟩

def plusOctave (n : Note) : Note :=
  n.plusInterval 12

def minusOctave (n : Note) : Note :=
  n.plusInterval (-12)

end Note

abbrev Notes := List Note

namespace Notes

@[simp] def emptyNotes : Notes := []

-- Transformations

def shiftedOf : Notes → Int → Notes
  | h::t, of => [⟨h.val + of⟩] ++ shiftedOf t of
  | _,    _  => []

def invertedAt : Notes → Note → Notes
  | h::t, a => t ++ [⟨a.val + h.val⟩]
  | _, _    => []

def invertedAtN : Notes → Note → Nat → Notes
  | l, _, Nat.zero    => l
  | l, a, Nat.succ n' => (l.invertedAt a).invertedAtN a n'

-- Comparisons

def isEquiv (l l' : Notes) : Prop :=
  ∃ (of : Int), l.shiftedOf of = l'

def isEquivIfInverted (l l' : Notes) (a : Note) : Prop :=
  l.isEquiv l' ∧ ∃ (n : Nat), l.invertedAtN a n = l'

-- Proofs

theorem sameLengthOfShifted (l : Notes) (of : Int) :
    l.length = (l.shiftedOf of).length := by
  induction l with
    | nil         => rfl
    | cons _ _ hi => simp [hi] rfl

theorem sameLengthOfInverted (l : Notes) (n : Note) :
    l.length = (l.invertedAt n).length := by
  cases l with
    | nil      => rfl
    | cons _ _ => simp [invertedAt]

theorem shiftOfHeadAndTail (h : Note) (of : Int) (t : Notes) :
    shiftedOf (h::t) of = (⟨h.val + of⟩)::(shiftedOf t of) := rfl

end Notes
