/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

/-- Notes can't be simple integers because operations between notes aren't trivially typed. -/
structure Note where
  val : Int := 0 -- standard C
  deriving Inhabited, DecidableEq

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

@[simp] def emptyNotes : List Note := []

end Note
