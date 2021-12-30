/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

/-- Notes can't be simple integers because operations between notes aren't trivially typed. -/
structure Note where
  val : Int := 0 -- standard C
  deriving Inhabited, DecidableEq

def Note.lt (n n' : Note) : Prop := n.val < n'.val
def Note.le (n n' : Note) : Prop := n.val ≤ n'.val

instance : LT Note := ⟨Note.lt⟩
instance : LE Note := ⟨Note.le⟩

def Note.decLt (n n' : Note) : Decidable (n < n') :=
  match n, n' with
  | ⟨p⟩, ⟨p'⟩ => inferInstanceAs (Decidable (p < p'))

def Note.decLe (n n' : Note) : Decidable (n ≤ n') :=
  match n, n' with
  | ⟨p⟩, ⟨p'⟩ => inferInstanceAs (Decidable (p ≤ p'))

instance (n n' : Note) : Decidable (n < n') := Note.decLt n n'
instance (n n' : Note) : Decidable (n ≤ n') := Note.decLe n n'

def Note.min (n n' : Note) : Note :=
  if n ≤ n' then n else n'

def Note.max (n n' : Note) : Note :=
  if n ≤ n' then n' else n
