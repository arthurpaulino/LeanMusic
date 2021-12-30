/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import LeanMusic.Notes

/-- Semi-*int*ervals are represented with the type `Int` (happy coincidence). -/
abbrev Intervals := List Int

def Intervals.grows : Intervals → Prop
  | h::h'::t => h < h' ∧ grows t
  | _        => True

def Intervals.maxRelativeInterval (l : Intervals) (h : l.grows := by simp) : Int :=
  l.getLastD 0 - l.headD 0

def Intervals.shiftOf (l : Intervals) (of : Int) : Intervals :=
  l.map fun i => i + of

def Intervals.invertAt : Intervals → Int → Intervals
  | h::t, a => t ++ [a - h]
  | _, _    => []

def Intervals.invertAtN : Intervals → Int → Nat → Intervals
  | l, _, Nat.zero    => l
  | l, a, Nat.succ n' => l.invertAtN a n'

theorem Intervals.sameLengthOfShifted (l : Intervals) :
    ∀ (of : Int), l.length = (l.shiftOf of).length :=
  fun _ => by induction l with
    | nil         => rfl
    | cons _ _ hi => simp [List.length, hi] rfl

theorem Intervals.sameLengthOfInverted (l : Intervals) :
    ∀ (a : Int), l.length = (l.invertAt a).length :=
  fun _ => by cases l with
    | nil      => rfl
    | cons h t => simp [invertAt]

theorem Intervals.sameLengthOfInvertedN (l : Intervals) :
    ∀ (n : Nat), (∀ (a : Int), l.length = (l.invertAtN a n).length) := sorry

-- TODO
-- prove correctness of `Intervals.grow` (and consequently of `Intervals.maxRelativeInterval`)
-- prove that shifting doesn't change the result of `Intervals.maxRelativeInterval`
-- prove that inverting keeps the result of `Intervals.maxRelativeInterval` bounded
-- prove that if l grows then l shifted grows too
-- prove that if l grows then l inverted grows too as long as `of` is big enough

def Note.intervalUntilNote (n n' : Note) : Int :=
  n'.val - n.val

def Note.intervalFromNote (n n' : Note) : Int :=
  - n.intervalUntilNote n'

def Note.plusInterval (n : Note) (i : Int) : Note :=
  ⟨n.val + i⟩

def Note.plusOctave (n : Note) : Note :=
  n.plusInterval 12

def Note.minusOctave (n : Note) : Note :=
  n.plusInterval (-12)

def Intervals.OfNotes (head : Note) (tail : List Note) : Intervals :=
  tail.map fun n => n.intervalFromNote head

def Intervals.toNotes (l : Intervals) (head : Note) : List Note :=
  [head] ++ (l.map fun i => head.plusInterval i)

def minorTriadInterval : Intervals := [3, 7]
def majorTriadInterval : Intervals := [4, 7]

def isMinorTriad (l : Intervals) : Prop := sorry