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

def max (l : Intervals) (ha : l.ascending := by simp) : Int :=
  l.getLastD 0

-- Proofs

theorem ascendingTailOfAscending (l : Intervals) (ha : l.ascending) :
    l.tail.ascending := by
  induction l with
  | nil => simp [ascending]
  | cons h t hi => sorry

-- Intervals ↔ Notes 

def toNotes (l : Intervals) (head : Note) : Notes :=
  [head] ++ (l.map fun i => head.plusInterval i)

def ofNotes (head : Note) (tail : Notes) : Intervals :=
  tail.map fun n => n.intervalFromNote head

def minorTriadInterval : Intervals := [3, 7]
def majorTriadInterval : Intervals := [4, 7]

end Intervals
