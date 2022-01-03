/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import LeanMusic.Intervals

structure ScaleShape where
  n            : Nat
  intervals    : Intervals
  allPositive  : intervals.allPositive         := by simp
  boundedDelta : intervals.delta < Int.ofNat n := by simp

variable (n : Nat) (l : Intervals)
  (hp : l.allPositive         := by simp)
  (hd : l.delta < Int.ofNat n := by simp)

namespace ScaleShape

def invert (ss : ScaleShape) : ScaleShape :=
  let s := ss.intervals
  let i := Int.ofNat ss.n
  ⟨ss.n, s.invertedAt i,
    s.posInvOfPosAndBound i ss.allPositive ss.boundedDelta,
    s.boundInvOfPosAndBound i ss.allPositive ss.boundedDelta⟩

def invertN : ScaleShape → Nat → ScaleShape
  | ss, Nat.zero    => ss
  | ss, Nat.succ n' => invertN ss.invert n'

def auto : ScaleShape := ⟨n, l, hp, hd⟩

def toString (ss : ScaleShape) : String :=
  s!"⟪{ss.n}⟫{ss.intervals}"

instance : ToString ScaleShape where
  toString ss := ss.toString

end ScaleShape

structure Scale where
  base : Int
  shape : ScaleShape

namespace Scale

def invert (s : Scale) : Scale :=
  ⟨s.base + s.shape.intervals.headD 0, s.shape.invert⟩

def invertN : Scale → Nat → Scale
  | s, Nat.zero    => s
  | s, Nat.succ n' => invertN s.invert n'

def shift (s : Scale) (i : Int) : Scale :=
  ⟨s.base + i, s.shape⟩

def notes (s : Scale) : List Int := Id.run do
  let mut otherNotes : List Int := []
  let mut sum : Int := 0
  for i in s.shape.intervals do
    sum := sum + i
    otherNotes := otherNotes.concat (s.base + sum)
  [s.base] ++ otherNotes

def toString (s : Scale) : String :=
  s!"⟪{s.shape.n}⟫{s.notes}"

instance : ToString Scale where
  toString s := s.toString

def toString' (s : Scale) (m : Int → String) : String :=
  s!"⟪{s.shape.n}⟫{s.notes.map m}"

end Scale
