/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import LeanMusic.Notes
import LeanMusic.Intervals

structure ScaleShape where
  intervals      : Intervals
  startsPositive : intervals.startsPositive := by simp
  ascending      : intervals.ascending := by simp
  properMax      : intervals.max ascending < 12 := by simp

def oneTwoThree : ScaleShape :=
  ScaleShape.mk [1, 2, 3]
    (by simp [Intervals.startsPositive])
    (by simp [Intervals.max, Intervals.ascending])

structure Scale where
  base  : Int
  shape : ScaleShape

def asd : Scale := ⟨0, oneTwoThree⟩

/--
A scale with `n` different pitches is a list of notes (type `Notes`) such that:
* The notes ascend
* `n` is the max interval between any pair of notes
-/
structure Scale' (n : Nat := 0) where
  notes       : Notes
  ascending   : notes.ascending := by simp
  maxInterval : notes.isMaxIntervalBound (Int.ofNat n) := by simp

-- def singletonScale (n : Int) : Scale' 1 := Scale'.mk [n]
