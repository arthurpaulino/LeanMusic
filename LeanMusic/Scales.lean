/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

import LeanMusic.Intervals
import LeanMusic.Notes

/--
A scale shape is a list of intervals such that:
* There can't be more than 11 intervals in it
* The intervals must be in ascending order
* The maximal range of its relative intervals can't be greater than an octave
-/
structure ScaleShape where
  intervals      : Intervals
  startsPositive : intervals.startsPositive := by simp
  ascending      : intervals.ascending := by simp
  properMax      : intervals.max ascending < 12 := by simp

structure Scale where
  base  : Int
  shape : ScaleShape
