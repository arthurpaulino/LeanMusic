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
  intervals    : Intervals
  properLength : intervals.length < 12 := by simp
  grows        : intervals.grows := by simp
  properRange  : intervals.maxRelativeInterval grows ≤ 12 := by simp

structure Scale where
  base  : Note
  shape : ScaleShape

def Scale.toNotes (s : Scale) : List Note :=
  s.shape.intervals.toNotes s.base

@[simp] def emptyNotes : List Note := []

theorem Scale.toNotesNotEmpty (s : Scale) : s.toNotes ≠ emptyNotes :=
  by simp [Intervals.toNotes, toNotes]
