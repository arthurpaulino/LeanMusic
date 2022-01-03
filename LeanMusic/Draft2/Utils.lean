/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

theorem And.trivialRight (h : a) : a ∧ True := by
  simp only [and_true]
  exact h

theorem Int.zeroLtSubOfLt (a b : Int) (h : a < b) : 0 < b - a := sorry

theorem Int.what (a b c : Int) (h : 0 < c) : a + (b - (c + a) + 0) < b := sorry
