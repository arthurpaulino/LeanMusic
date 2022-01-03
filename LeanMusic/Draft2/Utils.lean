/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

theorem Int.sumGeOfGtGe (a b : Int) (ha : 0 < a) (hb : 0 ≤ b) :
    a + b ≥ 0 := sorry

theorem Int.zeroLtSubOfLt (a b : Int) (h : a < b) : 0 < b - a := sorry

theorem Int.ltOfZeroLtAndSumLt (a b c : Int) (ha : 0 < a) (h : a + b < c) :
    b < c := sorry

@[simp] theorem List.eqOfAppendEmpty (l : List α) :
    List.append l [] = l := sorry
