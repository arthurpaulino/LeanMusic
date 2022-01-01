/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

theorem Int.ltOfPlus {a b c : Int} (h : a < b) : a + c < b + c := sorry

@[simp] theorem Int.leOfAny {a : Int} : a ≤ a := sorry

@[simp] theorem List.containsHeadOfNonEmpty [BEq α] :
    (h::t : List α).contains h = true := sorry

theorem List.eqOfSingletonContains [BEq α] :
    ([h] : List α).contains h' → h = h' := sorry

theorem List.nonEmptyOfHeadAndTail : (h::t : List α) ≠ [] := by simp

theorem List.isEmptyIff {l : List α} : l.isEmpty ↔ l = [] := by
  cases l with | _ => simp [isEmpty]
