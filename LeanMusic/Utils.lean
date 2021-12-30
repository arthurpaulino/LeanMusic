/-
  Copyright (c) 2021 Arthur Paulino. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Arthur Paulino
-/

theorem List.isEmptyIff {l : List α} : l.isEmpty ↔ l = [] := by
  cases l with
  | nil      => simp [isEmpty]
  | cons _ _ => simp [isEmpty]
