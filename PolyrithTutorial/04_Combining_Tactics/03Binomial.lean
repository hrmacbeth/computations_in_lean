/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Julian Kuelshammer, Heather Macbeth
-/
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Polyrith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Qify


#check @Nat.centralBinom
-- Nat.centralBinom : ℕ → ℕ

#check Nat.succ_mul_centralBinom_succ


example {i j : ℕ} :
    ((i + 1).centralBinom : ℚ)
      * j.centralBinom * (i - j + 1) / (2 * (i + j + 1) * (i + j + 2))
    - i.centralBinom * (j + 1).centralBinom
      * (i - j - 1) / (2 * (i + j + 1) * (i + j + 2))
    = i.centralBinom / (i + 1) * (j.centralBinom / (j + 1)) := by
  have h₁ := i.succ_mul_centralBinom_succ
  have h₂ := j.succ_mul_centralBinom_succ
  sorry
