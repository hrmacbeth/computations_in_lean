/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith
import Mathlib.Data.Complex.Basic

noncomputable def f : ℝ → ℝ := fun x => (1 - x)⁻¹

example {x : ℝ} (h₁ : x ≠ 1) (h₀ : x ≠ 0) : f (f (f x)) = x := by
  dsimp [f]
  have : 1 - x ≠ 0 := by contrapose! h₁; linear_combination -h₁
  have : -x ≠ 0 := by contrapose! h₀; linear_combination -h₀
  have : -x - (1 - x) ≠ 0 := by intro h; linarith
  field_simp
  ring
