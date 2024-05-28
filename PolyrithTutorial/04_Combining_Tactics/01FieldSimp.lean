/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith
import Mathlib.Data.Complex.Basic


example (a b : ℚ) (ha : a ≠ 0) (H : b = a ^ 2 + 3 * a) : b / a - a = 3 := by
  field_simp
  linear_combination H


example (t : ℝ) : ((t ^ 2 - 1) / (t ^ 2 + 1)) ^ 2 + (2 * t  / (t ^ 2 + 1)) ^ 2 = 1 := by
  field_simp
  ring


example (m n : ℝ) (hmn : (m, n) ≠ 0) :
    ((m ^ 2 - n ^ 2) / (m ^ 2 + n ^ 2)) ^ 2 + (2 * m * n / (m ^ 2 + n ^ 2)) ^ 2 = 1 := by
  have : m ^ 2 + n ^ 2 ≠ 0 := by
    contrapose! hmn
    ext <;> dsimp <;> nlinarith
  field_simp
  ring


example {x : ℂ} (hx : x ^ 5 = 1) (hx' : x ≠ 1) : (x + 1 / x) ^ 2 + (x + 1 / x) - 1 = 0 := by
  have : x ≠ 0 := by
    intro h₀
    have : (1 : ℂ) = 0 := by polyrith
    norm_num at this
  field_simp
  rw [← sub_ne_zero] at hx'
  apply mul_left_cancel₀ hx'
  polyrith


noncomputable def f : ℝ → ℝ := fun x => (1 - x)⁻¹

example {x : ℝ} (h₁ : x ≠ 1) (h₀ : x ≠ 0) : f (f (f x)) = x := by
  dsimp [f]
  sorry
