/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Polyrith


example {x : ℤ} (hx : x ^ 2 - 4 * x = -4) : x = 2 := by
  have H : (x - 2) ^ 2 = 0 := by linear_combination hx
  apply pow_eq_zero at H
  linear_combination H


-- hover over the `(exp := 2)` to get a useful explanation in a pop-up
example {x : ℚ} (hx : x ^ 2 - 4 * x = - 4) : x = 2 := by linear_combination (exp := 2) hx


example {x : ℚ} (hx : x ^ 2 - 4 * x = - 4) : x = 2 := by polyrith
-- produces `linear_combination (exp := 2) hx`


example {a b : ℝ} (h₁ : a ^ 2 = 2 * b ^ 2) (h₂ : b ^ 2 = 2 * a ^ 2) : a = 0 := by
  polyrith

example {x y z : ℚ} (h₁ : x = y) (h₂ : x * y = 0) : x + y * z = 0 := by
  polyrith


example {z : ℂ} (h₁ : z ^ 3 = 1) (h₂ : z ≠ 1) : z ^ 2 + z + 1 = 0 := by
  rw [← sub_ne_zero] at h₂
  apply mul_left_cancel₀ h₂
  polyrith


example {a b c d e f : ℤ} (h₁ : a * d = b * c) (h₂ : c * f = d * e) (hd : d ≠ 0) :
    a * f = b * e := by
  sorry

example {r s : ℚ} (hr : r ≠ 1) (h : r * s - 2 = s - 2 * r) : s = -2 := by
  sorry
