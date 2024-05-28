/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Polyrith

example {a b c d e f : ℤ} (h₁ : a * d = b * c) (h₂ : c * f = d * e) (hd : d ≠ 0) :
    a * f = b * e := by
  apply mul_left_cancel₀ hd
  linear_combination f * h₁ + b * h₂

example {r s : ℚ} (hr : r ≠ 1) (h : r * s - 2 = s - 2 * r) : s = -2 := by
  rw [← sub_ne_zero] at hr
  apply mul_left_cancel₀ hr
  linear_combination h
