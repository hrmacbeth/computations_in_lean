/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

example {x y : ℝ} (h₁ : x + 3 = 5) (h₂ : 2 * x - y * x = 0) : y = 2 := by
  linear_combination (-1 / 2 * y + 1) * h₁ - 1 / 2 * h₂

example {x y : ℝ} (h₁ : x - y = 4) (h₂ : x * y = 1) : (x + y) ^ 2 = 20 := by
  linear_combination (x - y + 4) * h₁ + 4 * h₂

example {a b c d e f : ℤ} (h₁ : a * d = b * c) (h₂ : c * f = d * e) :
    d * (a * f - b * e) = 0 := by
  linear_combination f * h₁ + b * h₂

example {u v : ℝ} (h₁ : u + 1 = v) : u ^ 2 + 3 * u + 1 = v ^ 2 + v - 1 := by
  linear_combination (u + v + 2) * h₁

example {z : ℝ} (h₁ : z ^ 2 + 1 = 0) : z ^ 4 + z ^ 3 + 2 * z ^ 2 + z + 3 = 2 := by
  linear_combination (z ^ 2 + z + 1) * h₁

example {p q r : ℚ} (h₁ : p + q + r = 0) (h₂ : p * q + p * r + q * r = 2) :
    p ^ 2 + q ^ 2 + r ^ 2 = -4 := by
  linear_combination (p + q + r) * h₁ - 2 * h₂
