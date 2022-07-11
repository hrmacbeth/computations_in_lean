/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import data.complex.basic
import tactic.polyrith

example {x y : ℤ} (h₁ : 2 * x + y = 4) (h₂ : x + y = 1) : x = 3 :=
by linear_combination h₁ - h₂

example {r s : ℝ} (h₁ : r + 2 * s = -1) (h₂ : s = 3) : r = -7 :=
by linear_combination h₁ - 2 * h₂

example {c : ℚ} (h₁ : 4 * c + 1 = 3 * c - 2) : c = -3 :=
by linear_combination h₁

example {x y : ℤ} (h₁ : x - 3 * y = 5) (h₂ : y = 3) : x = 14 :=
by linear_combination h₁ + 3 * h₂

example {x y : ℤ} (h₁ : 2 * x - y = 4) (h₂ : y - x + 1 = 2) : x = 5 :=
by linear_combination h₁ + h₂

example {x y : ℝ} (h₁ : x = 3) (h₂ : y = 4 * x - 3) : y = 9 :=
by linear_combination 4 * h₁ + h₂

example {a b c : ℝ} (h₁ : a + 2 * b + 3 * c = 7) (h₂ : b + 2 * c = 3) (h₃ : c = 1) :
  a = 2 :=
by linear_combination h₁ - 2 * h₂ + h₃

example {a b : ℝ} (h₁ : a + 2 * b = 4) (h₂ : a - b = 1) : a = 2 :=
by linear_combination 1 / 3 * h₁ + 2 / 3 * h₂

example {u v : ℚ} (h₁ : u + 2 * v = 4) (h₂ : u - 2 * v = 6) : u = 5 :=
by linear_combination 1 / 2 * h₁ + 1 / 2 * h₂

example {u v : ℚ} (h₁ : 4 * u + v = 3) (h₂ : v = 2) : u = 1 / 4 :=
by linear_combination 1 / 4 * h₁ - 1 / 4 * h₂
