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

example {i j : ℕ} :
    ((i + 1).centralBinom : ℚ)
      * j.centralBinom * (i - j + 1) / (2 * (i + j + 1) * (i + j + 2))
    - i.centralBinom * (j + 1).centralBinom
      * (i - j - 1) / (2 * (i + j + 1) * (i + j + 2))
    = i.centralBinom / (i + 1) * (j.centralBinom / (j + 1)) := by
  have h₁ := i.succ_mul_centralBinom_succ
  have h₂ := j.succ_mul_centralBinom_succ
  qify at h₁ h₂
  field_simp
  linear_combination
    (1 / 4 * ↑i * ↑j * ↑(Nat.centralBinom (j + 1)) - 1 / 4 * ↑j ^ 2 * ↑(Nat.centralBinom (j + 1)) +
                  1 / 2 * ↑(Nat.centralBinom j) * ↑i +
                1 / 4 * ↑i * ↑(Nat.centralBinom (j + 1)) -
              1 / 8 * ↑j * ↑(Nat.centralBinom (j + 1)) +
            3 / 4 * ↑(Nat.centralBinom j) +
          1 / 8 * ↑(Nat.centralBinom (j + 1))) *
        h₁ +
      (-(1 / 4 * ↑(Nat.centralBinom (i + 1)) * ↑i ^ 2) +
                      1 / 4 * ↑(Nat.centralBinom (i + 1)) * ↑i * ↑j -
                    3 / 8 * ↑(Nat.centralBinom (i + 1)) * ↑i +
                  1 / 4 * ↑(Nat.centralBinom (i + 1)) * ↑j +
                ↑i * ↑(Nat.centralBinom i) +
              1 / 2 * ↑j * ↑(Nat.centralBinom i) -
            1 / 8 * ↑(Nat.centralBinom (i + 1)) +
          5 / 4 * ↑(Nat.centralBinom i)) *
        h₂
