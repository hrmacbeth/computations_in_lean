/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth
-/
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic.Polyrith

open Polynomial

/-- The Chebyshev polynomials, defined recursively. -/
noncomputable def T : ℕ → ℤ[X]
  | 0 => 1
  | 1 => X
  | n + 2 => 2 * X * T (n + 1) - T n

-- now record the three pieces of the recursive definition for easy access
theorem T_zero : T 0 = 1 := rfl

theorem T_one : T 1 = X := rfl

theorem T_add_two (n : ℕ) : T (n + 2) = 2 * X * T (n + 1) - T n := by rw [T]

/-- The product of two Chebyshev polynomials is the sum of two other Chebyshev polynomials. -/
theorem mul_T : ∀ m : ℕ, ∀ k, 2 * T m * T (m + k) = T (2 * m + k) + T k
  | 0 => by
    intro k
    ring_nf
    have h := T_zero
    linear_combination 2 * T k * h
  | 1 => by
    intro k
    have h₁ := T_add_two k
    have h₂ := T_one
    ring_nf at h₁ h₂ ⊢
    linear_combination 2 * T (1 + k) * h₂ - 1 * h₁
  | m + 2 => by
    intro k
    have H₁ := mul_T (m + 1) (k + 1)
    have H₂ := mul_T m (k + 2)
    have h₁ := T_add_two m
    have h₂ := T_add_two (2 * m + k + 2)
    have h₃ := T_add_two k
    ring_nf at H₁ H₂ h₁ h₂ h₃ ⊢
    linear_combination 2 * X * H₁ - 1 * H₂ + 2 * T (2 + m + k) * h₁ - 1 * h₂ - 1 * h₃
