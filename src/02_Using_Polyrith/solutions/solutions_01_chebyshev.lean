/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth
-/
import data.polynomial.basic
import tactic.polyrith

open polynomial
open_locale polynomial

/-- The Chebyshev polynomials, defined recursively.-/
noncomputable def T : ℕ → ℤ[X]
| 0       := 1
| 1       := X
| (n + 2) := 2 * X * T (n + 1) - T n

-- now record the three pieces of the recursive definition for easy access
lemma T_zero : T 0 = 1 := rfl
lemma T_one : T 1 = X := rfl
lemma T_add_two (n : ℕ) : T (n + 2) = 2 * X * T (n + 1) - T n := by rw T

/-- The product of two Chebyshev polynomials is the sum of two other Chebyshev polynomials. -/
lemma mul_T : ∀ m : ℕ, ∀ k, 2 * T m * T (m + k) = T (2 * m + k) + T k
| 0 := begin
    intros k,
    ring_nf,
    linear_combination 2 * T k * T_zero
  end
| 1 := begin
    intros k,
    have H := T_add_two k,
    ring_nf at ⊢ H,
    linear_combination - H + 2 * T (k + 1) * T_one,
  end
| (m + 2) := begin
    intros k,
    have H₁ := mul_T (m + 1) (k + 1),
    have H₂ := mul_T m (k + 2),
    have h₁ := T_add_two m,
    have h₂ := T_add_two (2 * m + k + 2),
    have h₃ := T_add_two k,
    ring_nf at H₁ H₂ h₁ h₂ h₃ ⊢,
    linear_combination 2 * T (k + (m + 2)) * h₁ + 2 * X * H₁ - H₂ - h₂ - h₃,
  end

