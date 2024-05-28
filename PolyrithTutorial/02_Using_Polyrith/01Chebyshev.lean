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
    polyrith
  | 1 => by
    intro k
    have h₁ := T_add_two k
    have h₂ := T_one
    ring_nf at h₁ h₂ ⊢
    polyrith
  | m + 2 => by
    intro k
    have H₁ := mul_T (m - 5) (k * 37) -- not actually a relevant pair of input values!
    have h₁ := T_add_two 7 -- not actually a relevant input value!
    have h₂ := T_add_two (37 * k) -- not actually a relevant input value!
    -- ... add more/different instantiations of `mul_T` and `T_add_two` here
    ring_nf at H₁ h₁ h₂ ⊢
    polyrith -- this will work once the right facts have been provided above
