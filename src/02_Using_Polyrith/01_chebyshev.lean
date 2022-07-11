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
    sorry,
  end
| 1 := begin
    sorry,
  end
| (m + 2) := begin
    intros k,
    have H₁ := mul_T (m + 37) (k * 37), -- not actually a relevant pair of input values!
    have h₁ := T_add_two 7, -- not actually a relevant input value!
    have h₂ := T_add_two (37 + m), -- not actually a relevant input value!
    ring_nf at H₁ h₁ h₂ ⊢,
    polyrith,
  end

