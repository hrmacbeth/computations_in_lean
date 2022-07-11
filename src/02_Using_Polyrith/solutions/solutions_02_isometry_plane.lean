/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: François Sunatori, Heather Macbeth
-/
import analysis.complex.basic
import tactic.polyrith

noncomputable theory

open complex
open_locale complex_conjugate

local notation `|` x `|` := complex.abs x

/-! This file contains a lot of computationally-intensive evaluation of operations on the complex
numbers. We speed it up slightly by specifiying in advance the path the simplifier should take.
-/

mk_simp_attribute complex_simps "simp-lemmas for polynomials"

attribute [complex_simps]
  norm_sq_eq_conj_mul_self norm_eq_abs of_real_pow of_real_one map_sub map_one

example {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) : f I = I ∨ f I = - I :=
begin
  have key : (f I - I) * (conj (f I) - conj (- I)) = 0,
  { have H₁ := congr_arg (λ t, (↑(t ^ 2) : ℂ)) (f.norm_map (I - 1)),
    have H₂ := congr_arg (λ t, (↑(t ^ 2) : ℂ)) (f.norm_map I),
    simp only [h, ←norm_sq_eq_abs] with complex_simps at H₁ H₂,
    have h₂ : conj (-I) = I := by norm_num,
    linear_combination I * H₁ - (-1 + I) * H₂ - (f I - I) * h₂ },
  -- From `key`, we deduce that either `f I - I = 0` or `conj (f I) - conj (- I) = 0`.
  cases eq_zero_or_eq_zero_of_mul_eq_zero key with hI hI,
  { left,
    linear_combination hI },
  { right,
    apply (conj : ℂ →+* ℂ).injective,
    linear_combination hI },
end
