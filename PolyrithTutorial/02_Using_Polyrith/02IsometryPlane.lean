/-
Copyright (c) 2021 François Sunatori. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: François Sunatori, Heather Macbeth
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Polyrith

attribute [-simp] mul_eq_zero

noncomputable section

open Complex

open scoped ComplexConjugate

/-! Delaborator for complex conjugation -- to be added to Mathlib. -/
open Lean PrettyPrinter Delaborator SubExpr in
@[delab app.DFunLike.coe]
def conjDelab : Delab := do
  let f ← withNaryArg 4 delab
  let Syntax.node _ _ #[starRingEndSyntax, cplxSyntax₁] := (f : Syntax) | failure
  let Syntax.ident _ _ ``starRingEnd _ := starRingEndSyntax | failure
  let Syntax.node _ _ #[cplxSyntax₂] := cplxSyntax₁ | failure
  let Syntax.node _ _ #[cplxSyntax₃] := cplxSyntax₂ | failure
  let Syntax.atom _ "ℂ" := cplxSyntax₃ | failure
  let z ← withNaryArg 5 delab
  `(conj $z)

example {f : ℂ →ₗᵢ[ℝ] ℂ} (h : f 1 = 1) : f I = I ∨ f I = -I := by
  have key : (f I - I) * (conj (f I) - conj (-I)) = 0 := by
    have conj_fact : ∀ z, f z * conj (f z) = z * conj z := by simp [mul_conj']
    have H₀ := conj_fact I
    have H₁ := conj_fact (I - 1)
    simp [h] at *
    -- state some fact(s) about `ℂ` here so that `polyrith` can use them in the computation
    -- when you have done this, `polyrith` will work
    polyrith
  -- From `key`, we deduce that either `f I - I = 0` or `conj (f I) - conj (- I) = 0`.
  rw [mul_eq_zero] at key
  obtain hI | hI := key
  · left
    linear_combination hI
  · right
    apply (conj : ℂ →+* ℂ).injective
    linear_combination hI

