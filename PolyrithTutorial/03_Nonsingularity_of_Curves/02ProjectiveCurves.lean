/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Polyrith

attribute [simp] Matrix.vecHead Matrix.vecTail
attribute [-simp] mul_eq_zero

noncomputable section

open MvPolynomial

variable (K : Type*) [Field K] [CharZero K]


section Klein

/-- Defining polynomial for the Klein quartic curve x³y + y³z + z³x = 0 as a projective
hypersurface in Kℙ². -/
abbrev klein : MvPolynomial (Fin 3) K :=
  X 0 ^ 3 * X 1 + X 1 ^ 3 * X 2 + X 2 ^ 3 * X 0


/-- The Klein quartic is nonsingular. -/
example {x y z : K} (h : MvPolynomial.eval ![x, y, z] (klein K) = 0)
    (hdz : ∀ i, MvPolynomial.eval ![x, y, z] (MvPolynomial.pderiv i (klein K)) = 0) :
    ![x, y, z] = 0 := by
  have h₀ := hdz 0
  have h₁ := hdz 1
  have h₂ := hdz 2
  simp [map_ofNat] at h h₀ h₁ h₂
  ext i
  fin_cases i <;> dsimp
  · polyrith
  · polyrith
  · polyrith

end Klein

section Weierstrass


variable (p q : K)

/-- Defining polynomial for a Weierstrass-form elliptic curve zy² = x³ + pxz² + qz³ as a
projective hypersurface in Kℙ². -/
abbrev weierstrass : MvPolynomial (Fin 3) K :=
  -X 2 * X 1 ^ 2 + X 0 ^ 3 + C p * X 0 * X 2 ^ 2 + C q * X 2 ^ 3

/-- A Weierstrass-form elliptic curve with nonzero discriminant `27 * q ^ 2 + 4 * p ^ 3` is
nonsingular. -/
example {x y z : K} (disc : 27 * q ^ 2 + 4 * p ^ 3 ≠ 0)
    (h : MvPolynomial.eval ![x, y, z] (weierstrass K p q) = 0)
    (hdz : ∀ i, MvPolynomial.eval ![x, y, z] (MvPolynomial.pderiv i (weierstrass K p q)) = 0) :
    ![x, y, z] = 0 := by
  have h₀ := hdz 0
  have h₁ := hdz 1
  have h₂ := hdz 2
  simp [map_ofNat] at h h₀ h₁ h₂
  ext i
  fin_cases i <;> dsimp
  · sorry
  · sorry
  · sorry

end Weierstrass
