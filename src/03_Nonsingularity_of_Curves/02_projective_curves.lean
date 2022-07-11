/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import data.mv_polynomial.pderiv
import data.mv_polynomial.comm_ring
import tactic.polyrith
import tactic.norm_fin

noncomputable theory

open mv_polynomial

variables (K : Type*) [field K] [char_zero K]

/-! This file contains a lot of computationally-intensive evaluation of polynomials and their
derivatives. We speed it up slightly by specifiying in advance the path the simplifier should take.
-/

mk_simp_attribute poly_simps "simp-lemmas for polynomials"

attribute [poly_simps] mv_polynomial.eval_X mv_polynomial.eval_C
  map_add map_sub map_mul map_neg map_bit0 map_bit1 map_one map_pow map_zero
  matrix.cons_val_zero matrix.cons_val_one matrix.head_cons
  matrix.cons_vec_bit0_eq_alt0 matrix.cons_vec_bit1_eq_alt1
  matrix.cons_vec_alt0 matrix.cons_vec_alt1
  matrix.cons_append matrix.empty_append
  derivation.leibniz derivation.leibniz_pow pderiv_C pderiv_X_of_ne pderiv_X_self pi.single_eq_of_ne
  algebra.id.smul_eq_mul nsmul_eq_mul
  nat.cast_bit1 nat.cast_bit0 nat.cast_one
  -- `ring`/`linear_combination` would take care of the next ones, but we add them to aid human
  -- inspection
  mul_zero zero_mul mul_one one_mul add_zero zero_add pow_one mul_neg neg_zero

section klein


-- use (2x+1), (1-x+√3y), (1-x-√3y) for a nice picture

/-- Defining polynomial for the Klein quartic curve x³y + y³z + z³x = 0 as a projective hypersurface
in Kℙ². -/
@[reducible] def klein : mv_polynomial (fin 3) K :=
X 0 ^ 3 * X 1 + X 1 ^ 3 * X 2 + X 2 ^ 3 * X 0


/- If the first five lines of code in the next example run too slowly to meaningfully experiment
with the rest of the proof, temporarily comment the lines above and paste in the lines below, 
which states their result without proof.
  have h : x ^ 3 * y + y ^ 3 * z + z ^ 3 * x = 0 := sorry,
  have h₀ : y * (3 * x ^ 2) + z ^ 3 = 0 := sorry,
  have h₁ : x ^ 3 + z * (3 * y ^ 2) = 0 := sorry,
  have h₂ : y ^ 3 + x * (3 * z ^ 2) = 0 := sorry,
-/

/-- The Klein quartic is nonsingular. -/
example {x y z : K} (h : mv_polynomial.eval ![x, y, z] (klein K) = 0)
  (hdz : ∀ i, mv_polynomial.eval ![x, y, z] (mv_polynomial.pderiv i (klein K)) = 0) :
  ![x, y, z] = 0 :=
begin
  have : 3 - 1 = 2 := by norm_num,
  have h₀ := hdz 0,
  have h₁ := hdz 1,
  have h₂ := hdz 2,
  simp only [this] with poly_simps at h h₀ h₁ h₂ {discharger := `[norm_num1]},
  { sorry },
end

end klein

section weierstrass

variables (p q : K)

/-- Defining polynomial for a Weierstrass-form elliptic curve zy² = x³ + pxz² + qz³ as a projective
hypersurface in Kℙ². -/
@[reducible] def weierstrass : mv_polynomial (fin 3) K :=
- X 2 * X 1 ^ 2 + X 0 ^ 3 + C p * X 0 * X 2 ^ 2 + C q * X 2 ^ 3


/- If the first five lines of code in the next example run too slowly to meaningfully experiment
with the rest of the proof, temporarily comment the lines above and paste in the lines below, 
which states their result without proof.
  have h : -z * y ^ 2 + x ^ 3 + p * x * z ^ 2 + q * z ^ 3 = 0 := sorry,
  have h₀ : 3 * x ^ 2 + z ^ 2 * p = 0 := sorry,
  have h₁ : -z * (2 * y) = 0 := sorry,
  have h₂ : -y ^ 2 + p * x * (2 * z) + q * (3 * z ^ 2) = 0 := sorry,
-/

/-- A Weierstrass-form elliptic curve with nonzero discriminant `27 * q ^ 2 + 4 * p ^ 3` is
nonsingular. -/
example {x y z : K} (disc : 27 * q ^ 2 + 4 * p ^ 3 ≠ 0)
  (h : mv_polynomial.eval ![x, y, z] (weierstrass K p q) = 0)
  (hdz : ∀ i, mv_polynomial.eval ![x, y, z] (mv_polynomial.pderiv i (weierstrass K p q)) = 0) :
  ![x, y, z] = 0 :=
begin
  have three_sub : 3 - 1 = 2 := by norm_num,
  have two_sub : 2 - 1 = 1 := by norm_num,
  have h₀ := hdz 0,
  have h₁ := hdz 1,
  have h₂ := hdz 2,
  simp only [three_sub, two_sub] with poly_simps at h h₀ h₁ h₂ {discharger := `[norm_num1]},
  sorry,
end

end weierstrass
