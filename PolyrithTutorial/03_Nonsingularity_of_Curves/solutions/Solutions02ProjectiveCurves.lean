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
  simp at h h₀ h₁ h₂
  ext i
  fin_cases i <;> dsimp
  · linear_combination (exp := 6)
      -(27 / 28 * x * y * z * h₀) + (x ^ 3 - 3 / 28 * y ^ 2 * z) * h₁ + 9 / 28 * y * z ^ 2 * h₂
  · linear_combination (exp := 6)
      9 / 28 * x ^ 2 * z * h₀ - 27 / 28 * y * x * z * h₁ + (y ^ 3 - 3 / 28 * x * z ^ 2) * h₂
  · -- FIXME polyrith tabbing issue
    linear_combination (exp := 6)
      (z ^ 3 - 3 / 28 * x ^ 2 * y) * h₀ + 9 / 28 * x * y ^ 2 * h₁ - 27 / 28 * z * x * y * h₂

end Klein

section Weierstrass

variable (p q : K)

/-- Defining polynomial for a Weierstrass-form elliptic curve zy² = x³ + pxz² + qz³ as a
projective hypersurface in Kℙ². -/
abbrev weierstrass : MvPolynomial (Fin 3) K :=
  -X 2 * X 1 ^ 2 + X 0 ^ 3 + C p * X 0 * X 2 ^ 2 + C q * X 2 ^ 3

set_option maxHeartbeats 500000 in
/-- A Weierstrass-form elliptic curve with nonzero discriminant `27 * q ^ 2 + 4 * p ^ 3` is
nonsingular. -/
example {x y z : K} (disc : 27 * q ^ 2 + 4 * p ^ 3 ≠ 0)
    (h : MvPolynomial.eval ![x, y, z] (weierstrass K p q) = 0)
    (hdz : ∀ i, MvPolynomial.eval ![x, y, z] (MvPolynomial.pderiv i (weierstrass K p q)) = 0) :
    ![x, y, z] = 0 := by
  have h₀ := hdz 0
  have h₁ := hdz 1
  have h₂ := hdz 2
  simp at h h₀ h₁ h₂
  ext i
  fin_cases i <;> dsimp
  all_goals apply mul_left_cancel₀ disc
  · linear_combination (exp := 4)
      (256 / 3 * p ^ 12 * x ^ 2 + 128 * q * p ^ 11 * x * z + 2304 * q ^ 2 * p ^ 9 * x ^ 2 +
                                2592 * q ^ 3 * p ^ 8 * x * z -
                              64 * q * p ^ 10 * y ^ 2 +
                            23328 * q ^ 4 * p ^ 6 * x ^ 2 +
                          17496 * q ^ 5 * p ^ 5 * x * z -
                        1296 * q ^ 3 * p ^ 7 * y ^ 2 +
                      104976 * q ^ 6 * p ^ 3 * x ^ 2 +
                    39366 * q ^ 7 * p ^ 2 * x * z -
                  8748 * q ^ 5 * p ^ 4 * y ^ 2 +
                177147 * q ^ 8 * x ^ 2 -
              19683 * q ^ 7 * p * y ^ 2) *
            h₀ +
          (-(64 / 3 * p ^ 12 * x * y) + 32 * q * p ^ 11 * z * y - 432 * q ^ 2 * p ^ 9 * x * y +
                      648 * q ^ 3 * p ^ 8 * z * y -
                    2916 * q ^ 4 * p ^ 6 * x * y +
                  4374 * q ^ 5 * p ^ 5 * z * y -
                6561 * q ^ 6 * p ^ 3 * x * y +
              19683 / 2 * q ^ 7 * p ^ 2 * z * y) *
            h₁ +
        (-(128 / 3 * p ^ 12 * x * z) - 192 * q * p ^ 10 * x ^ 2 - 864 * q ^ 2 * p ^ 9 * x * z -
                    3888 * q ^ 3 * p ^ 7 * x ^ 2 -
                  5832 * q ^ 4 * p ^ 6 * x * z -
                26244 * q ^ 5 * p ^ 4 * x ^ 2 -
              13122 * q ^ 6 * p ^ 3 * x * z -
            59049 * q ^ 7 * p * x ^ 2) *
          h₂
  · linear_combination (exp := 3)
      (96 * q * p ^ 9 * z + 64 * p ^ 10 * x + 1944 * q ^ 3 * p ^ 6 * z + 1296 * q ^ 2 * p ^ 7 * x +
                  13122 * q ^ 5 * p ^ 3 * z +
                8748 * q ^ 4 * p ^ 4 * x +
              59049 / 2 * q ^ 7 * z +
            19683 * q ^ 6 * p * x) *
          h₁ +
        (-(64 * p ^ 9 * y) - 1296 * q ^ 2 * p ^ 6 * y - 8748 * q ^ 4 * p ^ 3 * y -
            19683 * q ^ 6 * y) *
          h₂
  · linear_combination (exp := 5)
      (1024 * z ^ 3 * p ^ 14 + 34560 * z ^ 3 * q ^ 2 * p ^ 11 + 4608 * z ^ 2 * q * p ^ 12 * x +
                        419904 * z ^ 3 * q ^ 4 * p ^ 8 +
                      93312 * z ^ 2 * q ^ 3 * p ^ 9 * x +
                    2204496 * z ^ 3 * q ^ 6 * p ^ 5 +
                  629856 * z ^ 2 * q ^ 5 * p ^ 6 * x +
                4251528 * z ^ 3 * q ^ 8 * p ^ 2 +
              1417176 * z ^ 2 * q ^ 7 * p ^ 3 * x) *
            h₀ +
          (-(768 * z * p ^ 13 * y * x) + 7776 * z ^ 2 * q ^ 3 * p ^ 9 * y -
                                  20736 * z * q ^ 2 * p ^ 10 * y * x -
                                3456 * q * p ^ 11 * y * x ^ 2 +
                              157464 * z ^ 2 * q ^ 5 * p ^ 6 * y -
                            209952 * z * q ^ 4 * p ^ 7 * y * x -
                          69984 * q ^ 3 * p ^ 8 * y * x ^ 2 +
                        1062882 * z ^ 2 * q ^ 7 * p ^ 3 * y -
                      944784 * z * q ^ 6 * p ^ 4 * y * x -
                    472392 * q ^ 5 * p ^ 5 * y * x ^ 2 +
                  4782969 / 2 * z ^ 2 * q ^ 9 * y -
                1594323 * z * q ^ 8 * p * y * x -
              1062882 * q ^ 7 * p ^ 2 * y * x ^ 2) *
            h₁ +
        (-(1536 * z ^ 2 * p ^ 13 * x) + 15552 * z ^ 3 * q ^ 3 * p ^ 9 -
                                41472 * z ^ 2 * q ^ 2 * p ^ 10 * x -
                              6912 * z * q * p ^ 11 * x ^ 2 +
                            314928 * z ^ 3 * q ^ 5 * p ^ 6 -
                          419904 * z ^ 2 * q ^ 4 * p ^ 7 * x -
                        139968 * z * q ^ 3 * p ^ 8 * x ^ 2 +
                      2125764 * z ^ 3 * q ^ 7 * p ^ 3 -
                    1889568 * z ^ 2 * q ^ 6 * p ^ 4 * x -
                  944784 * z * q ^ 5 * p ^ 5 * x ^ 2 +
                4782969 * z ^ 3 * q ^ 9 -
              3188646 * z ^ 2 * q ^ 8 * p * x -
            2125764 * z * q ^ 7 * p ^ 2 * x ^ 2) *
          h₂

end Weierstrass
