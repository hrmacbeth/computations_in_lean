/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.Quaternion
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Tactic.Polyrith

open Quaternion Matrix

noncomputable section

/-! To make the simplifications in this file work, it's necessary slightly to tweak the standard
setup for what constitutes simplification of matrix expressions.

TODO Think about whether these changes should be made throughout Mathlib. -/

attribute [-simp] vecCons_const
attribute [simp] vecHead vecTail star_eq_conjTranspose

@[simp] theorem Matrix.cons_conjTranspose {α : Type u} [Star α] {m : ℕ} {n' : Type uₙ} (v : n' → α)
    (A : Matrix (Fin m) n' α) :
    conjTranspose (of (vecCons v A)) = of fun i => vecCons (star (v i)) (conjTranspose A i) := by
  ext i j
  refine Fin.cases ?_ ?_ j <;> simp


/-! # Double cover of SO(3, ℝ) -/


/-- Explicit matrix formula for the double cover of SO(3, ℝ) by the unit quaternions. -/
@[simp] def Quaternion.toMatrix (a : ℍ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let ⟨x, y, z, w⟩ := a
  !![x ^ 2 + y ^ 2 - z ^ 2 - w ^ 2, 2 * (y * z - w * x), 2 * (y * w + z * x);
    2 * (y * z + w * x), x ^ 2 + z ^ 2 - y ^ 2 - w ^ 2, 2 * (z * w - y * x);
    2 * (y * w - z * x), 2 * (z * w + y * x), x ^ 2 + w ^ 2 - y ^ 2 - z ^ 2]

/-- The explicit matrix formula `toMatrix` defines a monoid homomorphism from the quaternions
into the algebra of 3x3 matrices. -/
@[simps] def Quaternion.toMatrixHom' : ℍ →* Matrix (Fin 3) (Fin 3) ℝ where
  toFun := Quaternion.toMatrix
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' := by
    rintro ⟨x, y, z, w⟩ ⟨r, s, t, u⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> ring


/-- The group (we only prove it to be a monoid) of unit quaternions. -/
def unitQuaternions : Submonoid ℍ :=
  MonoidHom.mker ((Quaternion.normSq : ℍ →*₀ ℝ) : ℍ →* ℝ)

@[simp] theorem mem_unitQuaternions (a : ℍ) :
    a ∈ unitQuaternions ↔ a.re ^ 2 + a.imI ^ 2 + a.imJ ^ 2 + a.imK ^ 2 = 1 := by
  rw [←Quaternion.normSq_def']
  exact Iff.rfl


#check Matrix.orthogonalGroup (Fin 3) ℝ
-- Matrix.orthogonalGroup (Fin 3) ℝ : Submonoid (Matrix (Fin 3) (Fin 3) ℝ)

namespace unitQuaternions


/-- The explicit matrix formula `to_matrix` sends a unit quaternion to an element of SO(3, ℝ).
-/
theorem toMatrix_mem_orthogonal {a : ℍ} (ha : a ∈ unitQuaternions) :
    toMatrix a ∈ Matrix.orthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_orthogonalGroup_iff]
  obtain ⟨x, y, z, w⟩ := a
  have H : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 1 := by rwa [mem_unitQuaternions] at ha
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp
  · polyrith
  · polyrith
  · polyrith
  · polyrith
  · polyrith
  · polyrith
  · polyrith
  · polyrith
  · polyrith

/-- Double cover of SO(3, ℝ) by the unit quaternions, as a homomorphism of monoids. This is obtained
by restriction of the homomorphism `Quaternion.toMatrixHom'` from `ℍ` into the 3x3 matrices; it is
well-defined by `toMatrix_mem_orthogonal`. -/
abbrev toMatrixHom : unitQuaternions →* Matrix.orthogonalGroup (Fin 3) ℝ :=
  (toMatrixHom'.restrict unitQuaternions).codRestrict (Matrix.orthogonalGroup (Fin 3) ℝ) fun a =>
    toMatrix_mem_orthogonal a.prop


/-- The unit quaternion -1 (the quaternion -1 together with a proof that its norm is one). -/
@[simps] noncomputable def negOne : unitQuaternions := ⟨-1, by simp⟩

/-- Verify the "double cover" property of the homomorphism from unit quaternions to SO(3, ℝ):
the kernel is {1, -1}. -/
theorem toMatrixHom_mker :
    (MonoidHom.mker toMatrixHom : Set unitQuaternions) = {1, negOne} := by
  ext a
  obtain ⟨⟨x, y, z, w⟩, h⟩ := a
  have H : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 1 := by rwa [mem_unitQuaternions] at h
  simp [MonoidHom.mem_mker]
  constructor
  · -- hard direction: a quaternion in the kernel is ±1
    intro h1
    have h₀₁ := congr_fun₂ h1 0 1
    -- Add more matrix entry inspections here as needed, and adjust the simplification line.
    -- The `polyrith` applications that follow will be broken until you do this!
    simp at h₀₁
    obtain rfl : y = 0 := by
      polyrith
    obtain rfl : z = 0 := by
      polyrith
    obtain rfl : w = 0 := by
      polyrith
    have hx : x ^ 2 = (1 : ℝ) ^ 2 := by
      polyrith
    -- now do a case division depending on the two cases for `x ^ 2 = 1 ^ 2`
    rw [sq_eq_sq_iff_eq_or_eq_neg] at hx
    obtain rfl | rfl := hx
    · left
      ext <;> simp
    · right
      ext <;> simp
  · -- easy direction: ±1 are in the kernel
    rintro (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩) <;> ext i j <;> fin_cases i <;>
      fin_cases j <;> simp

end unitQuaternions

