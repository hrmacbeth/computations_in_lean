/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import analysis.quaternion
import data.matrix.notation
import linear_algebra.unitary_group
import tactic.polyrith

open_locale quaternion

/-! This file contains a lot of computationally-intensive evaluation of matrices and quaternions.
We speed it up slightly by specifiying in advance the path the simplifier should take. -/

mk_simp_attribute quaternion_simps "simp-lemmas for quaternions and orthogonal group"

attribute [quaternion_simps]
  matrix.vec_head matrix.vec_tail matrix.star_eq_conj_transpose matrix.mul_eq_mul
  matrix.cons_mul matrix.cons_vec_mul matrix.cons_val_zero  matrix.cons_val_one
  matrix.cons_vec_bit0_eq_alt0 matrix.cons_append matrix.cons_vec_alt0
  matrix.empty_vec_mul matrix.empty_append matrix.empty_mul matrix.one_apply_eq matrix.one_apply_ne
  matrix.conj_transpose_apply matrix.head_cons matrix.unitary_group.one_val
  function.comp_app
  fin.succ_zero_eq_one fin.succ_one_eq_two
  pi.add_apply pi.smul_apply pi.zero_apply
  is_R_or_C.star_def is_R_or_C.conj_to_real algebra.id.smul_eq_mul submonoid.coe_one neg_zero
  subtype.ext_iff subtype.coe_mk set_like.mem_coe
  quaternion_algebra.ext_iff
  quaternion.one_re quaternion.one_im_i quaternion.one_im_j quaternion.one_im_k
  quaternion.neg_re quaternion.neg_im_i quaternion.neg_im_j quaternion.neg_im_k
  monoid_hom.mem_mker
  set.mem_insert_iff set.mem_singleton_iff


/-- Explicit matrix formula for the double cover of SO(3, ℝ) by the unit quaternions. -/
@[quaternion_simps]
def quaternion.to_matrix (a : ℍ) : matrix (fin 3) (fin 3) ℝ :=
let ⟨x, y, z, w⟩ := a in
![![x ^ 2 + y ^ 2 - z ^ 2 - w ^ 2, 2 * (y * z - w * x), 2 * (y * w + z * x)],
  ![2 * (y * z + w * x), x ^ 2 + z ^ 2 - y ^ 2 - w ^ 2, 2 * (z * w - y * x)],
  ![2 * (y * w - z * x), 2 * (z * w + y * x), x ^ 2 + w ^ 2 - y ^ 2 - z ^ 2]]


/-- The explicit matrix formula `to_matrix` defines a monoid homomorphism from the quaternions into
the algebra of 3x3 matrices. -/
def quaternion.to_matrix_hom' : ℍ →* matrix (fin 3) (fin 3) ℝ :=
{ to_fun := quaternion.to_matrix,
  map_one' := show quaternion.to_matrix ⟨1, 0, 0, 0⟩ = 1, begin
    ext i j; fin_cases i; fin_cases j;
      simp only with quaternion_simps { discharger := `[norm_num1] }; norm_num,
  end,
  map_mul' :=  begin
    rintros ⟨x, y, z, w⟩ ⟨r, s, t, u⟩,
    show quaternion.to_matrix ⟨_, _, _, _⟩
      = quaternion.to_matrix ⟨_, _, _, _⟩ * quaternion.to_matrix ⟨_, _, _, _⟩,
    ext i j; fin_cases i; fin_cases j; simp only with quaternion_simps; ring,
  end }


/-- The group (we only prove it to be a monoid) of unit quaternions. -/
def unit_quaternions : submonoid ℍ :=
monoid_hom.mker ((quaternion.norm_sq : ℍ →*₀ ℝ) : ℍ →* ℝ)

@[simp] lemma mem_unit_quaternions (a : ℍ) :
  a ∈ unit_quaternions ↔ a.re ^ 2 + a.im_i ^ 2 + a.im_j ^ 2 + a.im_k ^ 2 = 1 :=
by { rw ← quaternion.norm_sq_def' a, exact iff.rfl }


#check matrix.orthogonal_group (fin 3) ℝ
-- matrix.orthogonal_group ℝ : submonoid (matrix (fin 3) (fin 3) ℝ)

namespace unit_quaternions
open quaternion


/-- The explicit matrix formula `to_matrix` sends a unit quaternion to an element of SO(3, ℝ). -/
lemma to_matrix_mem_orthogonal {a : ℍ} (ha : a ∈ unit_quaternions) :
  to_matrix a ∈ matrix.orthogonal_group (fin 3) ℝ :=
begin
  rw matrix.mem_orthogonal_group_iff,
  cases a with x y z w,
  have H : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 1 := by rwa [mem_unit_quaternions] at ha,
  ext i j,
  fin_cases i; fin_cases j; simp only with quaternion_simps { discharger := `[norm_num1] },
  { polyrith },
  { polyrith },
  { polyrith },
  { polyrith },
  { polyrith },
  { polyrith },
  { polyrith },
  { polyrith },
  { polyrith },
end

/-- Double cover of SO(3, ℝ) by the unit quaternions, as a homomorphism of monoids. This is obtained
by restriction of the homomorphism `quaternion.to_matrix_hom'` from `ℍ` into the 3x3 matrices; it is
well-defined by `to_matrix_mem_orthogonal`. -/
def to_matrix_hom : unit_quaternions →* matrix.orthogonal_group (fin 3) ℝ :=
(to_matrix_hom'.restrict unit_quaternions).cod_restrict (matrix.orthogonal_group (fin 3) ℝ)
(λ a, to_matrix_mem_orthogonal a.prop)

@[quaternion_simps] lemma coe_to_matrix_hom_apply (a : unit_quaternions) :
  @coe _ (matrix (fin 3) (fin 3) ℝ) coe_to_lift (to_matrix_hom a) = to_matrix a :=
rfl



/-- The unit quaternion -1 (the quaternion -1 together with a proof that its norm is one). -/
def neg_one : unit_quaternions := ⟨-1, show (⟨_, _, _, _⟩ : ℍ) ∈ _, by simp⟩

@[quaternion_simps] lemma coe_neg_one : (neg_one : ℍ) = -1 := rfl

/-- Verify the "double cover" property of the homomorphism from unit quaternions to SO(3, ℝ): the
kernel is {1, -1}. -/
lemma to_matrix_hom_mker : (to_matrix_hom.mker : set unit_quaternions) = {1, neg_one} :=
begin
  ext a,
  obtain ⟨⟨x, y, z, w⟩, h⟩ := a,
  have H : x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 = 1 := by rwa [mem_unit_quaternions] at h,
  simp only with quaternion_simps,
  split,
  { -- hard direction: a quaternion in the kernel is ±1
    intros h,
    have h₀₁ := congr_fun₂ h 0 1,
    -- Add more matrix entry inspections here as needed, and adjust the simplification line.
    -- The `polyrith` applications that follow will be broken until you do this!
    simp only with quaternion_simps at h₀₁ { discharger := `[norm_num1] },
    have hy : y = 0,
    { polyrith },
    have hz : z = 0,
    { polyrith },
    have hw : w = 0,
    { polyrith },
    have hx : x ^ 2 = 1 ^ 2,
    { polyrith },
    -- now do a case division depending on the two cases for `x ^ 2 = 1 ^ 2`
    rw sq_eq_sq_iff_eq_or_eq_neg at hx,
    cases hx,
    { simp [hx, hy, hz, hw] },
    { simp [hx, hy, hz, hw] } },
  { -- easy direction: ±1 are in the kernel
    rintros (⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩); ext i j; fin_cases i; fin_cases j;
      simp only with quaternion_simps { discharger := `[norm_num1] }; norm_num },
end

end unit_quaternions
