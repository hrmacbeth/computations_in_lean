/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Heather Macbeth
-/
import data.real.basic
import tactic.polyrith

noncomputable theory

-- introduce notation for the circle
local notation `𝕊` := {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 = 1}

/-- Stereographic projection, forward direction. This is a map from `ℝ × ℝ` to `ℝ`. It is smooth
away from the horizontal line `p.2 = 1`.  It restricts on the unit circle to the stereographic
projection. -/
def stereo_to_fun (p : ℝ × ℝ) : ℝ := 2 * p.1 / (1 - p.2)

@[simp] lemma stereo_to_fun_apply (p : ℝ × ℝ) : stereo_to_fun p = 2 * p.1 / (1 - p.2) :=
rfl

/-- Stereographic projection, reverse direction.  This is a map from `ℝ` to the unit circle `𝕊` in
`ℝ × ℝ`. -/
def stereo_inv_fun (w : ℝ) : 𝕊 :=
⟨(w ^ 2 + 4)⁻¹ • (4 * w, w ^ 2 - 4), 
  begin
    dsimp,
    have h₁ : w ^ 2 + 4 ≠ 0 := by nlinarith,
    field_simp,
    ring,  
  end⟩

@[simp] lemma stereo_inv_fun_apply (w : ℝ) :
  (stereo_inv_fun w : ℝ × ℝ) = (w ^ 2 + 4)⁻¹ • (4 * w, w ^ 2 - 4) :=
rfl

lemma stereo_inv_fun_ne_north_pole (w : ℝ) :
  stereo_inv_fun w ≠ (⟨(0, 1), by simp⟩ : 𝕊) :=
begin
  refine subtype.ne_of_val_ne _,
  dsimp,
  rw [prod.mk.inj_iff],
  intros h,
  have h₁ : w ^ 2 + 4 ≠ 0 := by nlinarith,
  field_simp at h,
  have : (8:ℝ) = 0 := by linear_combination - h.2,
  norm_num at this,
end

lemma stereo_left_inv {p : 𝕊} (hp : (p : ℝ × ℝ) ≠ (0, 1)) :
  stereo_inv_fun (stereo_to_fun ↑p) = p :=
begin
  ext1,
  obtain ⟨⟨x, y⟩, pythag⟩ := p,
  dsimp at pythag hp ⊢,
  rw prod.mk.inj_iff at hp ⊢,
  have ha : 1 - y ≠ 0,
  { contrapose! hp with ha,
    have : y = 1 := by linear_combination -ha,
    refine ⟨_, this⟩,
    have : x ^ 2 = 0 := by linear_combination pythag - (y + 1) * this,
    exact pow_eq_zero this },
  have : (2 * x) ^ 2 + 4 * (1 - y) ^ 2 ≠ 0,
  { refine ne_of_gt _,
    have : 0 < (1 - y) ^ 2 := sq_pos_of_ne_zero (1 - y) ha,
    nlinarith },
  split,
  { field_simp,
    linear_combination 4 * (y - 1) * x * pythag },
  { field_simp,
    linear_combination - 4 * (y - 1) ^ 3 * pythag },
end

lemma stereo_right_inv (w : ℝ) : stereo_to_fun ↑(stereo_inv_fun w) = w :=
begin
  dsimp,
  have : w ^ 2 + 4 ≠ 0 := by nlinarith,
  field_simp,
  ring,
end

