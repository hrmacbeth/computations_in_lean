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
    sorry,
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
  sorry,
end


lemma stereo_left_inv {p : 𝕊} (hp : (p : ℝ × ℝ) ≠ (0, 1)) :
  stereo_inv_fun (stereo_to_fun ↑p) = p :=
begin
  ext1,
  obtain ⟨⟨x, y⟩, pythag⟩ := p,
  dsimp at pythag hp ⊢,
  rw prod.mk.inj_iff at hp ⊢,
  sorry,
end


lemma stereo_right_inv (w : ℝ) : stereo_to_fun ↑(stereo_inv_fun w) = w :=
begin
  dsimp,
  sorry,
end


/-- Stereographic projection, as a bijection to `ℝ` from the complement of `(0, 1)` in the unit 
circle `𝕊` in `ℝ × ℝ`. -/
def stereographic_projection : ({(⟨(0, 1), by simp⟩ : 𝕊)}ᶜ : set 𝕊) ≃ ℝ :=
{ to_fun := stereo_to_fun ∘ coe,
  inv_fun := λ w, ⟨stereo_inv_fun w, stereo_inv_fun_ne_north_pole w⟩,
  left_inv := λ p, subtype.coe_injective $ stereo_left_inv (subtype.coe_injective.ne p.prop),
  right_inv := λ w, stereo_right_inv w }
