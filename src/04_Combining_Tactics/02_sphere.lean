/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Heather Macbeth
-/
import data.real.basic
import tactic.polyrith

noncomputable theory


-- introduce notation for the circle
local notation `π` := {p : β Γ β | p.1 ^ 2 + p.2 ^ 2 = 1}

/-- Stereographic projection, forward direction. This is a map from `β Γ β` to `β`. It is smooth
away from the horizontal line `p.2 = 1`.  It restricts on the unit circle to the stereographic
projection. -/
def stereo_to_fun (p : π) : β := 2 * p.1.1 / (1 - p.1.2)

@[simp] lemma stereo_to_fun_apply (p : π) : stereo_to_fun p = 2 * p.1.1 / (1 - p.1.2) :=
rfl


/-- Stereographic projection, reverse direction.  This is a map from `β` to the unit circle `π` in
`β Γ β`. -/
def stereo_inv_fun (w : β) : π :=
β¨(w ^ 2 + 4)β»ΒΉ β’ (4 * w, w ^ 2 - 4), 
  begin
    dsimp,
    sorry,
  endβ©

@[simp] lemma stereo_inv_fun_apply (w : β) :
  (stereo_inv_fun w : β Γ β) = (w ^ 2 + 4)β»ΒΉ β’ (4 * w, w ^ 2 - 4) :=
rfl


lemma stereo_inv_fun_ne_north_pole (w : β) :
  stereo_inv_fun w β  (β¨(0, 1), by simpβ© : π) :=
begin
  refine subtype.ne_of_val_ne _,
  dsimp,
  rw [prod.mk.inj_iff],
  intros h,
  sorry,
end


lemma stereo_left_inv {p : π} (hp : (p : β Γ β) β  (0, 1)) :
  stereo_inv_fun (stereo_to_fun p) = p :=
begin
  ext1,
  obtain β¨β¨x, yβ©, pythagβ© := p,
  dsimp at pythag hp β’,
  rw prod.mk.inj_iff at hp β’,
  sorry,
end


lemma stereo_right_inv (w : β) : stereo_to_fun (stereo_inv_fun w) = w :=
begin
  dsimp,
  sorry,
end


/-- Stereographic projection, as a bijection to `β` from the complement of `(0, 1)` in the unit 
circle `π` in `β Γ β`. -/
def stereographic_projection : ({(β¨(0, 1), by simpβ© : π)}αΆ : set π) β β :=
{ to_fun := stereo_to_fun β coe,
  inv_fun := Ξ» w, β¨stereo_inv_fun w, stereo_inv_fun_ne_north_pole wβ©,
  left_inv := Ξ» p, subtype.coe_injective $ stereo_left_inv (subtype.coe_injective.ne p.prop),
  right_inv := Ξ» w, stereo_right_inv w }
