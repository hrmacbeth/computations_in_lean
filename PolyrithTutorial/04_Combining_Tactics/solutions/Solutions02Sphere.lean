/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Heather Macbeth
-/
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Group.Action.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Polyrith

set_option quotPrecheck false
noncomputable section

-- introduce notation for the circle
local notation "𝕊" => {v : ℝ × ℝ | v.1 ^ 2 + v.2 ^ 2 = 1}

/-- Stereographic projection, forward direction. This is a map from `ℝ × ℝ` to `ℝ`. It is
smooth away from the horizontal line `v.2 = 1`.  It restricts on the unit circle to the
stereographic projection. -/
def stereoToFun (p : 𝕊) : ℝ := 2 * p.val.1 / (1 - p.val.2)

@[simp]
theorem stereoToFun_apply (p : 𝕊) : stereoToFun p = 2 * p.val.1 / (1 - p.val.2) := rfl

/-- Stereographic projection, reverse direction.  This is a map from `ℝ` to the unit circle
`𝕊` in `ℝ × ℝ`. -/
def stereoInvFun (w : ℝ) : 𝕊 where
  val := (w ^ 2 + 4)⁻¹ • (4 * w, w ^ 2 - 4)
  property := by
    dsimp
    field_simp
    ring

@[simp]
theorem stereoInvFun_apply (w : ℝ) :
    (stereoInvFun w : ℝ × ℝ) = (w ^ 2 + 4)⁻¹ • (4 * w, w ^ 2 - 4) :=
  rfl

theorem stereoInvFun_ne_north_pole (w : ℝ) : stereoInvFun w ≠ (⟨(0, 1), by simp⟩ : 𝕊) := by
  refine Subtype.coe_ne_coe.1 ?_
  dsimp
  rw [Prod.mk.inj_iff]
  rintro ⟨h₁, h₂⟩
  field_simp at h₁ h₂
  have : (1 : ℝ) = 0 := by linear_combination (exp := 0) -1 * h₂ / 8
  norm_num at this

theorem stereo_left_inv {p : 𝕊} (hp : (p : ℝ × ℝ) ≠ (0, 1)) :
    stereoInvFun (stereoToFun p) = p := by
  ext1
  obtain ⟨⟨x, y⟩, pythag⟩ := p
  dsimp at pythag hp ⊢
  rw [Prod.mk.inj_iff] at hp ⊢
  have ha : 1 - y ≠ 0 := by
    contrapose! hp with ha
    constructor
    · linear_combination (exp := 2) pythag + (y + 1) * ha
    · linear_combination -(1 * ha)
  constructor
  · field_simp
    linear_combination 4 * (y - 1) * x * pythag
  · field_simp
    linear_combination -4 * (y - 1) ^ 3 * pythag

theorem stereo_right_inv (w : ℝ) : stereoToFun (stereoInvFun w) = w := by
  dsimp
  field_simp
  ring

