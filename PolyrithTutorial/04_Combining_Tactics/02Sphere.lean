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
    sorry

@[simp]
theorem stereoInvFun_apply (w : ℝ) :
    (stereoInvFun w : ℝ × ℝ) = (w ^ 2 + 4)⁻¹ • (4 * w, w ^ 2 - 4) :=
  rfl


theorem stereoInvFun_ne_north_pole (w : ℝ) : stereoInvFun w ≠ (⟨(0, 1), by simp⟩ : 𝕊) := by
  refine Subtype.coe_ne_coe.1 ?_
  dsimp
  rw [Prod.mk.inj_iff]
  rintro ⟨h₁, h₂⟩
  sorry

theorem stereo_left_inv {p : 𝕊} (hp : (p : ℝ × ℝ) ≠ (0, 1)) :
    stereoInvFun (stereoToFun p) = p := by
  ext1
  obtain ⟨⟨x, y⟩, pythag⟩ := p
  dsimp at pythag hp ⊢
  rw [Prod.mk.inj_iff] at hp ⊢
  sorry

theorem stereo_right_inv (w : ℝ) : stereoToFun (stereoInvFun w) = w := by
  dsimp
  sorry

/-- Stereographic projection, as a bijection to `ℝ` from the complement of `(0, 1)` in the
unit circle `𝕊` in `ℝ × ℝ`. -/
def stereographicProjection : ({(⟨(0, 1), by simp⟩ : 𝕊)}ᶜ : Set 𝕊) ≃ ℝ where
  toFun := stereoToFun ∘ (·)
  invFun w := ⟨stereoInvFun w, stereoInvFun_ne_north_pole w⟩
  left_inv p := Subtype.coe_injective <| stereo_left_inv (Subtype.coe_injective.ne p.prop)
  right_inv w := stereo_right_inv w
