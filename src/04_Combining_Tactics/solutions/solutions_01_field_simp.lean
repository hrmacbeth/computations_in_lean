/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import tactic.field_simp
import tactic.polyrith
import data.real.basic

noncomputable def f : ℝ → ℝ := λ x, (1 - x)⁻¹

example {x : ℝ} (h₁ : x ≠ 1) (h₀ : x ≠ 0) : f (f (f x)) = x :=
begin
  dsimp [f],
  have : 1 - x ≠ 0 := by contrapose! h₁; linear_combination -h₁,
  have : -x ≠ 0 := by contrapose! h₀; linear_combination -h₀,
  have : -x - (1 - x) ≠ 0 := by { intros h, linarith },
  field_simp,
  ring,
end
