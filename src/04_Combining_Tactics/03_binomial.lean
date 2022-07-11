/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Julian Kuelshammer, Heather Macbeth
-/
import data.nat.choose.central
import tactic.field_simp
import tactic.polyrith

#check nat.central_binom -- nat.central_binom : ℕ → ℕ
#check nat.succ_mul_central_binom_succ 
#check nat.succ_ne_zero -- nat.succ_ne_zero : ∀ (n : ℕ), n.succ ≠ 0


example {i j : ℕ} :
  ((i + 1).central_binom:ℚ) * j.central_binom * (i - j + 1) / (2 * (i + j + 1) * (i + j + 2))
  -  i.central_binom * (j + 1).central_binom * (i - j - 1) / (2 * (i + j + 1) * (i + j + 2))
  = i.central_binom / (i + 1) * (j.central_binom / (j + 1)) :=
begin
  have h₁ : ((i:ℚ) + 1) * (i + 1).central_binom = 2 * (2 * i + 1) * i.central_binom,
  { sorry },
  have h₂ : ((j:ℚ) + 1) * (j + 1).central_binom = 2 * (2 * j + 1) * j.central_binom,
  { sorry },
  have : (i:ℚ) + j + 1 ≠ 0,
  { sorry },
  have : (i:ℚ) + j + 2 ≠ 0,
  { sorry },
  have : (i:ℚ) + 1 ≠ 0,
  { sorry },
  have : (j:ℚ) + 1 ≠ 0,
  { sorry },
  sorry,
end
