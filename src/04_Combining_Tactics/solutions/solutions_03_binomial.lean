/-
Copyright (c) 2022 Julian Kuelshammer. All rights reserved.
Adapted from mathlib, released under Apache 2.0 license as described in that repository.
Authors: Julian Kuelshammer, Heather Macbeth
-/
import data.nat.choose.central
import tactic.field_simp
import tactic.polyrith

example {i j : ℕ} :
  ((i + 1).central_binom:ℚ) * j.central_binom * (i - j + 1) / (2 * (i + j + 1) * (i + j + 2))
  -  i.central_binom * (j + 1).central_binom * (i - j - 1) / (2 * (i + j + 1) * (i + j + 2))
  = i.central_binom / (i + 1) * (j.central_binom / (j + 1)) :=
begin
  have h₁ : ((i:ℚ) + 1) * (i + 1).central_binom = 2 * (2 * i + 1) * i.central_binom,
  { exact_mod_cast i.succ_mul_central_binom_succ },
  have h₂ : ((j:ℚ) + 1) * (j + 1).central_binom = 2 * (2 * j + 1) * j.central_binom,
  { exact_mod_cast j.succ_mul_central_binom_succ },
  have : (i:ℚ) + j + 1 ≠ 0,
  { exact_mod_cast (i + j).succ_ne_zero },
  have : (i:ℚ) + j + 2 ≠ 0,
  { exact_mod_cast (i + j + 1).succ_ne_zero },
  have : (i:ℚ) + 1 ≠ 0,
  { exact_mod_cast i.succ_ne_zero },
  have : (j:ℚ) + 1 ≠ 0,
  { exact_mod_cast j.succ_ne_zero },
  field_simp,
  linear_combination
    (2:ℚ) * j.central_binom * (i - j + 1)  * (j + 1) * (i + j + 1) * (i + j + 2) * h₁
    - 2 * i.central_binom * (i - j - 1) * (i + 1) * (i + j + 1) * (i + j + 2) * h₂,
end
