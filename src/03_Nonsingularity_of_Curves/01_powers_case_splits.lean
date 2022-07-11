/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Authors: Heather Macbeth
-/
import tactic.polyrith


example {x : ℚ} (hx : x ^ 2 - 4 * x = - 4) : x = 2 :=
by polyrith
-- polyrith failed to retrieve a solution from Sage! ValueError: polynomial is not in the ideal


example {x : ℤ} (hx : x ^ 2 - 4 * x = - 4) : x = 2 :=
begin
  have : (x - 2) ^ 2 = 0 := by polyrith,
  have := pow_eq_zero this,
  polyrith,
end


example {r s : ℚ} (hr : r ≠ 1) (h : r * s - 2 = s - 2 * r) : s = -2 :=
begin
  have hr' : r - 1 ≠ 0,
  { contrapose! hr,
    polyrith },
  apply mul_left_cancel₀ hr',
  polyrith,
end


example {r s : ℚ} (h : r * s - 2 = s - 2 * r) : true :=
begin
  have : (r - 1) * (s + 2) = 0 := by polyrith,
  cases eq_zero_or_eq_zero_of_mul_eq_zero this with H H,
  { sorry }, -- the case `r - 1 = 0`
  { sorry } -- the case `s + 2 = 0`
end
