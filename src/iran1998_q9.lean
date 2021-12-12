import data.real.basic
import data.real.sqrt

/-
Iranian Mathematical Olympiad 1998, Problem 9

Let x,y,z > 1 and 1/x + 1/y + 1/z = 2. Prove that

  √(x + y + z) ≥ √(x - 1) + √(y - 1) + √(z - 1).

-/

theorem iran1998_q9
  (x y z : ℝ)
  (hx : 1 < x)
  (hy : 1 < y)
  (hz : 1 < z)
  (h : 1/x + 1/y + 1/z = 2) :
  real.sqrt(x - 1) + real.sqrt(y - 1) + real.sqrt(z - 1) ≤ real.sqrt (x + y + z) :=
begin
  -- By cauchy schwarz,
  -- √(x + y + z) √((x-1)/x + (y-1)/y + (z-1)/z) ≥ √(x - 1) + √(y - 1) + √(z - 1).
  --
  -- On the other hand, by hypothesis,
  -- (x-1)/x + (y-1)/y + (z-1)/z = 1.
  --
  -- The desired result follows.

  have hxz : x ≠ 0 := by linarith,
  have hyz : y ≠ 0 := by linarith,
  have hzz : z ≠ 0 := by linarith,

  have hxf : (x-1)/x = 1 - 1/x := by field_simp,
  have hyf : (y-1)/y = 1 - 1/y := by field_simp,
  have hzf : (z-1)/z = 1 - 1/z := by field_simp,

  have : (x-1)/x + (y-1)/y + (z-1)/z = 1,
  { rw[hxf, hyf, hzf],
    linarith },

  sorry
end
