import data.real.basic
import data.real.sqrt

import analysis.inner_product_space.pi_L2
import analysis.normed_space.pi_Lp

/-
Iranian Mathematical Olympiad 1998, Problem 9

Let x,y,z > 1 and 1/x + 1/y + 1/z = 2. Prove that

  √(x + y + z) ≥ √(x - 1) + √(y - 1) + √(z - 1).

-/

def construct_vector (x y z : ℝ) : euclidean_space ℝ (fin 3)
| ⟨0, _⟩ := x
| ⟨1, _⟩ := y
| ⟨2, _⟩ := z
| _ := 0 -- impossible


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

  have h1 : (x-1)/x + (y-1)/y + (z-1)/z = 1,
  { rw[hxf, hyf, hzf],
    linarith },

  let v₁ := construct_vector (real.sqrt x) (real.sqrt y) (real.sqrt z),
  let v₂ := construct_vector (real.sqrt ((x - 1)/x)) (real.sqrt ((y-1)/y)) (real.sqrt ((z-1)/z)),

  --have : abs_inner_le_norm v₁ v₂,

  sorry
end
