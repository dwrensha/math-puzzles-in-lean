import data.real.basic
import data.real.sqrt

import analysis.inner_product_space.pi_L2
import analysis.normed_space.pi_Lp

open_locale big_operators

/-
Iranian Mathematical Olympiad 1998, Problem 9

Let x,y,z > 1 and 1/x + 1/y + 1/z = 2. Prove that

  √(x + y + z) ≥ √(x - 1) + √(y - 1) + √(z - 1).

-/

lemma compute_norm (v : euclidean_space ℝ (fin 3)) : ∥v∥ = real.sqrt (∑(i : fin 3), (v i)^2) :=
begin
  have hvi : (∀ i : fin 3, (v i) ^2 = ∥v i∥^2),
  { intro i, rw [real.norm_eq_abs], exact (sq_abs (v i)).symm },
  have := fintype.sum_congr ((λ jj, (v jj)^2): fin 3 → ℝ) (λ jj, ∥v jj∥^2) hvi,
  rw[this],
  exact euclidean_space.norm_eq v,
end

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

  have hx0 : 0 ≤ x := by linarith,
  have hy0 : 0 ≤ y := by linarith,
  have hz0 : 0 ≤ z := by linarith,

  have hx1 : 0 ≤ x - 1 := by linarith,
  have hy1 : 0 ≤ y - 1 := by linarith,
  have hz1 : 0 ≤ z - 1 := by linarith,

  have hxf : (x-1)/x = 1 - 1/x := by field_simp,
  have hyf : (y-1)/y = 1 - 1/y := by field_simp,
  have hzf : (z-1)/z = 1 - 1/z := by field_simp,

  have h1 : (x-1)/x + (y-1)/y + (z-1)/z = 1,
  { rw[hxf, hyf, hzf],
    linarith },

  let v₁ : euclidean_space ℝ (fin 3) := ![real.sqrt x, real.sqrt y, real.sqrt z],
  let v₂ : euclidean_space ℝ (fin 3) :=
      ![real.sqrt ((x - 1)/x), real.sqrt ((y-1)/y), real.sqrt ((z-1)/z)],

  have cauchy_schwarz := @abs_inner_le_norm ℝ (euclidean_space ℝ (fin 3)) _ _ v₁ v₂,

  have hv₁ : ∥v₁∥ = real.sqrt (x + y + z),
  { have hn := compute_norm v₁,
    have h1: ((∑ (i : fin 3), ((v₁ i) ^ 2)) : ℝ) = (v₁ 0)^2 + (v₁ 1)^2 + (v₁ 2)^2,
    { rw[fin.sum_univ_succ, fin.sum_univ_succ, fin.sum_univ_one],
      ring },
    rw [h1] at hn,
    have hv1 : v₁ 0 = real.sqrt x := rfl,
    have hv2 : v₁ 1 = real.sqrt y := rfl,
    have hv3 : v₁ 2 = real.sqrt z := rfl,
    rw [hv1, hv2, hv3] at hn,
    have hxx : (real.sqrt x) ^ 2 = x := real.sq_sqrt hx0,
    have hyy : (real.sqrt y) ^ 2 = y := real.sq_sqrt hy0,
    have hzz : (real.sqrt z) ^ 2 = z := real.sq_sqrt hz0,

    rwa [hxx, hyy, hzz] at hn},

  have hv₂ : ∥v₂∥ = 1,
  { have hn := compute_norm v₂,
    have h2: ((∑ (i : fin 3), ((v₂ i) ^ 2)) : ℝ) = (v₂ 0)^2 + (v₂ 1)^2 + (v₂ 2)^2,
    { rw[fin.sum_univ_succ, fin.sum_univ_succ, fin.sum_univ_one],
      ring },
    rw [h2] at hn,
    have hv1 : v₂ 0 = real.sqrt ((x-1)/x) := rfl,
    have hv2 : v₂ 1 = real.sqrt ((y-1)/y) := rfl,
    have hv3 : v₂ 2 = real.sqrt ((z-1)/z) := rfl,
    rw [hv1, hv2, hv3] at hn,
    have hxx : 0 ≤ (x-1)/x := div_nonneg hx1 hx0,
    have hxx' : real.sqrt(((x - 1) / x)) ^2 = (x - 1) / x := real.sq_sqrt hxx,

    have hyy : 0 ≤ (y-1)/y := div_nonneg hy1 hy0,
    have hyy' : real.sqrt(((y - 1) / y)) ^2 = (y - 1) / y := real.sq_sqrt hyy,

    have hzz : 0 ≤ (z-1)/z := div_nonneg hz1 hz0,
    have hzz' : real.sqrt(((z - 1) / z)) ^2 = (z - 1) / z := real.sq_sqrt hzz,

    rw[hxx', hyy', hzz'] at hn,
    have hfs: (x - 1) / x + (y - 1) / y + (z - 1) / z = 3 - (1/x + 1/y + 1/z) := by {field_simp, ring},
    rw[hfs, h] at hn,
    have ha: (3: ℝ) - 2 = 1 := by linarith,
    rw[hn, ha],
    exact real.sqrt_one},

  rw [hv₁, hv₂, mul_one] at cauchy_schwarz,

  have hinner := calc ((inner v₁ v₂): ℝ)
          = ∑(i : fin 3), v₁ i * v₂ i : rfl
      ... = v₁ 0 * v₂ 0 + v₁ 1 * v₂ 1 + v₁ 2 * v₂ 2 :
               by {rw[fin.sum_univ_succ, fin.sum_univ_succ, fin.sum_univ_one], ring}
      ... = real.sqrt x * real.sqrt ((x - 1) / x) +
            real.sqrt y * real.sqrt ((y - 1) / y) +
            real.sqrt z * real.sqrt ((z - 1) / z) : rfl,

  have hxxx : x * ((x - 1) / x) = x - 1 := by {field_simp, ring},
  have hyyy : y * ((y - 1) / y) = y - 1 := by {field_simp, ring},
  have hzzz : z * ((z - 1) / z) = z - 1 := by {field_simp, ring},

  rw [←real.sqrt_mul hx0 ((x - 1) / x),
      ←real.sqrt_mul hy0 ((y - 1) / y),
      ←real.sqrt_mul hz0 ((z - 1) / z),
      hxxx, hyyy, hzzz] at hinner,

  rw [hinner, is_R_or_C.abs_to_real] at cauchy_schwarz,
  exact le_of_abs_le cauchy_schwarz,
end
