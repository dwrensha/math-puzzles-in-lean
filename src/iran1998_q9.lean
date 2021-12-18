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

def construct_vector (x y z : ℝ) : euclidean_space ℝ (fin 3)
| ⟨0, _⟩ := x
| ⟨1, _⟩ := y
| ⟨2, _⟩ := z
| _ := 0 -- impossible

lemma compute_norm_aux (v : euclidean_space ℝ (fin 3)) : ∥v∥^2 = (∑(i : fin 3), (v i)^2) :=
begin
  have hips := @euclidean_space.inner_product_space (fin 3) ℝ _ _,
  have hi := hips.to_has_inner,
  have := @inner ℝ (euclidean_space ℝ (fin 3)) hi v v,

  have hh : ((inner v v): ℝ) = (∑(i : fin 3), (v i)^2),
  { simp,
    have hs : ∀ (x : fin 3), v x * v x = (v x) ^2,
    { intro x, ring },
    exact fintype.sum_congr (λ (a : fin 3), v a * v a) (λ (a : fin 3), v a ^ 2) hs
  },

  have hn : ∥v∥^2 = is_R_or_C.re (inner v v) := norm_sq_eq_inner v,
  have h1 : is_R_or_C.re ((inner v v):ℝ) = ((inner v v) :ℝ) := by finish,
  rw [hn,h1],
  exact hh,
end

lemma compute_norm (v : euclidean_space ℝ (fin 3)) : ∥v∥ = real.sqrt (∑(i : fin 3), (v i)^2) :=
begin
  have hf : ∥v∥^2 = (∑(i : fin 3), (v i)^2) := compute_norm_aux v,
  have hfs : real.sqrt(∥v∥^2) = real.sqrt(∑(i : fin 3), (v i)^2) := congr_arg real.sqrt hf,

  have h1 : real.sqrt(∥v∥^2) = | ∥v∥ | := ∥v∥.sqrt_sq_eq_abs,
  have hp : 0 ≤ ∥v∥ := norm_nonneg v,
  have hh : | ∥v∥ | = ∥v∥ := abs_eq_self.mpr hp,

  rw[hh] at h1,
  rw[h1] at hfs,
  exact hfs,
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

  have hxf : (x-1)/x = 1 - 1/x := by field_simp,
  have hyf : (y-1)/y = 1 - 1/y := by field_simp,
  have hzf : (z-1)/z = 1 - 1/z := by field_simp,

  have h1 : (x-1)/x + (y-1)/y + (z-1)/z = 1,
  { rw[hxf, hyf, hzf],
    linarith },

  let v₁ := construct_vector (real.sqrt x) (real.sqrt y) (real.sqrt z),
  let v₂ := construct_vector (real.sqrt ((x - 1)/x)) (real.sqrt ((y-1)/y)) (real.sqrt ((z-1)/z)),

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
    have hxx : (real.sqrt x) ^ 2 = x,
    { have hx0 : 0 ≤ x := by linarith,
      exact real.sq_sqrt hx0},

    have hyy : (real.sqrt y) ^ 2 = y,
    { have hy0 : 0 ≤ y := by linarith,
      exact real.sq_sqrt hy0},

    have hzz : (real.sqrt z) ^ 2 = z,
    { have hz0 : 0 ≤ z := by linarith,
      exact real.sq_sqrt hz0},

    rwa [hxx, hyy, hzz] at hn},

  have hv₂ : ∥v₂∥ = 1,
  { have hn := compute_norm v₂,
    sorry },

  rw [hv₁, hv₂, mul_one] at cauchy_schwarz,
  sorry
end
