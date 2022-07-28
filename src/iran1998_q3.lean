import data.real.basic

import analysis.mean_inequalities

open_locale big_operators

/-
Iranian Mathematical Olympiad 1998, problem 3

Let x₁, x₂, x₃, x₄ be positive real numbers such that

  x₁ ⬝ x₂ ⬝ x₃ ⬝ x₄ = 1.

Prove that
  x₁³ + x₂³ + x₃³ + x₄³ ≥ max(x₁ + x₂ + x₃ + x₄, 1/x₁ + 1/x₂ + 1/x₃ + 1/x₄).

-/

lemma cube_root_cube (x : ℝ) (h: 0 ≤ x): (x^(3:ℝ)) ^ ((1:ℝ)/3) = x :=
begin
  rw[←real.rpow_mul h],
  have : 3 * ((1:ℝ)/3) = 1 := by norm_num,
  rw[this],
  exact real.rpow_one x,
end

theorem iran1998_q3
  (x : ℕ → ℝ)
  (x_positive : ∀ i, 0 < x i)
  (h : ∏ (i : ℕ) in finset.range 4, x i = 1)
  : max (∑(i : ℕ) in finset.range 4, x i) (∑(i : ℕ) in finset.range 4, 1 / x i)
     ≤ ∑ (i : ℕ) in finset.range 4, (x i)^(3 : ℝ) :=
begin
  let A := ∑ (i : ℕ) in finset.range 4, (x i)^(3:ℝ),
  let B : ℕ → ℝ := λ j, (∑ (i : ℕ) in (finset.range 4).erase j, (x i)^(3:ℝ)),
  have hab : A = (1/3) * (∑ (i : ℕ) in finset.range 4, B i),
  { simp[finset.sum_range_succ, A],
    ring },
  have h2 : ∀ j ∈ (finset.range 4), ∏ (i : ℕ) in (finset.range 4).erase j, x i ≤ (1/3) * B j,
  { intros j hj,
    have hcard1: (finset.range 4).card = 4 := finset.card_range 4,
    have hcard: ((finset.range 4).erase j).card = (finset.range 4).card - 1 :=
      finset.card_erase_of_mem hj,
    rw[hcard1] at hcard,
    norm_num at hcard,

    have amgm := real.geom_mean_le_arith_mean_weighted
                  ((finset.range 4).erase j)
                  (λ ii, (1:ℝ)/3)
                  (λ ii, x ii ^ (3:ℝ))
                  (by { intros i hi, simp, norm_num})
                  (by { simp[finset.sum_range_succ, hcard]})
                  (by {intros i _,
                       exact real.rpow_nonneg_of_nonneg (le_of_lt (x_positive i)) 3}),
    have hr : ∀ i ∈ ((finset.range 4).erase j),
                 (λ (ii : ℕ), x ii ^ (3:ℝ)) i ^ (λ (ii : ℕ), (1:ℝ) / 3) i = x i,
    { intros i _, exact cube_root_cube _ (le_of_lt (x_positive i)) },
    rw [finset.prod_congr rfl hr] at amgm,
    have hs : ∀ i ∈ ((finset.range 4).erase j),
      (λ (ii : ℕ), (1:ℝ) / 3) i * (λ (ii : ℕ), x ii ^ (3:ℝ)) i =
       ((1:ℝ)/3) * x i ^ (3:ℝ) := by simp,
    have := finset.sum_congr rfl hs,
    rw [finset.sum_congr rfl hs] at amgm,
    rw [←finset.mul_sum] at amgm,
    have hrfl : (λ (j : ℕ), ∑ (i : ℕ) in (finset.range 4).erase j, x i ^ (3:ℝ)) j =
                  ∑ (i : ℕ) in (finset.range 4).erase j, x i ^ (3:ℝ) := rfl,
    rw [←hrfl] at amgm,
    exact amgm,
  },
  have h3 : ∀ j ∈ (finset.range 4), ∏ (i : ℕ) in (finset.range 4).erase j, x i = 1 / x j,
  { intros j hj,
    rw [←h],
    rw[←finset.prod_erase_mul _ _ hj],
    have : x j ≠ 0 := ne_of_gt (x_positive j),
    field_simp },
  sorry
end
