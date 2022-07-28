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

theorem iran1998_q3
  (x : ℕ → ℝ)
  (x_positive : ∀ i, 0 < x i)
  (h : ∏ (i : ℕ) in finset.range 4, x i = 1)
  : max (∑(i : ℕ) in finset.range 4, x i) (∑(i : ℕ) in finset.range 4, 1 / x i)
     ≤ ∑ (i : ℕ) in finset.range 4, (x i)^3 :=
begin
  let A := ∑ (i : ℕ) in finset.range 4, (x i)^3,
  let B : ℕ → ℝ := λ j, (∑ (i : ℕ) in (finset.range 4).erase j, (x i)^3),
  have hab : A = (1/3) * (∑ (i : ℕ) in finset.range 4, B i),
  { simp[finset.sum_range_succ, A],
    ring },
  have : ∀ j ∈ (finset.range 4), ∏ (i : ℕ) in (finset.range 4).erase j, x i ≤ (1/3) * B j,
  { intros j hj,
    have hcard1: (finset.range 4).card = 4 := finset.card_range 4,
    have hcard: ((finset.range 4).erase j).card = (finset.range 4).card - 1 :=
      finset.card_erase_of_mem hj,
    rw[hcard1] at hcard,
    norm_num at hcard,

    have amgm := real.geom_mean_le_arith_mean_weighted
                  ((finset.range 4).erase j)
                  (λ ii, 1/3)
                  (λ ii, x ii ^ 3)
                  (by { intros i hi, simp, norm_num})
                  (by { simp[finset.sum_range_succ, hcard]})
                  (by {intros i _, simp, exact le_of_lt (x_positive i)}),
    sorry
  },
  sorry
end
