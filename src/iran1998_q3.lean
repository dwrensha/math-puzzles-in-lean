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

/- seems like there should be something like this in mathlib... -/

lemma prod_pow' (n : ℕ) (x : ℝ) (f : ℕ → ℝ) (hf : ∀ i < n, 0 ≤ f i)  :
(finset.range n).prod (λ (i : ℕ), f i ^ x) = (finset.range n).prod (λ (i : ℕ), f i) ^ x :=
begin
  suffices : 0 ≤ (finset.range n).prod (λ (i : ℕ), f i) ∧
    (finset.range n).prod (λ (i : ℕ), f i ^ x) = (finset.range n).prod (λ (i : ℕ), f i) ^ x,
  { exact this.2 },

  induction n with n' ih,
  { simp},
  { rw[finset.prod_range_succ, finset.prod_range_succ],
    have hp: ∀ (i : ℕ), i < n' → 0 ≤ f i,
    { intros i hi,
      exact hf i (nat.lt.step hi)},
    obtain ⟨hs0, hs⟩ := ih hp,
    rw [hs],
    split,
    { have : 0 ≤ f n' := hf n' (lt_add_one n'),
      exact mul_nonneg hs0 this},
    { clear ih hp hs,
      have : 0 ≤ f n' := hf n' (lt_add_one n'),
      exact (real.mul_rpow hs0 this).symm,
    },
  },
end

theorem iran1998_q3
  (x : ℕ → ℝ)
  (x_positive : ∀ i, 0 < x i)
  (h : ∏ (i : ℕ) in finset.range 4, x i = 1)
  : max (∑(i : ℕ) in finset.range 4, x i) (∑(i : ℕ) in finset.range 4, 1 / x i)
     ≤ ∑ (i : ℕ) in finset.range 4, (x i)^(3 : ℝ) :=
begin
  rw[max_le_iff],
  split,
  { have amgm' := real.geom_mean_le_arith_mean_weighted
                    (finset.range 4)
                    (λ ii, (1:ℝ)/4)
                    (λ ii, x ii)
                    (by {intros i hi, norm_num})
                    (by simp)
                    (by {intros j hj, exact le_of_lt (x_positive j) }),
    have x_pos' : ∀ i < 4, 0 ≤ x i := by { intros i _, exact le_of_lt (x_positive i) },
    rw[prod_pow' 4 (1/4) x x_pos', h, real.one_rpow] at amgm',
    dsimp at amgm',
    rw [←finset.mul_sum] at amgm',
    have xnonneg : ∀ i ∈ finset.range 4, 0 ≤ x i,
    { intros i _, exact le_of_lt (x_positive i)},
    let C := 1/4 * ∑ (i : ℕ) in finset.range 4, x i,
    have hcp' : 0 ≤ ∑ (i : ℕ) in finset.range 4, x i := finset.sum_nonneg xnonneg,
    have hcp : 0 ≤ C := mul_nonneg (by norm_num) hcp',
    have hccp : 0 ≤ C * C := mul_nonneg hcp hcp,

    have hCC : C * C * C = C ^(3:ℕ) := by ring_exp,
    rw[←real.rpow_nat_cast] at hCC,
    simp at hCC,

    have hC := calc C
                ≤ C * C : le_mul_of_one_le_left hcp amgm'
            ... ≤ C * C * C : le_mul_of_one_le_right hccp amgm'
            ... = C^(3 : ℝ) : hCC,

    have h13 : (1:ℝ) ≤ 3 := by norm_num,
    have holder := real.rpow_sum_le_const_mul_sum_rpow (finset.range 4) x h13,

    have habs : ∀ i ∈ finset.range 4, |x i| = x i,
    {intros i hi, exact abs_of_pos (x_positive i)},
    rw[finset.sum_congr rfl habs] at holder,

    have habs3 : ∀ i ∈ finset.range 4, |x i| ^ (3:ℝ) = x i ^ (3:ℝ),
    { intros i hi, have := habs i hi, exact congr_fun (congr_arg pow this) 3},
    rw[finset.sum_congr rfl habs3] at holder,
    have hccc: (4:ℝ) * C =  ∑ (i : ℕ) in finset.range 4, x i := by {field_simp[C], ring},
    rw[←hccc] at holder,

    have h4nn : (0:ℝ) ≤ 4 := by norm_num,
    rw[real.mul_rpow h4nn hcp] at holder,
    have h43nn : (0:ℝ) ≤ 4 ^ (3:ℝ) := by norm_num,
    have hcard' : (finset.range 4).card = 4 := by simp,
    rw[hcard'] at holder,
    have hss: C ^ (3:ℝ) ≤ ((1:ℝ) / 4) * ∑ (i : ℕ) in finset.range 4, x i ^ (3:ℝ),
    { ring_exp at holder,
      clear_except holder,
      have hknn : (0:ℝ) ≤ (4:ℝ) ^ (-3 : ℝ) := by norm_num,
      have hh := mul_le_mul_of_nonneg_left holder hknn,
      rw[←mul_assoc] at hh,
      have h4mm: (4:ℝ) ^ (-3: ℝ) * (4:ℝ) ^ (3:ℝ) = 1 := by norm_num,
      rw[h4mm, one_mul] at hh,
      rw[←mul_assoc] at hh,
      have hnc: ((4:ℕ) :ℝ) = (4:ℝ) := by norm_cast,
      rw[hnc] at hh,
      have h4mm': (4:ℝ) ^ (-3: ℝ) * (4:ℝ) ^ (2:ℝ) = 1/4 := by norm_num,
      rw[h4mm'] at hh,
      exact hh },
    have htrans := le_trans hC hss,
    have hm4 : 4 * C ≤ 4 * ((1/4) * ∑ (i : ℕ) in finset.range 4, x i ^ (3:ℝ)) :=
      mul_le_mul_of_nonneg_left htrans h4nn,
    have h4c: 4 * C = ∑ (i : ℕ) in finset.range 4, x i,
    { field_simp[C], ring },
    rw[h4c] at hm4,
    have hro : 4 * (1 / 4 * ∑ (i : ℕ) in finset.range 4, x i ^ (3:ℝ)) =
                    ∑ (i : ℕ) in finset.range 4, x i ^ (3:ℝ),
    { field_simp, ring },
    rw[hro] at hm4,
    exact hm4 },
  { let A := ∑ (i : ℕ) in finset.range 4, (x i)^(3:ℝ),
    let B : ℕ → ℝ := λ j, (∑ (i : ℕ) in (finset.range 4).erase j, (x i)^(3:ℝ)),
    have hab : A = (1/3) * (∑ (i : ℕ) in finset.range 4, B i),
    { simp[finset.sum_range_succ, A], ring },
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
      exact amgm },
    have h3 : ∀ j ∈ (finset.range 4), ∏ (i : ℕ) in (finset.range 4).erase j, x i = 1 / x j,
    { intros j hj,
      rw [←h],
      rw[←finset.prod_erase_mul _ _ hj],
      have : x j ≠ 0 := ne_of_gt (x_positive j),
      field_simp },
    have h4 : ∀ j ∈ finset.range 4, 1 / x j ≤ 1 / 3 * B j,
    { intros j hj,
      have h2j := h2 j hj,
      have h3j := h3 j hj,
      rwa[h3j] at h2j },
    have h5 : ∑ (i : ℕ) in finset.range 4, 1 / x i ≤ A,
    { have h5': ∑ (i : ℕ) in finset.range 4, 1 / x i ≤ ∑ (i : ℕ) in finset.range 4, (1 / 3) * B i,
      { exact finset.sum_le_sum h4 },
      rw [←finset.mul_sum] at h5',
      rwa [hab] },
    exact h5 }
end
