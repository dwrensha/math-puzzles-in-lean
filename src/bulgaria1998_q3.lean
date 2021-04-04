import data.real.basic
import algebra.big_operators.pi
import analysis.specific_limits

/-
Bulgarian Mathematical Olympiad 1998, Problem 3

Let ℝ⁺ be the set of positive real numbers. Prove that there does not exist a function
f: ℝ⁺ → ℝ⁺ such that

                (f(x))² ≥ f(x + y) * (f(x) + y)

for every x,y ∈ ℝ⁺.

-/

open_locale big_operators

lemma geom_sum_bound (n:ℕ) : ∑(i : ℕ) in finset.range n, (1:ℝ) / (2^i) < 3 :=
begin
  calc ∑(i : ℕ) in finset.range n, (1:ℝ) / 2^i
          = ∑(i : ℕ) in finset.range n, (1 / 2)^i : by {congr; simp [div_eq_mul_inv]}
      ... ≤ 2 : sum_geometric_two_le n
      ... < 3 : by norm_num,
end

theorem bulgaria1998_q3
  (f: ℝ → ℝ)
  (hpos : ∀ x : ℝ, 0 < x → 0 < f x)
  (hf : (∀x y : ℝ, 0 < x → 0 < y → (f (x + y)) * (f x + y) ≤ (f x)^2)) :
  false :=
begin
  have f_decr : ∀ x y : ℝ, 0 < x → 0 < y → f (x + y) < f x,
  {
    intros x y hx hy,
    have h0 := hpos x hx,
    have h1 := hf x y hx hy,
    have h2 : 0 < f x + y := by linarith,
    have h3 : 0 ≠ f x + y := by linarith,
    have h4 : f x < f x + y := lt_add_of_pos_right (f x) hy,
    have h5 : f x / (f x + y) < 1 := by rwa [div_lt_iff h2, one_mul],
    calc f (x + y) = f (x + y) * 1                       : (mul_one (f (x + y))).symm
               ... = f (x + y) * ((f x + y) / (f x + y)) : by rw (div_self (ne.symm h3))
               ... = (f (x + y) * (f x + y)) / (f x + y) : mul_div_assoc' (f (x + y)) (f x + y) (f x + y)
               ... ≤ (f x)^2 / (f x + y)                 : (div_le_div_right h2).mpr h1
               ... = (f x) * (f x / (f x + y))           : by field_simp [pow_two]
               ... < f x                                 : (mul_lt_iff_lt_one_right (hpos x hx)).mpr h5,
  },
  have f_half : ∀ x : ℝ, 0 < x → f (x + f x) ≤ f x / 2,
  {
    intros x hx,
    have h0 := hpos x hx,
    have h1 := hf x (f x) hx h0,
    have h2 : 0 < f x + f x := by linarith,
    have h3 : 0 ≠ f x + f x := by linarith,
    have h5 := ne_of_lt h0,
    have h6: 2 * f x ≠ 0 := by linarith,
    have h7 : (f x/ (2 * f x)) = 1 / 2 := by { rw [div_eq_iff h6], ring },

    calc f (x + f x) = f (x + f x) * 1                   : (mul_one _).symm
               ... = f (x + f x) * ((f x + f x) / (f x + f x)) : by rw (div_self (ne.symm h3))
               ... = (f (x + f x) * (f x + f x)) / (f x + f x) : mul_div_assoc' _ _ _
               ... ≤ (f x)^2 / (f x + f x)                 : (div_le_div_right h2).mpr h1
               ... = (f x) * (f x / (f x + f x))           : by field_simp [pow_two]
               ... = (f x) * (f x/ (2 * f x))             : by rw [two_mul]
               ... = (f x) * (1 /2 )                      : by rw [h7]
               ... = f x / 2                              : by field_simp,
  },

  let x_seq : ℕ → ℝ := λ n : ℕ, 1 + ∑(i : ℕ) in finset.range n, (f 1) / (2^i),

  have hz : x_seq 0 = 1 := by simp only [add_right_eq_self, finset.sum_empty, finset.range_zero],

  have f_x_seq: ∀ n:ℕ, f(x_seq n) ≤ f 1 / 2^n,
  { intro n,
    induction n with pn hpn,
    { rw hz, simp only [div_one, pow_zero],},
    sorry,
  },

  have x_seq_pos : ∀ n: ℕ, 0 < x_seq n,
  { intro n,
    simp only [x_seq],

    have sum_nonneg : 0 ≤ ∑ (i : ℕ) in finset.range n, f 1 / 2 ^ i,
    { apply finset.sum_nonneg,
      intros i hi,
      have h1 := hpos 1 zero_lt_one,
      have h2 : (0:ℝ) < 2 ^ i := pow_pos (by norm_num) i,
      exact le_of_lt (div_pos_iff.mpr (or.inl ⟨h1, h2⟩)),
    },
    linarith,
  },

  have h1: ∀ n: ℕ, x_seq n < 1 + 3 * f 1,
  { sorry},

  have h2 : ∀ n : ℕ, 0 < 1 + 3 * f 1 - x_seq n,
  { intro n, linarith [h1 n]},

  have : ∀ n:ℕ, f (1 + 3 * f 1) < f 1 / 2 ^ n,
  { intro n,
    calc f (1 + 3 * f 1) = f (x_seq n + (1 + 3 * f 1 - x_seq n)) : by ring_nf
                     ... < f (x_seq n) : f_decr (x_seq n) _ (x_seq_pos n) (h2 n)
                     ... ≤ f 1 / 2^n : f_x_seq n,
  },

  have nonpos : f ( 1 + 3 * f 1) ≤ 0,
  { sorry, },

  have := hpos (1 + 3 * f 1) (by linarith [hpos 1 zero_lt_one]),
  linarith,
end
