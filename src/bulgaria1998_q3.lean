import data.real.basic

/-
Bulgarian Mathematical Olympiad 1998, Problem 3

Let ℝ⁺ be the set of positive real numbers. Prove that there does not exist a function
f: ℝ⁺ → ℝ⁺ such that

                (f(x))² ≥ f(x + y) * (f(x) + y)

for every x,y ∈ ℝ⁺.

-/

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
               ... = (f x) * (f x / (2 * f x))             : by rw [two_mul]
               ... = (f x) * (f x/ (2 * f x))             : by rw [two_mul]
               ... = (f x) * (1 /2 )                      : by rw [h7]
               ... = f x / 2                              : by field_simp,
  },

  sorry
end
