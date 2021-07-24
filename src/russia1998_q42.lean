import data.real.basic

/-
 Russian Mathematical Olympiad 1998, problem 42

 A binary operation ⋆ on real numbers has the property that (a ⋆ b) ⋆ c = a + b + c.
 Prove that a ⋆ b = a + b.

-/

theorem russia1998_q42
  (star : ℝ → ℝ → ℝ)
  (stardef : ∀ a b c, star (star a b) c = a + b + c) :
  (∀ a b, star a b = a + b) :=
begin
  have lemma2 : ∀ a b d, star a b = star d b → a = d,
  { intros a b d hab,
    have := calc a + b + a = star (star a b) a : (stardef _ _ _).symm
                       ... = star (star d b) a : by rw [hab]
                       ... = d + b + a : stardef _ _ _,
    have : a + b = d + b := (add_left_inj a).mp this,
    have : a = d := (add_left_inj b).mp this,
    exact this },

  have lemma3 : ∀ a b, star a b = star b a,
  { intros a b,
    let d1 := star a b,
    let d2 := star b a,
    have h1 := calc star d1 1 = a + b + 1 : stardef _ _ _
                          ... = b + a + 1 : by rw [add_comm a b]
                          ... = star d2 1 : (stardef _ _ _).symm,

    exact lemma2 d1 1 d2 h1 },

  have lemma4 : ∀ a, star a 0 = a,
  { intro a,
    let x := star a 0,
    have h1 := calc star x 0 = a + 0 + 0 : stardef a 0 0
                         ... = a: by rw [add_zero, add_zero],

    have h2 := calc 2 * x = x + x : two_mul x
                      ... = x + 0 + x : by rw [add_zero]
                      ... = star (star x 0) x : (stardef _ _ _).symm
                      ... = star a x : by rw [h1]
                      ... = star x a : lemma3 _ _
                      ... = star (star a 0) a : rfl
                      ... = a + 0 + a : stardef _ _ _
                      ... = a + a : by rw [add_zero]
                      ... = 2 * a : (two_mul a).symm,

    have h3 : (2:ℝ) ≠ 0 := two_ne_zero,
    have h4 : x = a := (mul_right_inj' h3).mp h2,
    exact h4 },

  intros a b,

  have := calc a + b = a + b + 0 : by rw [add_zero]
                 ... = star (star a b) 0 : (stardef _ _ _).symm
                 ... = star a b : lemma4 _,

  exact this.symm
end
