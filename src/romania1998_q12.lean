import data.rat.basic
import data.real.basic
import data.complex.exponential

/-
Romanian Mathematical Olympiad 1998, Problem 12

Find all functions u : ℝ → ℝ for which there exists a strictly monotonic
function f : ℝ → ℝ such that

  ∀ x,y ∈ ℝ, f(x + y) = f(x)u(y) + f(y)

-/

lemma extend_function
   (f₁ : ℝ → ℝ)
   (f₂ : ℝ → ℝ)
   (h_cont : continuous f₁)
   (h_mono : monotone f₂)
   (h : ∀ x : ℚ, f₁ x = f₂ x) :
   ∀ x : ℝ, f₁ x = f₂ x :=
begin
  -- suppose not.
  by_contra hn,
  push_neg at hn,

  -- then there is y such that f₁ y ≠ f₂ y
  obtain ⟨y, hy⟩ := hn,

  let ε: ℝ := |f₁ y - f₂ y|,

  -- then find a δ such that for all z, |z-y| < δ implies that
  -- |f₁ z - f₁ y| < ε.
  sorry,
end

lemma exp_strict_mono' (k x y : ℝ) (hkp: 0 < k) (h : x < y) :
  real.exp(k * x) < real.exp(k * y) :=
begin
  finish,
end

lemma exp_strict_anti' (k x y : ℝ) (hkp: k < 0) (h : x < y) :
  real.exp(k * y) < real.exp(k * x) :=
begin
  finish
end

lemma romania1998_q12_mp (u : ℝ → ℝ) :
    (∃ f : ℝ → ℝ, (strict_mono f ∨ strict_anti f)
        ∧ ∀ x y : ℝ, f (x + y) = f x * u y + f y) →
    (∃ k : ℝ, ∀ x : ℝ, u x = real.exp (k * x)) :=
begin
  intro h,
  obtain ⟨f, hf⟩ := h,
  sorry,
end

lemma romania1998_q12_mpr (u : ℝ → ℝ) :
 (∃ k : ℝ, ∀ x : ℝ, u x = real.exp (k * x)) →
    (∃ f : ℝ → ℝ, (strict_mono f ∨ strict_anti f)
        ∧ ∀ x y : ℝ, f (x + y) = f x * u y + f y)
     :=
begin
  intro h,
  obtain ⟨k, hk⟩ := h,
  cases classical.em (k = 0) with hkz hknz,
  { -- k = 0
    use id,
    split,
    { left, exact strict_mono_id},
    { intros x y,
      rw [hk y, hkz, zero_mul, real.exp_zero],
      simp },
   },
   { -- k ≠ 0
     let f : ℝ → ℝ := λ x, real.exp (k * x) - 1,
     have hfm : (strict_mono f ∨ strict_anti f),
     { cases classical.em (0 < k) with hkp hkn,
       { left,
         intros x y hxy,
         have := exp_strict_mono' k x y hkp hxy,
         exact sub_lt_sub_right this 1 },
       { right,
         intros x y hxy,
         have hkn' : k < 0, {
              simp only [not_lt] at *,
              exact ne.lt_of_le hknz hkn,
         },
         have := exp_strict_anti' k x y hkn' hxy,
         exact sub_lt_sub_right this 1 }
     },
     use f,
     use hfm,
     intros x y,
     rw [hk y],
     calc real.exp (k * (x + y)) - 1
             = real.exp (k * x + k * y) - 1 : by {rw[mul_add]}
         ... = real.exp (k * x) * real.exp (k * y) - 1 : by {rw[real.exp_add]}
         ... = (real.exp (k * x) - 1) * real.exp (k * y) +
                  (real.exp (k * y) - 1) : by ring
   }
end

theorem romania1998_q12 (u : ℝ → ℝ) :
  (∃ f : ℝ → ℝ, (strict_mono f ∨ strict_anti f)
        ∧ ∀ x y : ℝ, f (x + y) = f x * u y + f y) ↔
  (∃ k : ℝ, ∀ x : ℝ, u x = real.exp (k * x)) :=
⟨romania1998_q12_mp u, romania1998_q12_mpr u⟩
