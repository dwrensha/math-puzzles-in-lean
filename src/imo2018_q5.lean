import data.int.basic
import data.int.gcd
import data.pnat.basic
import data.rat.defs

import algebra.big_operators.basic
import ring_theory.coprime.basic

import tactic.field_simp
import tactic.linarith
import tactic.ring

/-
IMO 2018 Q5

Let a₁, a₂, ..., aₙ, ... be a sequence of positive integers such that

      a₁/a₂ + a₂/a₃ + ... + aₙ₋₁/aₙ + aₙ/a₁

is an integer for all n ≥ k, where k is some positive integer.

Prove that there exists a positive integer m such that aₙ = aₙ₊₁
for all n ≥ m.

-/

open_locale big_operators

lemma gcd_dvd (a b c : ℤ)
  (hgcd : a.gcd c = 1)
  (h_cab : c ∣ a * b) :
  c ∣ b :=
begin
  have : is_coprime c a,
  {
    have h1 := int.gcd_eq_gcd_ab a c,
    rw hgcd at h1,
    simp at h1,
    rw add_comm at h1,
    use a.gcd_b c,
    use a.gcd_a c,
    linarith,
  },
  exact is_coprime.dvd_of_dvd_mul_left this h_cab,
end

/-
 Let a,b,c be positive integers such that N = b/c + (c-b)/a is an integer. Then:
  (1) if gcd(a,c) = 1, then c divides b
-/
lemma lemma_1
  (a b c : ℤ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (N : ℤ)
  (hN : (b:ℚ)/(c:ℚ) + ((c:ℚ) - (b:ℚ)) / (a:ℚ) = N)
  (hgcd : int.gcd a c = 1) :
  c∣b :=
begin
  /-
   Write a*b = c*(a*N + b - c). Since gcd(a,c) = 1, it follows that c divides b.
  -/
  have : (a:ℚ) * b = c * (a * N + b - c),
  {
    have ha0 : (a:ℚ) ≠ 0 := ne_of_gt (int.cast_pos.mpr ha),
    have hc0 : (c:ℚ) ≠ 0 := ne_of_gt (int.cast_pos.mpr hc),

    have h2: (a:ℚ) * (c:ℚ) * ((b:ℚ)/(c:ℚ) + ((c:ℚ) - (b:ℚ)) / (a:ℚ))
      = (a:ℚ) * (c:ℚ) * N := congr_arg (has_mul.mul (↑a * ↑c)) hN,

    have : (a:ℚ) * (c:ℚ) * ((b:ℚ)/(c:ℚ) + ((c:ℚ) - (b:ℚ)) / (a:ℚ))
     = (a:ℚ) * (b:ℚ) + (c:ℚ) * ((c:ℚ) - (b:ℚ)) := by {field_simp, ring},

    linarith,
  },

  have hz: a * b = c * (a * N + b - c),
  {
    assumption_mod_cast,
  },

  clear this,
  have h_cab : c ∣ a * b := dvd.intro (a * N + b - c) (eq.symm hz),

  clear hz hN N,

  exact gcd_dvd a b c hgcd h_cab,
end

/-
 Let a,b,c be positive integers such that N = b/c + (c-b)/a is an integer. Then:
  (2) if gcd(a,b,c) = 1, then gcd(a,b) = 1
-/
lemma lemma_2
  (a b c : ℤ)
  (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (N : ℤ)
  (hN : (b:ℚ)/(c:ℚ) + ((c:ℚ) - (b:ℚ)) / (a:ℚ) = N)
  (hgcd : int.gcd a (int.gcd b c) = 1) :
  int.gcd a b = 1 :=
begin
  have : (c:ℚ) * c - b * c = a * (c * N - b),
  {
    have ha0 : (a:ℚ) ≠ 0 := ne_of_gt (int.cast_pos.mpr ha),
    have hc0 : (c:ℚ) ≠ 0 := ne_of_gt (int.cast_pos.mpr hc),

    have h2: (a:ℚ) * (c:ℚ) * ((b:ℚ)/(c:ℚ) + ((c:ℚ) - (b:ℚ)) / (a:ℚ))
      = (a:ℚ) * (c:ℚ) * N := congr_arg (has_mul.mul (↑a * ↑c)) hN,

    have : (a:ℚ) * (c:ℚ) * ((b:ℚ)/(c:ℚ) + ((c:ℚ) - (b:ℚ)) / (a:ℚ))
     = (a:ℚ) * (b:ℚ) + (c:ℚ) * ((c:ℚ) - (b:ℚ)) := by {field_simp, ring},

    linarith,
   },

  have hz: c * c - b * c = a * (c * N - b) := by assumption_mod_cast,
  clear this,
  have h1 : a ∣ (c * c - b * c) := dvd.intro (c * N - b) (eq.symm hz),
  have h1' : ((a.gcd b):ℤ) ∣ a := int.gcd_dvd_left a b,
  have h2 : ((a.gcd b):ℤ) ∣ (c * c - b * c) := dvd_trans h1' h1,
  have h3 : ((a.gcd b):ℤ) ∣ b := int.gcd_dvd_right a b,
  have h4 : ((a.gcd b):ℤ) ∣ b * c := dvd_mul_of_dvd_left h3 c,
  have h5 : ((a.gcd b):ℤ) ∣ c * c := (dvd_iff_dvd_of_dvd_sub h2).mpr h4,

  rw[←int.gcd_assoc] at hgcd,
  sorry
end

theorem imo2018_q5
  (a: ℕ → ℕ+)
  (ha: ∃k : ℕ,
       ∀n : ℕ,
       k ≤ n →
        (∑ (i : ℕ) in finset.range n, ((a i):ℚ) / ((a ((i+1) % n)):ℚ)).denom = 1) :
  (∃m : ℕ, ∀ n : ℕ, m ≤ n → a n = a (n+1)) :=
begin
  sorry
end
