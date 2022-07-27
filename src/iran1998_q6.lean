import data.nat.basic
import data.nat.gcd
import data.nat.pow

import algebra.associated
import algebra.group_power.basic


/-
Iranian Mathematical Olympiad 1998, Problem 6

Let x,a,b be positive integers such that x^(a+b) = a^b * b. Prove
that a = x and b = x^x.
-/

theorem iran1998_q6
  (x a b : ℕ)
  (hx : 0 < x)
  (ha : 0 < a)
  (hb : 0 < b)
  (h : x^(a+b) = a^b * b)
 : a = x ∧ b = x^x :=
begin
  cases x,
  { exact false.elim (nat.lt_asymm hx hx) },
  cases x,
  { rw [one_pow] at h,
    have hab : 1 ≤ a ^ b := nat.one_le_pow b a ha,
    have habb : a ^ b ≤ a ^ b * b := nat.le_mul_of_pos_right hb,
    rw [←h] at habb,
    have hab' : a ^ b = 1 := le_antisymm habb hab,
    rw [hab', one_mul, eq_comm] at h,
    rw[one_pow],
    rw [h, pow_one] at hab',
    exact ⟨hab', h⟩ },
  let x' := x.succ.succ,
  have : ∀ p : ℕ, prime p → p ∣ x → p ∣ b,
  { intros p hpp hpx,
    sorry },
  sorry
end
