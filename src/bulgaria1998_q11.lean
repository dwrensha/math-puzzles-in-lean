import data.nat.basic
import data.nat.modeq
import algebra.group_power.basic
import algebra.parity

import tactic.ring

/-
Bulgarian Mathematical Olympiad 1998, Problem 11

Let m,n be natural numbers such that

   A = ((m + 3)ⁿ + 1) / (3m)

is an integer. Prove that A is odd.

-/

lemma mul_mod_lemma (a b c d : ℕ) (h : a % b = c % b) : (d * a) % b = (d * c) % b :=
begin
  rw [nat.mul_mod, nat.mul_mod d c b],
  exact congr (congr_arg has_mod.mod (congr_arg (has_mul.mul (d % b)) h)) rfl
end

lemma mod_plus_pow (m n : ℕ) : (m + 3)^n % 3 = m^n % 3 :=
begin
  induction n with pn hpn,
  { simp, },
  { rw[pow_succ],
    have h1 : (m + 3) * (m + 3) ^ pn = m * (m + 3) ^ pn + 3 * (m + 3) ^ pn := by ring,
    rw [h1],
    have h2 : 3 * (m + 3) ^ pn % 3 = 0 := nat.mul_mod_right 3 _,
    rw[nat.add_mod, h2, add_zero, nat.mod_mod, pow_succ],
    exact mul_mod_lemma _ _ _ _ hpn }
end

theorem bulgaria1998_q11 (m n A : ℕ) (h : 3 * m * A = (m + 3)^n + 1) :
  odd A :=
begin
  by_contra hno,
  sorry
end
