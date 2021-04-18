import data.nat.basic
import data.int.basic


/-
Polish Mathematical Olympiad 1998, Problem 4

Prove that the sequence {a_n} defined by a_1 = 1 and

     a_n = a_{n - 1} + a_{⌊n/2⌋}        n = 2,3,4,...

contains infinitely many integers divisible by 7.

-/

theorem poland1998_q4
  (a : ℤ → ℤ)
  (h1 : a 1 = 1)
  (ha : ∀ n : ℤ, 2 ≤ n → a n = a (n - 1) + a (n / 2)) :
  (∀ N : ℤ, ∃ M : ℤ, N ≤ M ∧ 7 ∣ a M) :=
begin
  sorry
end
