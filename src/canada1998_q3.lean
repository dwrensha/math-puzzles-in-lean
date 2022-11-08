import algebra.big_operators.pi
import data.real.basic

/-
Canadian Mathematical Olympiad 1998, Problem 3

Let n be a natural number such that n ≥ 2. Show that

  (1/(n + 1))(1 + 1/3 + ... + 1/(2n -1)) > (1/n)(1/2 + 1/4 + ... + 1/2n).
-/

open_locale big_operators

-- n' + 1 = n

theorem canada1998_q3 (n' : ℕ) (hn : 1 ≤ n') :
  ((1:ℝ)/(n'+2)) * ∑ (i:ℕ) in finset.range n', (1/(2 * n' + 1)) >
  ((1:ℝ)/(n'+1)) * ∑ (i:ℕ) in finset.range n', (1/(2 * n' + 2)) :=
begin
  cases n',
  { sorry, },
  clear hn,
  sorry
end
