import algebra.big_operators.pi
import data.rat.defs


/-!
Given a natural number n > 1, add up all the fractions 1 / (p ⬝ q), where
p and q are relatively prime, 0 < p < q ≤ n, and p + q > n. Prove that
the result is always 1/2.
-/

open_locale big_operators

theorem summing_fractions (n : ℕ) (hn : 1 < n) :
   (∑(p : ℕ) in finset.range n.succ, ∑(q : ℕ) in finset.range n.succ,
     if p < q ∧ n < p + q ∧ nat.coprime p q
     then rat.inv (p * q)
     else 0) = 1/2 :=
begin
  sorry
end
