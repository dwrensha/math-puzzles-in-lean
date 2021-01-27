import data.finset.basic
import data.nat.basic

import algebra.big_operators

open_locale big_operators

/-!
# IMO 2018 Q3

An anti-Pascal triangle is an equilateral triangular array of numbers such that,
except for the numbers in the bottom row, each number is the absolute value
of the difference of the two numbers immediately below it. For example,
the following array is an anti-Pascal triangle with four rows
which contains every integer from 1 to 10:

                  4
                2   6
              5   7   1
            8   3  10   9

Does there exist an anti-Pascal triangle with 2018 rows which contains every
integer from 1 to 1 + 2 + ... + 2018?

# Solution
No.

-/


theorem imo2018_q3 (f : ℕ → ℕ → ℕ)
  (h_antipascal : ∀ r < 2017, ∀ c < r,
      f r c + f r.succ c = f r.succ c.succ ∨
      f r c + f r.succ c.succ = f r.succ c)
  (h_contains_all : ∀ n ≤ (∑(i:ℕ) in finset.range 2018, i + 1),
    ∃ r < 2018, ∃ c < r, f r c = n) :
  false :=
begin
sorry
end
