import data.int.modeq
import data.nat.basic
import data.pnat.basic
import data.nat.digits
import data.nat.gcd
import data.zmod.basic

-- let a, b, c, be natural numbers, with c < b, a and b coprime.
-- prove that there exists k > 0 such that c a^k = c mod b.
lemma foo
  (a b c : ℕ)
  (h_coprime: nat.gcd a b = 1)
  : ∃k:ℕ+, (a^k.val) * c ≡ c [ZMOD b] :=
begin
  sorry,
end


def all_zero_or_one : list ℕ → Prop
| [] := true
| (0 :: ds) := all_zero_or_one ds
| (1 :: ds) := all_zero_or_one ds
| _ := false

theorem part_one (n : ℕ) : ∃ k : ℕ+, all_zero_or_one (digits 10 (n * k)) :=
begin
  sorry
end
