import data.int.modeq
import data.nat.basic
import data.pnat.basic
import data.nat.digits
import data.nat.gcd
import data.zmod.basic

lemma foo
  (base factor c d : ℕ)
  (h_coprime : nat.coprime factor base)
  (h_equal : base * c ≡ base * d [ZMOD factor])
  : c ≡ d [ZMOD factor] :=
begin
  have hd: (factor: ℤ) ∣ ((base: ℤ) * (d: ℤ)) - ((base: ℤ) * (c: ℤ)) := int.modeq.modeq_iff_dvd.mp h_equal,
  have hs: ((base: ℤ) * (d: ℤ)) - ((base: ℤ) * (c: ℤ)) = ((base: ℤ) * ( (d: ℤ) - (c: ℤ))),
  {
    exact (mul_sub ↑base ↑d ↑c).symm
  },
  rw hs at hd,
  apply int.modeq.modeq_iff_dvd.mpr,
  -- refine nat.coprime.dvd_of_dvd_mul_left h_coprime _,
  sorry,
end


-- let a, b, c, be natural numbers, with c < b, a and b coprime.
-- prove that there exists k > 0 such that c a^k = c mod b.
lemma periodic
  (base factor c : ℕ)
  (h_coprime: nat.gcd base factor = 1)
  : ∃k : ℕ+, (base^k.val) * c ≡ c [ZMOD factor] :=
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
