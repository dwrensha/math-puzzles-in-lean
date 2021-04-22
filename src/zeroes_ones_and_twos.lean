import data.int.modeq
import data.nat.basic
import data.nat.modeq
import data.pnat.basic
import data.nat.digits
import data.nat.gcd
import algebra.big_operators.pi

/-!
Let n be a natural number. Prove that

  (a) n has a (nonzero) multiple whose representation in base 10 contains
      only zeroes and ones; and
  (b) 2^n has a multiple whose representation contains only ones and twos.

-/

open_locale big_operators

def ones (b : ℕ) : ℕ → ℕ
| k := ∑(i : ℕ) in finset.range k, b^i

def map_mod (n : ℕ) (hn: 0 < n) (f : ℕ → ℕ) : ℕ → fin n
| m := ⟨f m % n, nat.mod_lt (f m) hn⟩

lemma pigeonhole (n : ℕ) (f : ℕ → fin n) :
  ∃ a b : ℕ, a ≠ b ∧ f a = f b :=
begin
  classical,
  by_contra hc,
  push_neg at hc,
  have hinj : function.injective f,
  { intros a b,
    contrapose,
    exact hc a b, },
  apply not_injective_infinite_fintype f hinj,
end

lemma pigeonhole' (n : ℕ) (f : ℕ → fin n) :
  ∃ a b : ℕ, a < b ∧ f a = f b :=
begin
  obtain ⟨a, b, hne, hfe⟩ := pigeonhole n f,
  obtain (ha : a < b) | (hb : b < a) := ne.lt_or_lt hne,
  { use a, use b, exact ⟨ha, hfe⟩},
  { use b, use a, exact ⟨hb, hfe.symm⟩},
end

@[simp]
def all_zero_or_one : list ℕ → Prop
| [] := true
| (0 :: ds) := all_zero_or_one ds
| (1 :: ds) := all_zero_or_one ds
| _ := false


lemma digits_lemma
  (base: ℕ)
  (h2: 2 ≤ base)
  (n: ℕ)
  (hn: 0 < n)
  : (nat.digits base (base * n)) = 0 :: (nat.digits base n) :=
begin
  have := nat.digits_add base h2 0 n (nat.lt_of_succ_lt (nat.succ_le_iff.mp h2)) (or.inr hn),
  rwa (zero_add (base * n)) at this,
end

lemma times_base_still_all_zero_or_one
  (base: ℕ)
  (h2: 2 ≤ base)
  (n: ℕ)
  (hn : all_zero_or_one (nat.digits base n))
  : all_zero_or_one (nat.digits base (base * n)) :=
begin
  cases (nat.eq_zero_or_pos n) with hz hp,
  {
    rw hz,
    simp only [mul_zero, nat.digits_zero]
  },

  rw (digits_lemma base h2 n hp),
  simpa,
end

lemma base_pow_still_all_zero_or_one
  (base: ℕ)
  (h2: 2 ≤ base)
  (k n: ℕ)
  (hn : all_zero_or_one (nat.digits base n))
  : all_zero_or_one (nat.digits base ((base ^ k) * n)) :=
begin
  induction k with pk hpk,
  { simpa },
  have := times_base_still_all_zero_or_one base h2 _ hpk,
  rwa [←(nat.add_one pk), pow_succ' base pk, mul_comm (base^pk) base, mul_assoc],
end

lemma lemma_1 (k b m: ℕ) :
  all_zero_or_one (b.digits (∑(i : ℕ) in finset.range k, b^(i + m))) :=
begin
  induction k with pk hpk,
  {simp},
  { -- should be straightfoward.
    -- factor out b^m...
    sorry
  },
end

lemma lemma_2
  (n : ℕ)
  (hn : n > 0)
  (a b : ℕ)
  (hlt : a < b)
  (hab : (finset.range a).sum (pow 10) % n = (finset.range b).sum (pow 10) % n) :
  (∑(i : ℕ) in finset.range (b - a), b^(i + a)) % n = 0 :=
begin
  sorry,
end

lemma lemma_3 {a n : ℕ} (hm : a % n = 0) : (∃ k : ℕ, a = n * k) :=
begin
  sorry
end

theorem zeroes_and_ones (n : ℕ) : ∃ k : ℕ+, all_zero_or_one (nat.digits 10 (n * k)) :=
begin
  have hn : n > 0,
  { sorry },
  obtain ⟨a, b, hlt, hab⟩ := pigeonhole' n (λm, map_mod n hn (ones 10) m),
  simp [map_mod, ones] at hab,
  have h' : (∑(i : ℕ) in finset.range (b - a), b^(i + a)) % n = 0 := lemma_2 n hn a b hlt hab,
  have := lemma_3 h',
  obtain ⟨k, hk⟩ := this,
  use k,
  sorry,
  sorry,
end

def all_one_or_two : list ℕ → Prop
| [] := true
| (1 :: ds) := all_one_or_two ds
| (2 :: ds) := all_one_or_two ds
| _ := false

theorem ones_and_twos (n : ℕ) : ∃ k : ℕ+, all_one_or_two (nat.digits 10 (2^n * k)) :=
begin
  sorry
end
