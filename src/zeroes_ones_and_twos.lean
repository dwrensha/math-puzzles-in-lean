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

lemma times_base_plus_one_still_all_zero_or_one
  (base: ℕ)
  (h2: 2 ≤ base)
  (n: ℕ)
  (hazoo : all_zero_or_one (nat.digits base n))
  : all_zero_or_one (nat.digits base (1 + base * n)) :=
begin
  rw (nat.digits_add base h2 1 n (nat.succ_le_iff.mp h2) (or.inl nat.one_pos)),
  simpa,
end

lemma lemma_0 (k b : ℕ) (h2 : 2 ≤ b) :
  all_zero_or_one (b.digits (∑(i : ℕ) in finset.range k, b^i)) :=
begin
  -- might also need to assume that b ≥ 2.
  induction k with pk hpk,
  { simp },
  { have hh := calc
          ∑ (i : ℕ) in finset.range pk.succ, b ^ i
        = b ^ 0 + ∑ (i : ℕ) in finset.range pk, b ^ i.succ : sorry
    ... = 1 + ∑ (i : ℕ) in finset.range pk, b ^ i.succ : by rw pow_zero
    ... =  1 + b * ∑ (i : ℕ) in finset.range pk, b ^ i : sorry,
    have := times_base_plus_one_still_all_zero_or_one
               b h2
               (∑ (i : ℕ) in finset.range pk, b ^ i) hpk,
    rwa hh,
  },
end

lemma lemma_1 (k b m: ℕ) :
  all_zero_or_one (b.digits (∑(i : ℕ) in finset.range k, b^(i + m))) :=
begin
  have h := calc
          (∑ (i : ℕ) in finset.range k, b ^ (i + m))
        = (∑ (i : ℕ) in finset.range k, b ^ i * b ^ m) :
             by { refine finset.sum_congr rfl _, intros x hx, exact pow_add b x m }
    ... = (∑ (i : ℕ) in finset.range k, b ^ m * b ^ i) :
             by { refine finset.sum_congr rfl _, intros x hx, exact mul_comm (b ^ x) (b ^ m) }
    ... = b^m * (∑ (i : ℕ) in finset.range k, b ^ i) :
             finset.sum_hom _ (has_mul.mul (b ^ m)),

  have h2 : 2 ≤ b := sorry, -- will need this as hypothesis

  have := base_pow_still_all_zero_or_one b h2 m
                       (∑ (i : ℕ) in finset.range k, b ^ i)
                       (lemma_0 k b h2),
  rwa h,
end

lemma lemma_2'''
  (c d : ℕ)
  (f: ℕ → ℕ) :
  (∑(i : ℕ) in finset.range c, f (i + d)) + (∑(i : ℕ) in finset.range d, f i)  =
     ∑(i : ℕ) in finset.range (c+d), f i :=
begin
  induction c with pc hpc,
  { simp },
  { have h1 : ∑ (i : ℕ) in finset.range pc.succ, f (i + d) =
              ∑ (i : ℕ) in finset.range pc, f (i + d) + f (pc + d) :=
         finset.sum_range_succ (λ (x : ℕ), f (x + d)) pc,

    have h2 := calc
          ∑ (i : ℕ) in finset.range (pc.succ + d), f i
        = ∑ (i : ℕ) in finset.range (pc + d).succ, f i : by rw nat.succ_add
    ... = ∑ (i : ℕ) in finset.range (pc + d), f i + f(pc + d) : finset.sum_range_succ f _,

    linarith
  },
end

lemma lemma_2''
  (a b : ℕ)
  (hlt : a < b)
  (f: ℕ → ℕ) :
  (∑(i : ℕ) in finset.range (b - a), f (i + a)) + (∑(i : ℕ) in finset.range a, f i)  =
     ∑(i : ℕ) in finset.range b, f i :=
begin
  have := lemma_2''' (b - a) a f,
  rwa [nat.sub_add_cancel (le_of_lt hlt)] at this,
end

lemma lemma_2'
  (a b : ℕ)
  (hlt : a < b) :
  (∑(i : ℕ) in finset.range (b - a), 10^(i + a)) + (∑(i : ℕ) in finset.range a, 10^i)  =
     ∑(i : ℕ) in finset.range b, 10^i :=
begin
  exact lemma_2'' a b hlt (λi, 10^i),
end

lemma lemma_2
  (n : ℕ)
  (hn : n > 0)
  (a b : ℕ)
  (hlt : a < b)
  (hab : ((finset.range a).sum (pow 10)) % n = ((finset.range b).sum (pow 10)) % n) :
  (∑(i : ℕ) in finset.range (b - a), 10^(i + a)) % n = 0 :=
begin
  sorry,
end

lemma lemma_3 {a n : ℕ} (ha: 0 < a) (hm : a % n = 0) : (∃ k : ℕ+, a = n * k) :=
begin
  have h2 : n ∣ a := nat.dvd_of_mod_eq_zero hm,
  obtain ⟨k', hk'⟩ := exists_eq_mul_right_of_dvd h2,
  have hkp : 0 < k',
  {
    cases k',
    { rw hk' at ha,
      rwa mul_zero at ha },
    { exact nat.succ_pos k' }
  },
  use ⟨k', hkp⟩,
  simpa [hkp],
end

lemma lemma_4 {k : ℕ} (hk : 0 < k) (f: ℕ → ℕ) (hf: ∀ i, 0 < f i) :
      0 < ∑(i : ℕ) in finset.range k, f i :=
begin
  sorry
end

theorem zeroes_and_ones (n : ℕ) : ∃ k : ℕ+, all_zero_or_one (nat.digits 10 (n * k)) :=
begin
  have hn : n > 0,
  { sorry },
  obtain ⟨a, b, hlt, hab⟩ := pigeonhole' n (λm, map_mod n hn (ones 10) m),
  simp [map_mod, ones] at hab,
  have h' : (∑(i : ℕ) in finset.range (b - a), 10^(i + a)) % n = 0 := lemma_2 n hn a b hlt hab,
  have ha: 0 < ∑(i : ℕ) in finset.range (b - a), 10^(i + a),
  { have hm : 0 < b - a := nat.sub_pos_of_lt hlt,
    have hp : ∀ j:ℕ, 0 < 10 ^ (j+a) := sorry,
    exact lemma_4 hm (λ (i : ℕ), 10 ^ (i + a)) hp,
  },
  obtain ⟨k, hk⟩ := lemma_3 ha h',
  use k,
  rw [←hk],
  exact lemma_1 (b - a) 10 a
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
