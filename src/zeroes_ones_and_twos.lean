import data.int.modeq
import data.nat.basic
import data.nat.modeq
import data.pnat.basic
import data.nat.digits
import data.nat.gcd
import algebra.big_operators.pi
import algebra.big_operators.ring

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
  { rw hz,
    simp only [mul_zero, nat.digits_zero] },
  { rw (digits_lemma base h2 n hp),
    simpa }
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
  induction k with pk hpk,
  { simp },
  { have hh := calc
          ∑ (i : ℕ) in finset.range pk.succ, b ^ i
        = ∑ (i : ℕ) in finset.range pk, b ^ i.succ + b ^ 0 :
               finset.sum_range_succ' (λ (i : ℕ), b ^ i) pk
    ... = b ^ 0 + ∑ (i : ℕ) in finset.range pk, b ^ i.succ : add_comm _ _
    ... = 1 + ∑ (i : ℕ) in finset.range pk, b ^ i.succ : by rw pow_zero
    ... = 1 + ∑ (i : ℕ) in finset.range pk, b * b ^ i :
          by {simp, exact finset.sum_congr rfl (λx _, pow_succ _ _)}
    ... =  1 + b * ∑ (i : ℕ) in finset.range pk, b ^ i :
          by simp [finset.mul_sum],
    have := times_base_plus_one_still_all_zero_or_one
               b h2
               (∑ (i : ℕ) in finset.range pk, b ^ i) hpk,
    rwa hh,
  },
end

lemma lemma_1 (k b m: ℕ) (h2 : 2 ≤ b):
  all_zero_or_one (b.digits (∑(i : ℕ) in finset.range k, b^(i + m))) :=
begin
  have h := calc
          (∑ (i : ℕ) in finset.range k, b ^ (i + m))
        = (∑ (i : ℕ) in finset.range k, b ^ i * b ^ m) :
             by { refine finset.sum_congr rfl _, intros x hx, exact pow_add b x m }
    ... = (∑ (i : ℕ) in finset.range k, b ^ m * b ^ i) :
             by { refine finset.sum_congr rfl _, intros x hx, exact mul_comm (b ^ x) (b ^ m) }
    ... = b^m * (∑ (i : ℕ) in finset.range k, b ^ i) : finset.mul_sum.symm,

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

lemma lemma_2_aux (n a b c: ℕ) (hc : a + b = c) (hab: a % n = c % n) : b % n = 0 :=
begin
  have h1: a ≡ c [MOD n] := hab,
  have h2 : a + b ≡ c + b [MOD n] := nat.modeq.add h1 rfl,
  rw hc at h2,
  have h2' : c + 0 = c := self_eq_add_right.mpr rfl,
  have h2'' : c + 0 ≡ c + b [MOD n] := by rwa h2',
  have h3 : 0 ≡ b [MOD n] := nat.modeq.add_left_cancel' c h2'',
  have h4 : 0 % n = b % n := h3,
  rw [nat.zero_mod] at h4,
  exact eq.symm h4,
end

lemma lemma_2
  (n : ℕ)
  (hn : n > 0)
  (a b : ℕ)
  (hlt : a < b)
  (hab : (∑(i : ℕ) in finset.range a, 10^i) % n = (∑(i : ℕ) in finset.range b, 10^i) % n) :
  (∑(i : ℕ) in finset.range (b - a), 10^(i + a)) % n = 0 :=
begin
  have h1 := lemma_2' a b hlt,
  refine lemma_2_aux n _ (∑(i : ℕ) in finset.range (b - a), 10^(i + a)) _ _ hab,
  rwa add_comm,
end

lemma lemma_3 {a n : ℕ} (ha: 0 < a) (hm : a % n = 0) : (∃ k : ℕ+, a = n * k) :=
begin
  have h2 : n ∣ a := nat.dvd_of_mod_eq_zero hm,
  obtain ⟨k', hk'⟩ := exists_eq_mul_right_of_dvd h2,
  have hkp : 0 < k',
  { cases k',
    { rw hk' at ha,
      rwa mul_zero at ha },
    { exact nat.succ_pos k' } },
  use ⟨k', hkp⟩,
  simpa [hkp],
end

lemma lemma_4 {k : ℕ} (hk : 0 < k) (f: ℕ → ℕ) (hf0 : 0 < f 0) :
      0 < ∑(i : ℕ) in finset.range k, f i :=
begin
  cases k,
  { exfalso, exact nat.lt_asymm hk hk },

  calc 0 < f 0 : hf0
     ... ≤ (∑(i : ℕ) in finset.range k, f i.succ) + f 0 :
                  nat.le_add_left (f 0) (∑ (i : ℕ) in finset.range k, f i.succ)
     ... = (∑(i : ℕ) in finset.range k.succ, f i) :
                  (finset.sum_range_succ' (λ (i : ℕ), f i) k).symm
end

--
-- Prove that n has a positive multiple whose representation contains only zeroes and ones.
--
theorem zeroes_and_ones (n : ℕ) : ∃ k : ℕ+, all_zero_or_one (nat.digits 10 (n * k)) :=
begin
  obtain (hn0 : n = 0 ) | (hn : n > 0) := nat.eq_zero_or_pos n,
  { use 1, rw hn0, simp },
  obtain ⟨a, b, hlt, hab⟩ := pigeonhole' n (λm, map_mod n hn (ones 10) m),
  unfold map_mod at hab, unfold ones at hab,
  rw [subtype.mk_eq_mk] at hab,
  have h' : (∑(i : ℕ) in finset.range (b - a), 10^(i + a)) % n = 0 := lemma_2 n hn a b hlt hab,
  have ha: 0 < ∑(i : ℕ) in finset.range (b - a), 10^(i + a),
  { have hm : 0 < b - a := nat.sub_pos_of_lt hlt,
    have hp : 0 < 10 ^ (0 + a) := pow_pos (by norm_num) _,
    exact lemma_4 hm (λ (i : ℕ), 10 ^ (i + a)) hp,
  },
  obtain ⟨k, hk⟩ := lemma_3 ha h',
  use k,
  rw [←hk],
  exact lemma_1 (b - a) 10 a (by norm_num)
end

def all_one_or_two : list ℕ → Prop
| [] := true
| (1 :: ds) := all_one_or_two ds
| (2 :: ds) := all_one_or_two ds
| _ := false


def prepend_one (n : ℕ) := 10 ^ (list.length (nat.digits 10 n)) + n

lemma prepend_one_pos (n: ℕ) : 0 < prepend_one n :=
begin
  cases n,
  { simp[prepend_one], },
  { rw[prepend_one],
    norm_num },
end

lemma two_le_ten : (2 : ℕ) ≤ 10 := by norm_num

lemma digits_len' (n : ℕ) (hn : 0 < n) :
      list.length (nat.digits 10 n) = 1 + list.length (nat.digits 10 (n / 10)) :=
begin
  rw[nat.digits_def' two_le_ten hn],
  rw[list.length],
  exact add_comm _ _,
end

lemma prepend_one_div (n : ℕ) (hn : 0 < n) : prepend_one n / 10 = prepend_one (n / 10) :=
begin
  rw[prepend_one, prepend_one],
  cases n,
  { exfalso, exact nat.lt_asymm hn hn },
  {
    have hb : 2 ≤ 10 := by norm_num,
    rw[digits_len' n.succ (nat.succ_pos n)],
    rw[pow_add, pow_one],
    rw[add_comm],
    have tenpos: 0 < 10 := by norm_num,
    rw [nat.add_mul_div_left _ _ tenpos],
    exact add_comm _ _ }
end

lemma prepend_one_mod (n : ℕ) (hn : 0 < n) : prepend_one n % 10 = n % 10 :=
begin
  rw[prepend_one],
  rw[nat.digits_len _ _ two_le_ten hn],
  rw[pow_add, pow_one],
  exact nat.mul_add_mod _ 10 n
end

lemma prepend_one_eq_append (n : ℕ) :
    nat.digits 10 (prepend_one n) = (nat.digits 10 n) ++ [1] :=
begin
  induction n using nat.strong_induction_on with n' ih,
  cases n',
  { simp[prepend_one], },
  { rw[nat.digits_def' two_le_ten (prepend_one_pos _)],
    rw[prepend_one_div _ (nat.succ_pos n')],
    have hns : n'.succ / 10 < n'.succ := nat.div_lt_self' n' 8,
    rw[ih _ hns],
    rw[←list.cons_append],
    rw[prepend_one_mod _ (nat.succ_pos _), ← nat.digits_def' two_le_ten (nat.succ_pos n')] }
end

lemma prepend_one_all_one_or_two (n : ℕ) (hn : all_one_or_two (nat.digits 10 n)) :
    all_one_or_two (nat.digits 10 (prepend_one n)) :=
begin
 rw[prepend_one_eq_append],
 cases (nat.digits 10 n),
 { simp },
 { rw[list.cons_append],
   sorry },
end

def prepend_two (n : ℕ) := 2 * (10 ^ (list.length (nat.digits 10 n))) + n

lemma prepend_two_all_one_or_two (n : ℕ) (hn : all_one_or_two (nat.digits 10 n)) :
    all_one_or_two (nat.digits 10 (prepend_two n)) :=
begin
 sorry
end

lemma ones_and_twos_aux (n : ℕ) :
  ∃ k : ℕ+, (list.length (nat.digits 10 (2^n.succ * k)) = n.succ) ∧
             all_one_or_two (nat.digits 10 (2^n.succ * k)) :=
begin
  induction n with pn hpn,
  { use 1, simp, },
  obtain ⟨pk, hpk1, hpk2⟩ := hpn,

  /-
    Adding a 1 or a 2 to the front of 2^pn.succ * pk increments it by 2^pn.succ * 5^pn.succ or
    by 2^{pn.succ+1} * 5^pn.succ, in each case preserving divisibility by 2^pn.succ. Since the
    two choices differ by 2^pn.succ * 2^pn.succ, one of them must actually achieve
    divisibility by 2^{pn.succ+1}.
  -/

  sorry
end

--
-- Prove that 2^n has a positive multiple whose representation contains only ones and twos.
--
theorem ones_and_twos (n : ℕ) : ∃ k : ℕ+, all_one_or_two (nat.digits 10 (2^n * k)) :=
begin
  cases n,
  { use 1, simp, },
  obtain ⟨k, hk1, hk2⟩ := ones_and_twos_aux n,
  exact ⟨k, hk2⟩
end
