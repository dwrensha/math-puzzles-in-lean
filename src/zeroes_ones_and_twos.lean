import data.int.modeq
import data.nat.basic
import data.nat.modeq
import data.pnat.basic
import data.nat.digits
import data.nat.gcd
import data.zmod.basic

lemma foo_aux
  (base factor c d : ℕ)
  (hord : c ≤ d)
  (h_coprime : nat.coprime factor base)
  (h_equal : base * c ≡ base * d [MOD factor])
  : c ≡ d [MOD factor] :=
begin
  have hm : (base * c) ≤ (base * d) := nat.mul_le_mul_left base hord,
  have hd: (factor ∣ (base * d) - (base * c)) := (nat.modeq.modeq_iff_dvd' hm).mp h_equal,
  rw [←nat.mul_sub_left_distrib base d c] at hd,
  apply (nat.modeq.modeq_iff_dvd' hord).mpr,
  exact nat.coprime.dvd_of_dvd_mul_left h_coprime hd,
end

lemma foo
  (base factor c d : ℕ)
  (h_coprime : nat.coprime factor base)
  (h_equal : base * c ≡ base * d [MOD factor])
  : c ≡ d [MOD factor] :=
begin
  have hord: c ≤ d ∨ d ≤ c := nat.le_total,
  cases hord with hcd hdc,
  {
    exact foo_aux base factor c d hcd h_coprime h_equal,
  },
  {
   exact (foo_aux base factor d c hdc h_coprime h_equal.symm).symm,
  }
end

lemma coprime_power
  (base factor : ℕ)
  (k : ℕ)
  (h_coprime : nat.coprime factor base)
  : nat.coprime factor (base^k) :=
begin
  exact nat.coprime.pow_right k h_coprime
end

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


def iterate_pow (base factor : ℕ) (hfactor: factor > 0) : ℕ → fin factor :=
λn, ⟨(base ^ n) % factor, nat.mod_lt (base ^ n) hfactor ⟩

lemma bar
  (base factor : ℕ)
  (hf: factor > 0)
  : ∃ m n : ℕ, (m ≠ n ∧ base^m ≡ base^n [MOD factor]) :=
begin
  let f := iterate_pow base factor hf,
  have he : ∃ a b : ℕ, a ≠ b ∧ f a = f b := pigeonhole factor f,
  obtain ⟨a, b, hab⟩ := he,
  cases hab,
  use a,
  use b,
  use hab_left,
  have : base ^ a % factor = base ^ b % factor,
  {
     have hval :(f a).val = (f b).val := congr_arg subtype.val hab_right,

     have havala: (f a).val = (base ^ a) % factor := rfl,
     rw ← havala,

     have havalb: (f b).val = (base ^ b) % factor := rfl,
     rw ← havalb,

     assumption,
  },
  unfold nat.modeq,
  assumption,
end

-- let a, b, c, be natural numbers, with c < b, a and b coprime.
-- prove that there exists k > 0 such that c a^k = c mod b.
lemma periodic
  (base factor : ℕ)
  (h_coprime: nat.gcd base factor = 1)
  : ∃k : ℕ+, (base^k.val) ≡ 1 [MOD factor] :=
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
