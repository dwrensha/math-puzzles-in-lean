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

lemma prop_fiddling (a b : Prop) : (¬ (a → b)) → (a ∧ ¬ b) :=
begin
  intro h,
  exact not_imp.mp h,
end

lemma not_not_lemma (a : Prop) : ¬ ¬ a → a :=
begin
  exact not_not.mp
end

lemma pidgeonhole :
  ∀ s: finset ℕ, ∀ f : ℕ → {x : ℕ // x ∈ s}, ∃ a b : ℕ, (a ≠ b ∧ f a = f b) :=
begin
  apply @finset.induction ℕ (λ s: finset ℕ, ∀ f : ℕ → {x : ℕ // x ∈ s}, ∃ a b : ℕ, (a ≠ b ∧ f a = f b)),
  {
     intro,
     exfalso,
     exact (finset.not_mem_empty (f 0).val) (f 0).property,
  },
  intros n s hn hip f,
  cases classical.em (∃k:ℕ, (∀ m:ℕ, k ≤ m → (f m).val ≠ n)) with hbounded hinf,
  {
    obtain ⟨k0, hk0⟩ := hbounded,
    let fk: ℕ → {x // x ∈ s} := (λn:ℕ, ⟨(f (n + k0)).val, _⟩),
    {
      obtain ⟨a, ha⟩ := hip fk,
      obtain ⟨b, hb⟩ := ha,
      use (a + k0),
      use (b + k0),
      cases hb,
      split,
      {
        intro heq,
        apply hb_left,
        exact nat.add_right_cancel heq,
      },
      simp at hb_right,
      exact subtype.ext hb_right,
    },
    have hk0a := (hk0 (n + k0)) (nat.le_add_left _ _),
    exact finset.mem_of_mem_insert_of_ne (f (n + k0)).property hk0a,
  },
  {
    have hall : ∀k:ℕ, ¬(∀ m:ℕ, k ≤ m → (f m).val ≠ n) := not_exists.mp hinf,
    let hk0 := hall 0,
    have : (∃ m:ℕ, ¬(0 ≤ m → (f m).val ≠ n)) := not_forall.mp hk0,
    obtain ⟨m0, hm0⟩ := this,
    have hnn : 0 ≤ m0 ∧ ¬ (f m0).val ≠ n := not_imp.mp hm0,
    have hfm0 : (f m0).val = n := not_not.mp hnn.2,

    let hk1 := hall (m0 + 1),
    have : (∃ m:ℕ, ¬(m0 + 1 ≤ m → (f m).val ≠ n)) := not_forall.mp hk1,
    obtain ⟨m1, hm1⟩ := this,
    have hnn1 : m0 + 1 ≤ m1 ∧ ¬ (f m1).val ≠ n := not_imp.mp hm1,
    have hfm1 : (f m1).val = n := not_not.mp hnn1.2,
    use m0,
    use m1,
    split,
    {
      cases hnn1,
      linarith,
    },
    have : (f m0).val = (f m1).val := by rw [hfm0, hfm1],
    exact subtype.eq this,
  }
end

lemma bar
  (base factor : ℕ)
  : ∃ m n : ℕ, (m ≠ n ∧ base^m ≡ base^n [MOD factor]) :=
begin
  sorry,
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
