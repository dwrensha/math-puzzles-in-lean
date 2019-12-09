import data.real.basic data.nat.basic

-- first, let's define what it means for a function to be "convex"...

-- f (tx_1 + (1-t)x2) ≤ t f(x1) + (1 - t) f(x2)

def is_convex (f: ℝ → ℝ) : Prop :=
  ∀ t: ℝ, ((0 ≤ t) && (t ≤ 1)) →
    ∀ x1 x2 : ℝ, f (t * x1 + (1 - t) * x2) ≤ t * f x1 + (1 - t) * f x2



def sum_first_n (f: ℕ → ℝ) : ℕ → ℝ
| 0 := f 0
| (nat.succ n) := (f (nat.succ n)) + (sum_first_n n)

def sum_seq { n : ℕ } (f: fin n → ℝ) : ℝ :=
  let f' := λ m : ℕ, if h: m < n then f ⟨m, h⟩ else 0 in
  sum_first_n f' n

def is_weight {n : ℕ} (a : fin n → ℝ) : Prop :=
  (sum_seq a = 1) ∧ ∀ i : fin n, a i ≥ 0

lemma empty_sum_is_zero (f : fin 0 → ℝ) : sum_seq f = 0 :=
begin
  unfold sum_seq,
  simp,
  unfold sum_first_n,
end

lemma no_empty_weight (a : fin 0 → ℝ) (h : is_weight a) : false :=
begin
  cases h with h_sum1 h_nonneg,
  rw empty_sum_is_zero a at h_sum1,
  linarith,
end

lemma singleton_weight_is_trivial (a : fin 1 → ℝ) (h : is_weight a) : a 0 = 1 :=
begin
  unfold is_weight at h,
  cases h with h1 hp,
  unfold sum_seq at h1,
  simp at h1,
  unfold sum_first_n at h1,
  simp at h1,
  exact h1,
end

theorem jensen_inequality {n: ℕ} (f: ℝ → ℝ) (a: fin n → ℝ) (ha : is_weight a) (hf : is_convex f):
  ∀ x : fin n → ℝ,
    (f (sum_seq (λ i : fin n, (a i) * (x i)))) ≤
    (sum_seq (λ i : fin n, (a i) * f (x i)))
:=
begin
  revert a,
  cases n,
     intros a hw,
     exfalso,
     exact no_empty_weight a hw,
  induction n with pn ih,
    intros a hw x,
    have hs := singleton_weight_is_trivial a hw,
    unfold sum_seq,
    simp,
    unfold sum_first_n,
    simp,
    have hz: 0 < 1,
      linarith,
    have haz: a 0 = a ⟨0, hz⟩,
      refl,
    rw haz at hs,
    rw hs,
    simp,
  intros a hw x,
  by_cases hp: (nat.succ pn) = 1,
    sorry,
  sorry,
end
