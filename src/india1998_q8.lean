import data.finset.basic
import data.finset.lattice
import data.nat.basic
import data.nat.gcd.basic
import data.pnat.basic

/-

Indian Mathematical Olympiad 1998, Problem 8.

Let M be a positive integer and consider the set

    S = { n ∈ ℕ : M² ≤ n < (M + 1)² }.

Prove that the products of the form a * b with a,b ∈ S are all distinct.

-/

theorem lemma_1
  (M : ℕ)
  (hM : 0 < M)
  (a b c d : {x : ℕ // M^2 ≤ x ∧ x < (M + 1)^2})
  (h_ne : ({a, b}: finset ℕ) ≠ {c, d})
  (h_wlog : a < c ∧ a < d)
  : a.val * b.val ≠ c.val * d.val :=
begin
  intro heq,
  let p := nat.gcd a c,
  -- let q = a / p and r = c / p
  -- then gcd(q,r) = 1
  -- Since q ∣(ab/p) = cd / p = rd, we have q∣d.
  -- Now let s = d/q so that b = cd /a = rs.
  -- Therefore, a = pq, b = rs, c = pr, d = qs for some positive integers p,q,r,s.

  -- Since c > a, r > q, and r ≥ q + 1.
  -- Since d > a, s > p, and s ≥ p + 1.
  -- Therefore,,
  --    b = rs ≥ (p + 1)(q + 1) = pq + p + q + 1
  --           ≥ pq + 2 sqrt(pq) + 1 = a + 2 sqrt(a) + 1
  --           ≥ M^2 + 2 M + 1 = (M + 1)^2
  -- Then b is not in S, a contradiction.
  sorry
end

theorem india1998_q8
  (M : ℕ)
  (hM : 0 < M)
  (a b c d : {x : ℕ // M^2 ≤ x ∧ x < (M + 1)^2})
  (h_ne : ({a, b}: finset ℕ) ≠ {c, d})
  : a.val * b.val ≠ c.val * d.val :=
begin
  let m : option ℕ := finset.min {a,b,c,d},
  
  -- delegate to lemma_1 ...
  sorry,
end

