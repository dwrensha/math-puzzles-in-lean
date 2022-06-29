import data.stream.defs
import data.stream.init

import algebra.big_operators

import tactic.basic
import tactic.push_neg
import tactic.rcases
import tactic.suggest

/-

Puzzle referenced from this tweet: https://twitter.com/sigfpe/status/1474173467016589323

From the book _Out of their Minds: The Lives and Discoveries of 15 Great Computer Scientists_
by Dennis Shasha and Cathy Lazere.


Problem: Suppose each (finite) word is either "decent" or "indecent". Given an infinite
sequence of characters, can you always break it into finite words so that all of them
except perhaps the first one belong to the same class?

Answer: yes.

-/

open_locale big_operators

variable {α : Type}

def break_into_words :
   (stream ℕ) → -- word lengths
   (stream α) → -- original sequence
   (stream (list α)) -- sequence of words
 := function.curry
     (stream.corec
       (λ ⟨lengths, a'⟩, stream.take (lengths.head) a')
       (λ ⟨lengths, a'⟩, ⟨lengths.tail, stream.drop (lengths.head) a'⟩))

--#eval (stream.take 10 (break_into_words id id))

/--
  Dropping the first word is equivalent to dropping `first_length` symbols of the original stream.
-/
lemma break_into_words_cons
  (lengths: stream ℕ)
  (first_length : ℕ)
  (a : stream α) :
  (break_into_words (first_length::lengths) a).tail = break_into_words lengths (a.drop first_length) :=
begin
  simp[break_into_words, stream.corec,stream.tail_map, stream.tail_iterate],
  refl
end

lemma break_into_words_closed_form
    (lengths : stream ℕ)
    (a : stream α)
   : break_into_words lengths a =
      (λ i, stream.take (lengths i) (stream.drop (∑(j : ℕ) in finset.range i, lengths j) a)) :=
begin
  funext n,
  convert_to ((stream.corec (λ x, stream.take (x.fst.head) x.snd)
                 (λ x, ⟨x.fst.tail, stream.drop (x.fst.head) x.snd⟩)) :
                  stream ℕ × stream α → stream (list α)) ⟨lengths, a⟩ n =
             stream.take (lengths n) (stream.drop (∑(j : ℕ) in finset.range n, lengths j) a),
  { rw[break_into_words, function.curry], congr; ext ⟨a,b⟩; refl },
  rw [stream.corec_def,stream.map],
  simp only,
  congr,
  { revert a lengths,
    induction n with pn hpn,
    { intros a b, refl},
    { intros a b,
      { have hnth: b pn.succ = b.nth pn.succ := rfl,
        rw[hnth, stream.nth_succ, stream.nth_succ, stream.iterate_eq, stream.tail_cons, hpn],
        refl } } },
  { revert a lengths,
    induction n with pn hpn,
    { intros a b, refl},
    { intros a b,
      rw [stream.nth_succ, stream.iterate_eq, stream.tail_cons, hpn, stream.drop_drop, finset.sum_range_succ'],
      congr } }
end

def all_same_class
  (is_decent : list α → Prop)
  (b : stream (list α))
  : Prop :=
 stream.all is_decent b ∨ stream.all (λ w ,¬is_decent w) b

def all_prefixes
  (p : list α → Prop)
  (a : stream α) : Prop :=
stream.all p (stream.inits a)

lemma take_prefix
   (is_decent : list α → Prop)
   (a : stream α)
   (ha : all_prefixes is_decent a)
   (n : ℕ)
   (hn : 0 < n) : is_decent (a.take n) :=
begin
  cases n,
  { exfalso, exact nat.lt_asymm hn hn},
  have ht := ha n,
  rwa [stream.nth_inits] at ht,
end

structure decent_word (a : stream α) (is_decent: list α → Prop) : Type :=
  (start : ℕ)
  (length : ℕ)
  (nonempty : 0 < length)
  (h : is_decent ((a.drop start).take length))

structure decent_accumulator (a: stream α) (is_decent : list α → Prop) : Type :=
  (start : ℕ)
  (prefix_decent: all_prefixes is_decent (stream.drop start a))

noncomputable def choose_decent_words
    (is_decent : list α → Prop)
    (a : stream α)
    (hinit: all_prefixes is_decent a)
    (hnot: ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧
            all_prefixes is_decent (stream.drop (n + k) a))
     : stream (decent_word a is_decent) :=
stream.corec (λ (acc: decent_accumulator a is_decent),
                  let new_word_length := classical.some (hnot acc.start) in
                  let new_word_nonempty := (classical.some_spec (hnot acc.start)).1 in
                  ⟨acc.start, new_word_length, new_word_nonempty,
                   take_prefix
                    is_decent _ acc.prefix_decent new_word_length new_word_nonempty⟩)
             (λ acc, ⟨acc.start + classical.some (hnot acc.start),
                      (classical.some_spec (hnot acc.start)).2⟩)
             ⟨0, hinit⟩

lemma chosen_decent_closed_form
    (is_decent : list α → Prop)
    (a : stream α)
    (hinit: all_prefixes is_decent a)
    (hnot: ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧
            all_prefixes is_decent (stream.drop (n + k) a))
  : ∀ n : ℕ, (((choose_decent_words is_decent a hinit hnot).nth n).start =
              ∑(j : ℕ) in finset.range n, ((choose_decent_words is_decent a hinit hnot).nth j).length)
            :=
begin
  intro n,
  induction n with n pn,
  { refl },
  { rw[finset.sum_range_succ, ← pn], refl },
end

lemma check_decent_words
    (is_decent : list α → Prop)
    (a : stream α)
    (hinit: all_prefixes is_decent a)
    (hnot: ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧
            all_prefixes is_decent (stream.drop (n + k) a))
  : stream.all
      is_decent
      (break_into_words
          (λ i, ((choose_decent_words is_decent a hinit hnot).nth i).length)
          a) :=
begin
  rw [break_into_words_closed_form],
  simp_rw [←chosen_decent_closed_form],
  intro j,
  exact ((choose_decent_words is_decent a hinit hnot).nth j).h
end

structure indecent_word (a : stream α) (is_decent: list α → Prop) : Type :=
  (start : ℕ)
  (length : ℕ)
  (nonempty : 0 < length)
  (h : ¬is_decent ((a.drop start).take length))

lemma not_all_prefixes
    (is_decent : list α → Prop)
    (a : stream α)
    (h : ¬ all_prefixes is_decent a) :
    ∃ n, ¬ is_decent (a.take (nat.succ n)) :=
begin
  simp[all_prefixes, stream.all_def] at h,
  obtain ⟨x, hx⟩ := h,
  rw [stream.nth_inits] at hx,
  use x
end

/-
 accumulator is: n, the number of symbols consumed so far
-/
noncomputable def choose_indecent_words
    (is_decent : list α → Prop)
    (a : stream α)
    (h: ∀ (k : ℕ), ¬all_prefixes is_decent (stream.drop k a))
     : stream (indecent_word a is_decent) :=
stream.corec (λ n, let hd := not_all_prefixes is_decent (stream.drop n a) (h n) in
                   let new_word_length := nat.succ (classical.some hd) in
                   let hh := (classical.some_spec hd) in
                   ⟨n, new_word_length, nat.succ_pos _, hh⟩
             )
             (λ n, let hd := not_all_prefixes is_decent (stream.drop n a) (h n) in
                   let new_word_length := nat.succ (classical.some hd) in
                   n + new_word_length)
             0

lemma chosen_indecent_closed_form
    (is_decent : list α → Prop)
    (a : stream α)
    (h: ∀ (k : ℕ), ¬all_prefixes is_decent (stream.drop k a))
  : ∀ n : ℕ, (((choose_indecent_words is_decent a h).nth n).start =
              ∑(j : ℕ) in finset.range n, ((choose_indecent_words is_decent a h).nth j).length)
            :=
begin
  intro n,
  induction n with n pn,
  { refl },
  { rw[finset.sum_range_succ, ← pn],
    refl },
end

lemma check_indecent_words
    (is_decent : list α → Prop)
    (a : stream α)
    (h: ∀ (k : ℕ), ¬all_prefixes is_decent (stream.drop k a))
  : stream.all
      (λ x, ¬ is_decent x)
      (break_into_words
          (λ i, ((choose_indecent_words is_decent a h).nth i).length)
          a) :=
begin
  rw [break_into_words_closed_form],
  simp_rw [←chosen_indecent_closed_form],
  intro j,
  exact ((choose_indecent_words is_decent a h).nth j).h
end

theorem kolmogorov_puzzle
  (is_decent : list α → Prop)
  (a : stream α)
  : (∃ (lengths : stream ℕ),
     (stream.all (λ length, 0 < length) lengths ∧
      all_same_class is_decent (break_into_words lengths a).tail)) :=
begin
  let p : Prop :=
     (∃ (n : ℕ), ∀ (k : ℕ), 0 < k →
         ¬ all_prefixes is_decent (stream.drop (n + k) a)),

  cases classical.em p with h hnot,
  { obtain ⟨n, hn⟩ := h,
    let a' := stream.drop (n + 1) a,
    have hn' : ∀ (k : ℕ), ¬all_prefixes is_decent (stream.drop k a'),
    { intro k,
      have hnk := hn (k + 1) (nat.succ_pos _),
      rw [stream.drop_drop],
      have ha : k + (n + 1) = n + (k + 1) := by ring,
      rwa[ha] },
    let d := choose_indecent_words is_decent a' hn',
    use n.succ::(λ i, (d.nth i).length),
    split,
    { intro i,
      cases i,
      {exact nat.succ_pos n},
      { exact (d.nth i).nonempty }},
    { right,
      rw [break_into_words_cons],
      exact check_indecent_words is_decent a' hn' }},
  { push_neg at hnot,
    obtain ⟨k, hkp, hinit⟩ := hnot 0,
    have hdka : stream.drop (0 + k) a = stream.drop k a := by { rw [←stream.drop_drop], refl },
    rw [hdka] at hinit,
    let a' := stream.drop k a,
    have hnot' : ∀ (n : ℕ), ∃ (k : ℕ), 0 < k ∧ all_prefixes is_decent (stream.drop (n + k) a'),
    { intros n',
      obtain ⟨k', hk0', hk'⟩ := hnot (k + n'),
      use k',
      split,
      { exact hk0' },
      have hd: (stream.drop (k + n' + k') a) = (stream.drop (n' + k') a'),
      { rw [stream.drop_drop],
        ring_nf },
      rwa [←hd] },
    let d := choose_decent_words is_decent a' hinit hnot',
    use k::(λ i, (d.nth i).length),
    split,
    { intro i,
      cases i,
      { exact hkp },
      {exact (d.nth i).nonempty }},
    { left,
      rw [break_into_words_cons],
      exact check_decent_words is_decent a' hinit hnot' }},
end
