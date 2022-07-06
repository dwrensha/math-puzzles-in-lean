import data.stream.defs
import data.stream.init

import tactic.basic

/-

(Alternate formulation of the kolmogorov_puzzle.lean.)

Puzzle referenced from this tweet: https://twitter.com/sigfpe/status/1474173467016589323

From the book _Out of their Minds: The Lives and Discoveries of 15 Great Computer Scientists_
by Dennis Shasha and Cathy Lazere.


Problem: Suppose each (finite) word is either "decent" or "indecent". Given an infinite
sequence of characters, can you always break it into finite words so that all of them
except perhaps the first one belong to the same class?

Answer: yes.

-/


variable {α : Type}

-- non-empty list of α
inductive word (α : Type) : Type
| base : α → word
| cons : α → word → word

def word_head : word α → α
| (word.base a) := a
| (word.cons a _) := a

def prepend_word : word α → stream α → stream α
| (word.base a) s := a :: s
| (word.cons a as) s := a :: prepend_word as s

/--
 Number of symbols in the word, minus one.
-/
def word_size : word α → ℕ
| (word.base a) := 0
| (word.cons a as) := 1 + word_size as

def append : word α → word α → word α
| (word.base c) b := word.cons c b
| (word.cons c cs) b := (word.cons c (append cs b))

structure accumulator_rest (α : Type) : Type :=
  (word_rest : word α)
  (stream_rest : stream (word α))

structure accumulator (α : Type) : Type :=
  (current : α)
  (rest : accumulator_rest α)

def flatten_step : accumulator_rest α → accumulator α
| ⟨word.base c, ws⟩ := ⟨c, ws.head, ws.tail⟩
| ⟨word.cons c cs, ws⟩ := ⟨c, cs, ws⟩

def flatten_aux (words : stream (word α)) : stream (accumulator α) :=
  stream.corec id
               (λ (acc : accumulator α), flatten_step acc.rest)
               (flatten_step ⟨words.head, words.tail⟩)

def flatten (words : stream (word α)) : stream α :=
  (flatten_aux words).map (λ acc, acc.current)

lemma flatten_cons (w : word α) (words : stream (word α)) :
      flatten (w :: words) = prepend_word w (flatten words) :=
begin
  simp[flatten, flatten_aux, stream.corec],
  rw [stream.map_id, stream.map_id],
  have hwh : (w::words).head = w := rfl,
  have hwt : (w::words).tail = words := rfl,
  rw [hwh, hwt], clear hwh hwt,
  induction w with wz a pw hpw,
  { have h :
       flatten_step {word_rest := word.base wz, stream_rest := words}
      = ⟨wz, words.head, words.tail⟩ := rfl,
    rw[prepend_word, h, stream.iterate_eq, stream.map_cons] },
  { have h : flatten_step {word_rest := word.cons a pw, stream_rest := words}
       = ⟨a, pw, words⟩ := rfl,
    rw[h, prepend_word, ←hpw, stream.iterate_eq, stream.map_cons] },
end

lemma flatten_head (words: stream (word α)) : (flatten words).nth 0 = word_head words.head :=
begin
  rw [flatten, flatten_aux],
  cases words.head with a a as,
  {refl},
  {refl},
end

def prefixes_core (w : word α) (s : stream α) : stream (word α) :=
stream.corec_on (w, s)
  (λ ⟨a, b⟩, a)
  (λ p, match p with (w', s') := ⟨append w' (word.base (s'.head)), s'.tail⟩ end)

/-- Initial segments of a stream -/
def prefixes (s : stream α) : stream (word α) :=
  prefixes_core (word.base s.head) s.tail

def all_prefixes'
  (p : word α → Prop)
  (a : stream α) : Prop :=
stream.all p (prefixes a)

/- takes a word of length n + 1 -/
def take_word : ℕ → stream α → word α
| 0 s := word.base s.head
| (n + 1) s := word.cons s.head (take_word n s.tail)

lemma take_prefix
   (is_decent : word α → Prop)
   (a : stream α)
   (ha : all_prefixes' is_decent a)
   (n : ℕ) : is_decent (take_word n a) :=
begin
  have ht := ha n,
  -- should be straightforward. prove an analog of stream.nth_inits
  sorry
end

structure decent_word (is_decent: word α → Prop) : Type :=
  (w: word α)
  (h : is_decent w)

/-
  accumulator is:
    n, the number of symbols already consumed
    h, a proof that (a.drop n) is prefix-decent
-/
noncomputable def choose_decent_words
    (is_decent : word α → Prop)
    (a : stream α)
    (hinit: all_prefixes' is_decent a)
    (hnot: ∀ (n : ℕ), ∃ (k : ℕ),
            all_prefixes' is_decent (stream.drop (k + 1 + n) a))
     : stream (decent_word is_decent) :=
stream.corec' (λ (acc: psigma (λ (n: ℕ), all_prefixes' is_decent (a.drop n))),
                 let ⟨n,hprev⟩ := acc in
                 let new_word_length := classical.some (hnot n) in
                 let h := (classical.some_spec (hnot n)) in
                 let new_word := take_word new_word_length (a.drop n) in
                 ⟨⟨new_word, take_prefix is_decent _ hprev new_word_length⟩,
                  ⟨new_word_length + 1 + n, h ⟩ ⟩)
               ⟨0, hinit⟩

lemma extract_all_decent
    (is_decent : word α → Prop)
    (s : stream (decent_word is_decent))
    : stream.all is_decent (s.map (λ x, x.w)) :=
begin
  intro n,
  exact (s n).h,
end

structure word_indices :=
  (start : ℕ)
  (size : ℕ) -- word length minus one

lemma unflatten
  (a : stream α)
  (b : stream word_indices)
  (w : stream (word α))
  (hw : ∀ n, take_word (b n).size (a.drop (b n).start) = w n)
  (hn : ∀ n, (b n).start + 1 + (b n).size = (b (n + 1)).start)
  (hz : (b 0).start = 0) :
  a = flatten w :=
begin
/-
  refine stream.coinduction _ _,
  { sorry },
  { intros β fr hfr,
    sorry
  },
-/
  ext,
  induction n with pn hpn,
  { have hw0 := hw 0,
    have hsd : stream.drop 0 a = a := rfl,
    have hnth : w 0 = w.head := rfl,
    rw [hz, hsd, hnth] at hw0,
    rw [flatten_head, ← hw0],
    cases (b 0).size,
    { refl },
    { refl },
  },
  { sorry },
end

lemma flatten_decent_words
    (is_decent : word α → Prop)
    (a : stream α)
    (hinit: all_prefixes' is_decent a)
    (hnot: ∀ (n : ℕ), ∃ (k : ℕ),
            all_prefixes' is_decent (stream.drop (k + 1 + n) a)) :
    a = flatten ((choose_decent_words is_decent a hinit hnot).map (λ x, x.1)) :=
begin
  simp[choose_decent_words, stream.corec', stream.corec, flatten],
  sorry
end


theorem kolmogorov_puzzle
  (is_decent : word α → Prop)
  (a : stream α)
  : (∃ (words : stream (word α)),
     (a = flatten words ∧
      (stream.all is_decent words.tail ∨
       stream.all (λ w, ¬ is_decent w) words.tail))) :=
begin
  let p : Prop :=
     (∃ (n : ℕ), ∀ (k : ℕ), --0 < k →
         ¬ all_prefixes' is_decent (stream.drop (k + n) a)),

  obtain ⟨n, hn⟩ | hnot := classical.em p,
  { sorry },
  { push_neg at hnot,
    sorry
  }
end
