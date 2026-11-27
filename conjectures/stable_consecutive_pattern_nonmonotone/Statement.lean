import Mathlib

/-!
# A stable consecutive pattern that is not monotone

Source: S. Chen, H. Fang, S. Kitaev, "Stable patterns on permutations of multisets",
arXiv:2602.13566v2, Conjecture 6.1: "A consecutive pattern is stable if and only if it is
monotone."  The claim below is a counterexample: the consecutive pattern 12435 is stable and
is not monotone.

Conventions.  A word of length `m` over the alphabet `{1, ..., n}` is a map
`w : Fin m → Fin n`.  The multiset `M(k_1, ..., k_n)` has `k a` copies of the letter `a`, and
its permutations are the words `w` with `mult w a = k a` for every letter `a`.  A pattern of
length `ℓ` with distinct letters is a permutation `p` of `Fin ℓ`: `p a` is the letter in
position `a`.
-/

/-- `mult w a` is the number of times the letter `a` occurs in the word `w`. -/
def mult {m n : ℕ} (w : Fin m → Fin n) (a : Fin n) : ℕ :=
  (Finset.univ.filter fun x => w x = a).card

/-- The consecutive pattern `p` occurs in `w` at position `i`: the `ℓ` adjacent letters
`w i, ..., w (i + ℓ - 1)` are in the same relative order as `p 0, ..., p (ℓ - 1)`.
(As `p` has distinct letters, this says that the reduction of the factor is `p`.) -/
def OccAt {ℓ m n : ℕ} (p : Equiv.Perm (Fin ℓ)) (w : Fin m → Fin n) (i : ℕ) : Prop :=
  ∃ h : i + ℓ ≤ m, ∀ a b : Fin ℓ, p a < p b ↔ w ⟨i + a, by omega⟩ < w ⟨i + b, by omega⟩

/-- The number of occurrences of the consecutive pattern `p` in the word `w`. -/
noncomputable def occ {ℓ m n : ℕ} (p : Equiv.Perm (Fin ℓ)) (w : Fin m → Fin n) : ℕ :=
  Set.ncard {i : ℕ | OccAt p w i}

/-- `p` is stable: for every multiset `M(k)`, every rearrangement `σ` of its multiplicities
and every `s`, the multisets `M(k)` and `M(k ∘ σ)` have the same number of permutations with
exactly `s` occurrences of `p`.  (The length `m` is free: if `m` is not the size of the
multiset, both sets are empty.  Multiplicities equal to zero are allowed.) -/
def PatternStable {ℓ : ℕ} (p : Equiv.Perm (Fin ℓ)) : Prop :=
  ∀ (m n : ℕ) (k : Fin n → ℕ) (σ : Equiv.Perm (Fin n)) (s : ℕ),
    Set.ncard {w : Fin m → Fin n | (∀ a, mult w a = k a) ∧ occ p w = s} =
      Set.ncard {w : Fin m → Fin n | (∀ a, mult w a = k (σ a)) ∧ occ p w = s}

/-- The pattern 12435 (with letters counted from zero: 0 1 3 2 4). -/
def p12435 : Equiv.Perm (Fin 5) := Equiv.swap 2 3

/-- The pattern 12435 is stable, and it is neither increasing nor decreasing. -/
def Claim : Prop :=
  PatternStable p12435 ∧ ¬ (StrictMono p12435 ∨ StrictAnti p12435)
