import Mathlib

/-- `a` is an Euler liar for `n` (the paper's Definition "Euler pseudoprime"):
`(a/n) ≡ a ^ ((n-1)/2) (mod n)`, where `(a/n)` is the Jacobi symbol. -/
def IsEulerLiar (n a : ℕ) : Prop :=
  ((jacobiSym (a : ℤ) n : ℤ) : ZMod n) = (a : ZMod n) ^ ((n - 1) / 2)

instance (n a : ℕ) : Decidable (IsEulerLiar n a) := by
  unfold IsEulerLiar
  infer_instance

/-- The number of Euler liars in `ℤ_n^*`: the residues `0 ≤ a < n` coprime to `n` that
are Euler liars for `n`. -/
def numEulerLiars (n : ℕ) : ℕ :=
  ((Finset.range n).filter fun a => Nat.Coprime a n ∧ IsEulerLiar n a).card

/-- Carmichael number (the paper's Definition "Carmichael number"): a composite number
`n` with `a ^ (n-1) ≡ 1 (mod n)` for all `a` relatively prime to `n`. -/
def IsCarmichael (n : ℕ) : Prop :=
  1 < n ∧ ¬ n.Prime ∧ ∀ a : ℕ, Nat.Coprime a n → a ^ (n - 1) ≡ 1 [MOD n]

/-- Sophie Germinus pseudoprime (the paper's Definition in the appendix): `n = p₁ p₂`
with `p₁` prime and `p₂ = 2 p₁ - 1` also prime. -/
def IsSophieGerminusPsp (n : ℕ) : Prop :=
  ∃ p₁ p₂ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₂ = 2 * p₁ - 1 ∧ n = p₁ * p₂

/-- The conjecture at the end of the appendix "Sophie Germinus pseudoprimes" of
arXiv:2602.21840v1, "Ours go to 211: Euler pseudoprimes to 47 prime bases (from
Carmichael numbers)".

If an odd squarefree composite integer `n` has `φ(n)/2` Euler liars in `ℤ_n^*` then it
is a Carmichael number, and if it has `φ(n)/4` Euler liars in `ℤ_n^*` then it is either
a Carmichael number or a Sophie Germinus pseudoprime.

"Has `φ(n)/2` Euler liars" is written `2 * numEulerLiars n = φ(n)`, and likewise for 4. -/
def Claim : Prop :=
  ∀ n : ℕ, Odd n → Squarefree n → 1 < n → ¬ n.Prime →
    (2 * numEulerLiars n = Nat.totient n → IsCarmichael n) ∧
    (4 * numEulerLiars n = Nat.totient n → IsCarmichael n ∨ IsSophieGerminusPsp n)
