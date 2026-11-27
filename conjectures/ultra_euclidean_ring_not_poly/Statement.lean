import Mathlib

/-!
Senan Sekhon, "A Necessary and Sufficient Condition for Uniqueness of Euclidean Division",
arXiv:2604.24399v2, section "Further investigation", second boxed statement ("Corollary",
stated as a consequence of the conjecture just before it, so itself conjectural):

  "If R has an ultra-Euclidean function, then either R is a field or R ≅ K[x] for some
   field K."

Here R is an integral domain.

`Claim` is the negation of that statement: it is false.
-/

/-- `f` is a Euclidean function on `R` (the paper's definition of a Euclidean function):
for all `a, b` with `b ≠ 0` there are `q, r` with `a = q b + r` and (`r = 0` or `f r < f b`).
In the paper `f` is only defined on nonzero elements. Here `f` is a total function and the
value `f 0` is never used: it only occurs as `f r` when `r = 0` already holds. -/
def IsEuclideanFn {R : Type} [CommRing R] (f : R → ℕ) : Prop :=
  ∀ a b : R, b ≠ 0 → ∃ q r : R, a = q * b + r ∧ (r = 0 ∨ f r < f b)

/-- `f` is ultra-Euclidean on `R` (the paper's definition of ultra-Euclidean): `f` is Euclidean and
`f (a + b) ≤ max (f a) (f b)` for all nonzero `a, b` with `a + b ≠ 0`. -/
def IsUltraEuclidean {R : Type} [CommRing R] (f : R → ℕ) : Prop :=
  IsEuclideanFn f ∧
    ∀ a b : R, a ≠ 0 → b ≠ 0 → a + b ≠ 0 → f (a + b) ≤ max (f a) (f b)

/-- The negation of the statement: it is not true that every integral domain with an
ultra-Euclidean function is a field or isomorphic (as a ring) to a polynomial ring `K[x]`
over a field `K`. -/
def Claim : Prop :=
  ¬ ∀ (R : Type) [CommRing R] [IsDomain R],
      (∃ f : R → ℕ, IsUltraEuclidean f) →
        IsField R ∨ ∃ (K : Type) (_ : Field K), Nonempty (R ≃+* Polynomial K)
