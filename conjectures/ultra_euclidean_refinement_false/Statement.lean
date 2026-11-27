import Mathlib

/-!
Senan Sekhon, "A Necessary and Sufficient Condition for Uniqueness of Euclidean Division",
arXiv:2604.24399v2, section "Further investigation", first boxed statement ("Conjecture"):

  "If f is ultra-Euclidean on R, so is f~."

Here R is an integral domain, f is a Euclidean function on R, and f~ is the refinement of f,
f~(a) = min over nonzero b of f(ab).

`Claim` is the negation of that statement: the conjecture is false.
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

/-- The refinement of `f` (the paper's definition of the refinement): `a ↦ min {f (a b) | b ≠ 0}`.
The infimum of a nonempty set of natural numbers is its minimum. -/
noncomputable def refinement {R : Type} [CommRing R] (f : R → ℕ) (a : R) : ℕ :=
  sInf {n : ℕ | ∃ b : R, b ≠ 0 ∧ n = f (a * b)}

/-- The negation of the conjecture: it is not true that for every integral domain `R` and
every ultra-Euclidean `f` on `R`, the refinement of `f` is again ultra-Euclidean. -/
def Claim : Prop :=
  ¬ ∀ (R : Type) [CommRing R] [IsDomain R] (f : R → ℕ),
      IsUltraEuclidean f → IsUltraEuclidean (refinement f)
