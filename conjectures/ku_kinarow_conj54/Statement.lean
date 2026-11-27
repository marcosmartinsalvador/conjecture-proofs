import Mathlib

/-- The eight directions `d ∈ {-1, 0, 1}^2 \ {0}` used for the lines of the paper's boards. -/
def directions (k : ℕ) : Finset (ZMod k × ZMod k) :=
  {(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1), (1, -1), (-1, 1)}

/-- The `k`-line `p + [0, k-1] d` of the toric `k`-board `(ℤ/kℤ)^2`: the set of points
`p, p + d, p + 2d, ..., p + (k-1) d`. For `d` in `directions k` these are exactly the
axis-parallel and diagonal lines of the paper. -/
def torusLine (k : ℕ) (p d : ZMod k × ZMod k) : Finset (ZMod k × ZMod k) :=
  (Finset.range k).image fun t : ℕ => p + t • d

/-- "There is a subset `A ⊆ (ℤ/kℤ)^2` with `|A| ≤ 2k + 2` satisfying `|L ∩ A| ≥ 2` for every
axis-parallel or diagonal line `L`." -/
def HasSmallDoubleCover (k : ℕ) : Prop :=
  ∃ A : Finset (ZMod k × ZMod k), A.card ≤ 2 * k + 2 ∧
    ∀ p : ZMod k × ZMod k, ∀ d ∈ directions k, 2 ≤ (torusLine k p d ∩ A).card

/-- Conjecture 5.4 of K.-H. Ku, "Monochromatic k in a row", arXiv:2606.12880v1:
"For every `k ∈ 3ℕ`, there is no subset `A ⊆ (ℤ/kℤ)^2` with `|A| ≤ 2k + 2` satisfying
`|L ∩ A| ≥ 2` for every axis-parallel or diagonal line `L`." -/
def KuConjecture : Prop :=
  ∀ k : ℕ, 0 < k → 3 ∣ k → ¬ HasSmallDoubleCover k

/-- The conjecture is false: such a subset exists for `k = 6` (14 points) and for `k = 9`
(20 points). In particular the conjecture as stated does not hold. (It also fails for
`k = 3`, for the simple reason that every line there has only three points; the cases
`k = 6` and `k = 9` are stated here so that the disproof does not rest on that case.) -/
def Claim : Prop :=
  HasSmallDoubleCover 6 ∧ HasSmallDoubleCover 9 ∧ ¬ KuConjecture
