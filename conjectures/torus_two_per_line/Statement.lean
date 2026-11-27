import Mathlib

/-- A `k`-line of the toric `k`-board of shape `(k, k)`, as in Section 2 of the paper:
`p + [0, k-1] d = {p + t d : t = 0, 1, ..., k - 1}` for a point `p ∈ (ℤ/kℤ)²` and a
direction `d`. -/
def toricLine (k : ℕ) (p : ZMod k × ZMod k) (d : ℤ × ℤ) : Finset (ZMod k × ZMod k) :=
  (Finset.range k).image fun t : ℕ =>
    (p.1 + (t : ZMod k) * (d.1 : ZMod k), p.2 + (t : ZMod k) * (d.2 : ZMod k))

/-- The directions of the paper: `d ∈ {-1, 0, 1}² \ {0}`. A line is axis-parallel when
one coordinate of `d` is `0`, and diagonal when both are `±1`. -/
def IsDirection (d : ℤ × ℤ) : Prop :=
  (d.1 = -1 ∨ d.1 = 0 ∨ d.1 = 1) ∧ (d.2 = -1 ∨ d.2 = 0 ∨ d.2 = 1) ∧ d ≠ (0, 0)

/-- The conjecture "(Restatement of Conjecture 5.1)" in Section 5.1 of K.-H. Ku,
"Monochromatic k in a row", arXiv:2606.12880v1.

For every `k ∈ 3ℕ` (that is, `k = 3, 6, 9, ...`), there is no subset
`A ⊆ (ℤ/kℤ)²` satisfying `|L ∩ A| = 2` for every axis-parallel or diagonal line `L`. -/
def Claim : Prop :=
  ∀ k : ℕ, 0 < k → 3 ∣ k →
    ¬ ∃ A : Finset (ZMod k × ZMod k),
        ∀ (p : ZMod k × ZMod k) (d : ℤ × ℤ), IsDirection d →
          (toricLine k p d ∩ A).card = 2
