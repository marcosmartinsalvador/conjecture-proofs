import Mathlib

/-- The first conjecture in the "Concluding Remarks" of S. Jirattikansakul,
T. Kittipassorn, K. Kongsiri, N. Moonwichit and K. Sriamorn, "Congruences via
Partitions with Exactly Two Part Sizes", arXiv:2604.25394v1.

"Let `N = 16n + 6` for some nonnegative integer `n`. Then
`∑_{1 ≤ k < √N} σ₀(N - k²) ≡ 0 (mod 4)`",
where `σ₀(m)` is the number of positive divisors of `m` (here `(Nat.divisors m).card`).

The index set `1 ≤ k < √N` is the set of positive integers `k` with `k² < N`; every
such `k` is below `N`, so it is written as a filter of `Finset.range N`. For these `k`
the number `N - k²` is positive, so the truncated subtraction of `ℕ` is the real one. -/
def Claim : Prop :=
  ∀ n : ℕ,
    (∑ k ∈ (Finset.range (16 * n + 6)).filter (fun k => 1 ≤ k ∧ k ^ 2 < 16 * n + 6),
      (Nat.divisors (16 * n + 6 - k ^ 2)).card) ≡ 0 [MOD 4]
