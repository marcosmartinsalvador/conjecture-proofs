import Mathlib

/-- Dedekind's psi function, written as the paper writes it: for `n = ∏ pᵢ ^ aᵢ`,
`ψ(n) = ∏ pᵢ ^ (aᵢ - 1) * (pᵢ + 1)`, and `ψ(1) = 1` (the empty product). -/
def dedekindPsi (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1)

/-- `σ(n)`: the sum of the positive divisors of `n`. -/
def sumDivisors (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- Conjecture 1 of S. I. Dimitrov, "Lower bounds on expressions depending on the
functions φ(n), ψ(n) and σ(n), III", arXiv:2606.12484v1.

For all integers `k ≥ 1` and `n ≥ 2`,
`(φ(n)^k + ψ(n)^k + σ(n)^k) (1/φ(n)^k + 1/ψ(n)^k + 1/σ(n)^k)
   ≥ (5 (n^2 - 1)^k + 2 (n + 1)^(2k) + 2 (n - 1)^(2k)) / (n^2 - 1)^k`,
where `φ` is Euler's totient (`Nat.totient`). Both sides are rational numbers, so
the inequality is stated in `ℚ`. -/
def Claim : Prop :=
  ∀ k n : ℕ, 1 ≤ k → 2 ≤ n →
    (5 * ((n : ℚ) ^ 2 - 1) ^ k + 2 * ((n : ℚ) + 1) ^ (2 * k) + 2 * ((n : ℚ) - 1) ^ (2 * k))
        / ((n : ℚ) ^ 2 - 1) ^ k
      ≤ ((Nat.totient n : ℚ) ^ k + (dedekindPsi n : ℚ) ^ k + (sumDivisors n : ℚ) ^ k)
        * (1 / (Nat.totient n : ℚ) ^ k + 1 / (dedekindPsi n : ℚ) ^ k
            + 1 / (sumDivisors n : ℚ) ^ k)
