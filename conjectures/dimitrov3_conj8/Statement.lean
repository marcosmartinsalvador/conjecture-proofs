import Mathlib

/-- Dedekind's psi function, written as the paper writes it: for `n = ∏ pᵢ ^ aᵢ`,
`ψ(n) = ∏ pᵢ ^ (aᵢ - 1) * (pᵢ + 1)`, and `ψ(1) = 1` (the empty product). -/
def dedekindPsi (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) * (p + 1)

/-- `σ(n)`: the sum of the positive divisors of `n`. -/
def sumDivisors (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- Conjecture 8 of S. I. Dimitrov, "Lower bounds on expressions depending on the
functions φ(n), ψ(n) and σ(n), III", arXiv:2606.12484v1.

For all integers `k ≥ 1` and `n ≥ 2`, with `φ = φ(n)` (Euler's totient, `Nat.totient`),
`ψ = ψ(n)` and `σ = σ(n)`:

`φ^k (ψ+σ) / (ψ^k (φ+σ) + σ^k (φ+ψ)) + ψ^k (φ+σ) / (φ^k (ψ+σ) + σ^k (φ+ψ))
     + σ^k (φ+ψ) / (φ^k (ψ+σ) + ψ^k (φ+σ))
   ≥ (n (n+1)^(k-1) (n-1)^k + (n-1)^(2k) + 4 n^2 (n+1)^(2k-2))
       / (2 n^2 (n+1)^(2k-2) + 2 n (n+1)^(k-1) (n-1)^k)`

Both sides are rational numbers, so the inequality is stated in `ℚ`. Below, `φ`, `ψ`, `σ`
and `N` are the values `φ(n)`, `ψ(n)`, `σ(n)` and `n` as rational numbers.
The exponents `k - 1` and `2 * k - 2` are natural-number subtractions; since `k ≥ 1`
they are the ordinary `k - 1` and `2k - 2`. -/
def Claim : Prop :=
  ∀ k n : ℕ, 1 ≤ k → 2 ≤ n →
    let φ : ℚ := (Nat.totient n : ℚ)
    let ψ : ℚ := (dedekindPsi n : ℚ)
    let σ : ℚ := (sumDivisors n : ℚ)
    let N : ℚ := (n : ℚ)
    (N * (N + 1) ^ (k - 1) * (N - 1) ^ k + (N - 1) ^ (2 * k)
          + 4 * N ^ 2 * (N + 1) ^ (2 * k - 2))
        / (2 * N ^ 2 * (N + 1) ^ (2 * k - 2) + 2 * N * (N + 1) ^ (k - 1) * (N - 1) ^ k)
      ≤ φ ^ k * (ψ + σ) / (ψ ^ k * (φ + σ) + σ ^ k * (φ + ψ))
        + ψ ^ k * (φ + σ) / (φ ^ k * (ψ + σ) + σ ^ k * (φ + ψ))
        + σ ^ k * (φ + ψ) / (φ ^ k * (ψ + σ) + ψ ^ k * (φ + σ))
