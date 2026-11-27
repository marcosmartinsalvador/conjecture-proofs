# Dimitrov's Conjecture 2

**Proved.** A full resolution of the conjecture as stated in the source.

| | |
|---|---|
| Kind | Full resolution |
| Outcome | Proved |
| Source | [S. I. Dimitrov, "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III", arXiv:2606.12484v1 (June 2026), Conjecture 2](https://arxiv.org/abs/2606.12484) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | Less sure. See [is it new?](#is-it-new) |

## In plain words

A lower bound, for every n ≥ 2 and every power k ≥ 1, on an expression built from Euler's φ, Dedekind's ψ and the sum of divisors σ, with equality when n is prime.

## The statement as printed

S. I. Dimitrov, "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III", arXiv:2606.12484v1 (June 2026), Conjecture 2.

```latex
\begin{conjecture}\label{Conjecture2}
For every integers $k\geq1$ and $n\geq2$, we have
\begin{align*}
&\big((\varphi(n)+\psi(n))^k +(\varphi(n)+\sigma(n))^k+(\psi(n)+\sigma(n))^k\big)\\
&\times\left(\frac{1}{(\varphi(n)+\psi(n))^k}+\frac{1}{(\varphi(n)+\sigma(n))^k}+\frac{1}{(\psi(n)+\sigma(n))^k}\right)\\ 
&\geq\frac{5n^k(n+1)^k+2(n+1)^{2k}+2n^{2k}}{n^k(n+1)^k}\,.
\end{align*}
\end{conjecture}
```

## What is proved here

`Claim` is the displayed inequality for all integers k ≥ 1 and n ≥ 2.

The three functions, for $n = \prod_i p_i^{a_i} \ge 2$:

- $\varphi(n) = \prod_i p_i^{a_i-1}(p_i-1)$, $\varphi(1)=1$: Euler's totient.
- $\psi(n) = \prod_i p_i^{a_i-1}(p_i+1)$, $\psi(1)=1$: the Dedekind psi function.
- $\sigma(n) = \prod_i \frac{p_i^{a_i+1}-1}{p_i-1}$, $\sigma(1)=1$: the sum-of-divisors function.

**How the Lean statement reads the source.**

- $\varphi^k(n)$ means the $k$-th power $(\varphi(n))^k$, not the $k$-fold iterate (same reading as for Conjecture 1, folder `phi_psi_sigma_power_bound`).
- `Statement.lean` uses the same definitions of ψ and σ as `phi_psi_sigma_power_bound`
  (ψ by the paper's product formula, σ as the sum over `n.divisors`); φ is `Nat.totient`.
- The statement uses `let` to name φ(n), ψ(n), σ(n) and n as rational numbers, so the
  formula reads like the paper's.
- Numeric cross-check: the Lean formula text, translated
  mechanically to Python, equals an independent transcription of the paper's formula for
  all 2 ≤ n < 120, 1 ≤ k ≤ 5 (exact rational arithmetic); the two sides are equal exactly
  at primes and the inequality is strict at composites in that range.

## Idea of the proof

Write x = (φ+ψ)^k, y = (φ+σ)^k, z = (ψ+σ)^k, U = n^k, V = (n+1)^k. The left side is
3 + (z/x + x/z) + (z/y + y/z) + (x/y + y/x) and the right side is 5 + 2(V/U + U/V).
Since t + 1/t increases for t ≥ 1, it is enough that z/x ≥ V/U and z/y ≥ V/U, that is
n(ψ+σ) ≥ (n+1)(φ+ψ) and n(ψ+σ) ≥ (n+1)(φ+σ). Both follow from the key inequality
(n+1)φ(n) + σ(n) ≤ nψ(n) (`key_ineq`) together with ψ(n) ≤ σ(n) (`psi_le_sigma`).

`Basic.lean` holds the helper lemmas and is identical in the seven folders
`dimitrov3_conj2`, `dimitrov3_conj4`, ..., `dimitrov3_conj9` except for its import line.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=dimitrov3_conj2  result : Claim  (Claim as defined in conjectures/dimitrov3_conj2/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: 6431772db73ffefb   proof sha256: f62b16c6ee3cabcc   files:Statement Basic Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Is it new?

**Less sure.** No proof of it was found anywhere. The reason for doubt: `the-omega-institute/trureturing` tried this conjecture on 14 November 2026 and recorded it as unresolved, and on 19 November that group published the same key step this proof uses, (n+1)φ(n) + σ(n) ≤ nψ(n), naming this conjecture as its use. A finished proof on their side that is not public yet would not be surprising.

What was searched, and what could not be, is in [the prior-art note](../../docs/prior-art.md). No search can show that nobody did this before; if you know of earlier work, please [open an issue](../../README.md#corrections).

## Files

- [`Basic.lean`](Basic.lean): helper lemmas imported by the proof
- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`result.json`](result.json): the data behind this result's row on the front page
