# Dimitrov's Conjecture 7

**Proved here, but someone else published it first.** This is a known result, not a new one.

| | |
|---|---|
| Kind | Known result |
| Outcome | Proved |
| Source | [S. I. Dimitrov, "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III", arXiv:2606.12484v1 (June 2026), Conjecture 7](https://arxiv.org/abs/2606.12484) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | No. See [who had it first](#who-had-it-first). |

## In plain words

Conjecture 7 of the paper: a lower bound, for every n ≥ 2 and every power k ≥ 1, on an expression built from Euler's φ, Dedekind's ψ and the sum of divisors σ. It is proved here.

## The statement as printed

S. I. Dimitrov, "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III", arXiv:2606.12484v1 (June 2026), Conjecture 7.

```latex
\begin{conjecture}\label{Conjecture7}
For every integers $k\geq1$ and $n\geq2$, we have
\begin{align*}
&\frac{\big(\varphi(n)+\psi(n)\big)^k}{\big(\varphi(n)+\sigma(n)\big)^k+\big(\psi(n)+\sigma(n)\big)^k}+\frac{\big(\varphi(n)+\sigma(n)\big)^k}{\big(\varphi(n)+\psi(n)\big)^k+\big(\psi(n)+\sigma(n)\big)^k}\\
&+\frac{\big(\psi(n)+\sigma(n)\big)^k}{\big(\varphi(n)+\psi(n)\big)^k+\big(\varphi(n)+\sigma(n)\big)^k}\geq\frac{4n^{2k}+(n+1)^{2k}+n^k(n+1)^k}{2\big(n^{2k}+n^k(n+1)^k\big)}\,. 
\end{align*}
\end{conjecture}
```

## What is proved here

`Claim` is the displayed inequality for all integers k ≥ 1 and n ≥ 2, with φᵏ(n) read as the k-th power of φ(n).

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

Write x = (φ+ψ)^k, y = (φ+σ)^k, z = (ψ+σ)^k, U = n^k, V = (n+1)^k. The left side is the
Nesbitt expression x/(y+z) + y/(x+z) + z/(x+y) and the right side is V/(2U) + 2U/(U+V), its
value at (U, U, V). With one big term z (z/x ≥ V/U and z/y ≥ V/U) the Nesbitt expression is
at least that value (`nesbitt_big`). The two ratio bounds are n(ψ+σ) ≥ (n+1)(φ+ψ) and
n(ψ+σ) ≥ (n+1)(φ+σ); both follow from the key inequality (n+1)φ(n) + σ(n) ≤ nψ(n)
(`key_ineq`) together with ψ(n) ≤ σ(n) (`psi_le_sigma`).

`Basic.lean` holds the helper lemmas and is identical in the seven folders
`dimitrov3_conj2`, `dimitrov3_conj4`, ..., `dimitrov3_conj9` except for its import line.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=dimitrov3_conj7  result : Claim  (Claim as defined in conjectures/dimitrov3_conj7/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: 7e35e08876207a1f   proof sha256: 8bc3a6b30bc69cce   files:Statement Basic Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Who had it first

`the-omega-institute/trureturing`, issue 30579: that group's public record says the full statement was proved in Lean and checked independently on their side on 14 to 15 November 2026, twelve days before the proof here. They had not published the proof when this was checked, so it could not be read or compared.

This result is kept here because the proof was found and checked independently, before the earlier work was known to this repository. It is not claimed as new.

## Files

- [`Basic.lean`](Basic.lean): helper lemmas imported by the proof
- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`result.json`](result.json): the data behind this result's row on the front page
