# Dimitrov's Conjecture 8

**Proved here, but someone else had it first.** This is a known result, not a new one.

| | |
|---|---|
| Kind | Known result |
| Outcome | Proved |
| Source | [S. I. Dimitrov, "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III", arXiv:2606.12484v1 (June 2026), Conjecture 8](https://arxiv.org/abs/2606.12484) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | No. See [who had it first](#who-had-it-first). |

## In plain words

Conjecture 8 of the paper: a lower bound, for every n ≥ 2 and every power k ≥ 1, on an expression built from Euler's φ, Dedekind's ψ and the sum of divisors σ. It is proved here.

## The statement as printed

S. I. Dimitrov, "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III", arXiv:2606.12484v1 (June 2026), Conjecture 8.

```latex
\begin{conjecture}\label{Conjecture8}
For every integers $k\geq1$ and $n\geq2$, we have
\begin{align*}
&\frac{\varphi^k(n)\big(\psi(n)+\sigma(n)\big)}{\psi^k(n)\big(\varphi(n)+\sigma(n)\big)+\sigma^k(n)\big(\varphi(n)+\psi(n)\big)}
+\frac{\psi^k(n)\big(\varphi(n)+\sigma(n)\big)}{\varphi^k(n)\big(\psi(n)+\sigma(n)\big)+\sigma^k(n)\big(\varphi(n)+\psi(n)\big)}\\
&+\frac{\sigma^k(n)\big(\varphi(n)+\psi(n)\big)}{\varphi^k(n)\big(\psi(n)+\sigma(n)\big)+\psi^k(n)\big(\varphi(n)+\sigma(n)\big)}\\
&\geq\frac{n(n+1)^{k-1}(n-1)^k+(n-1)^{2k}+4n^2(n+1)^{2k-2}}{2n^2(n+1)^{2k-2}+2n(n+1)^{k-1}(n-1)^k}\,.
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

Write x = φ^k(ψ+σ), y = ψ^k(φ+σ), z = σ^k(φ+ψ), P = n(n+1)^(k-1), Q = (n-1)^k. The left
side is the Nesbitt expression x/(y+z) + y/(x+z) + z/(x+y) and the right side is
Q/(2P) + 2P/(P+Q), its value at (Q, P, P). With one small term x (y/x ≥ P/Q and z/x ≥ P/Q,
lemma `hypA`) the Nesbitt expression is at least that value (`nesbitt_small`). Only
φ ≤ n-1, ψ ≥ n+1, σ ≥ n+1 are used.

`Basic.lean` holds the helper lemmas and is identical in the seven folders
`dimitrov3_conj2`, `dimitrov3_conj4`, ..., `dimitrov3_conj9` except for its import line.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=dimitrov3_conj8  result : Claim  (Claim as defined in conjectures/dimitrov3_conj8/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: a9747a5d84a94574   proof sha256: cb08d50ca7da2760   files:Statement Basic Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Who had it first

A public Lean proof in `the-omega-institute/trureturing`, merged 14 November 2026.

This result is kept here because the proof was found and checked independently, before the earlier work was known to this repository. It is not claimed as new.

## Files

- [`Basic.lean`](Basic.lean): helper lemmas imported by the proof
- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`result.json`](result.json): the data behind this result's row on the front page
