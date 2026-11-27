# Dimitrov's Conjecture 1

**Proved here, but someone else published it first.** This is a known result, not a new one.

| | |
|---|---|
| Kind | Known result |
| Outcome | Proved |
| Source | [S. I. Dimitrov, "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III", arXiv:2606.12484v1 (June 2026), Conjecture 1](https://arxiv.org/abs/2606.12484) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-25 |
| New? | No. See [who had it first](#who-had-it-first). |

## In plain words

Conjecture 1 of the paper: a lower bound, for every n ≥ 2 and every power k ≥ 1, on an expression built from Euler's φ, Dedekind's ψ and the sum of divisors σ. It is proved here.

## The statement as printed

S. I. Dimitrov, "Lower bounds on expressions depending on the functions φ(n), ψ(n) and σ(n), III", arXiv:2606.12484v1 (June 2026), Conjecture 1.

> **Conjecture 1.** For every integers $k\geq1$ and $n\geq2$, we have
> $$\big(\varphi^k(n)+\psi^k(n)+\sigma^k(n)\big)\left(\frac{1}{\varphi^k(n)}+\frac{1}{\psi^k(n)}+\frac{1}{\sigma^k(n)}\right)\geq\frac{5(n^2-1)^k+2(n+1)^{2k}+2(n-1)^{2k}}{(n^2-1)^k}\,.$$
>
> **Remark.** Following the method used in the proof of Theorem 1, it is not
> difficult to see that Conjecture 1 holds for $k=2$ and $k=3$.

## What is proved here

`Claim` is the displayed inequality for all integers k ≥ 1 and n ≥ 2, with φᵏ(n) read as the k-th power of φ(n).

The three functions, for $n = \prod_i p_i^{a_i} \ge 2$:

- $\varphi(n) = \prod_i p_i^{a_i-1}(p_i-1)$, $\varphi(1)=1$: Euler's totient,
  "the number of integers up to $n$ that are relatively prime to $n$".
- $\psi(n) = \prod_i p_i^{a_i-1}(p_i+1)$, $\psi(1)=1$: the Dedekind psi function.
- $\sigma(n) = \prod_i \frac{p_i^{a_i+1}-1}{p_i-1}$, $\sigma(1)=1$: "the sum-of-divisors function".

**How the Lean statement reads the source.**

- $\varphi^k(n)$ means the $k$-th power $(\varphi(n))^k$, not the $k$-fold iterate.
  Evidence: the $k=1$ case is the paper's Theorem 1, whose right-hand side
  $(9n^2-1)/(n^2-1)$ equals the conjecture's right-hand side at $k=1$; and at a
  prime $n$ (φ = n−1, ψ = σ = n+1) the two sides are equal with powers.
  The paper's introduction also uses $\varphi^k(n)$ for powers throughout.
- In `Statement.lean`, φ is Mathlib's `Nat.totient`; ψ and σ are defined in the
  file itself (ψ by the paper's product formula, σ as the sum over `n.divisors`).
  Values for n = 1..12 were compared with OEIS A001615 (ψ) and A000203 (σ).
- The inequality is between rational numbers and is stated in `ℚ`.

## Idea of the proof

Write a = φ(n)^k, b = ψ(n)^k, c = σ(n)^k, u = (n−1)^k, v = (n+1)^k. Then
0 < a ≤ u ≤ v ≤ b, c because φ(n) ≤ n−1 and ψ(n), σ(n) ≥ n+1 for n ≥ 2. The left
side is 3 + (b/a + a/b) + (c/a + a/c) + (b/c + c/b) and the right side is
5 + 2(v/u + u/v). Since x + 1/x increases for x ≥ 1 and b/a, c/a ≥ v/u ≥ 1, the
first two brackets are each ≥ v/u + u/v; the third is ≥ 2. No induction needed.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=phi_psi_sigma_power_bound  result : Claim  (Claim as defined in conjectures/phi_psi_sigma_power_bound/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: 1b799655ae4db8a3   proof sha256: 5fc5205e02f8129a   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Who had it first

A public Lean proof, `pro20541/dimitrov-conjectures-lean`, September 2026.

This result is kept here because the proof was found and checked independently, before the earlier work was known to this repository. It is not claimed as new.

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`result.json`](result.json): the data behind this result's row on the front page
