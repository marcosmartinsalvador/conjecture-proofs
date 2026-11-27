# Unimodal products of q-analogs: one clause of the conjecture is false

**Disproved as printed here, but someone else had it first.** This is a known result, not a new one.

| | |
|---|---|
| Kind | Known result |
| Outcome | Disproved as printed |
| Source | [B. B. Connelly, E. Ito, T. C. Martinez, O. Shevchenko, K. Yang, "Unimodality of q-Fibonomial coefficients for small cases", arXiv:2605.12822v1 (12 May 2026), the conjecture of the last section](https://arxiv.org/abs/2605.12822) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | No. See [who had it first](#who-had-it-first). |

## In plain words

A conjecture on when a product of q-analogs is unimodal. One clause of its second sentence ("necessary when p ≤ 3") is false, so the conjecture is disproved as printed. Its main sentence is still open.

## The statement as printed

B. B. Connelly, E. Ito, T. C. Martinez, O. Shevchenko, K. Yang, "Unimodality of q-Fibonomial coefficients for small cases", arXiv:2605.12822v1 (12 May 2026), the conjecture of the last section.

> **Conjecture.** Let $p \geq 2, k \geq 1$ and let $a_1,\ldots, a_k,b$ be positive
> integers. Then if $p \mid a_i$ for any $1 \leq i \leq k$ or
> $$b \leq 1+\sum_{i=1}^{k}\left\lfloor\frac{a_i}{p}\right\rfloor,$$
> the polynomial $[a_1]_q\dots[a_k]_q[b]_{q^{p}}$ is unimodal. Moreover, if
> $k \leq 3$ or $p \leq 3$, this condition is also necessary.
>
> We have computationally verified [the conjecture] for $k \leq 5, p \leq 6$ and
> $\max\{a_i,b\} \leq 15$. In general, the condition is not necessary:
> $([3]_q)^4 [2]_{q^4}$ is unimodal despite violating the inequality
> $b \leq 1 + \sum_{i=1}^{k}\lfloor \frac{a_i}{p} \rfloor$.

## What is proved here

The conjecture has two sentences.

1. "If the condition holds, the polynomial is unimodal." **Not settled.** Nothing in
   this folder proves or disproves it. A computer search found no counterexample
   (ranges below).
2. "Moreover, if k ≤ 3 or p ≤ 3, the condition is also necessary." **False for p = 3.**
   Take k = 6, a_1 = ... = a_6 = 2, b = 2, p = 3. The polynomial is
   (1 + q)^6 (1 + q^3) = 1 + 6q + 15q^2 + 21q^3 + 21q^4 + 21q^5 + 21q^6 + 15q^7 + 6q^8 + q^9,
   which is unimodal. But 3 does not divide 2, and b = 2 > 1 + 6·⌊2/3⌋ = 1, so the
   condition fails.

So the conjecture as printed is false, but only because of the p ≤ 3 half of its
second sentence. `Claim` says exactly this, in three parts: the example is unimodal,
the example does not satisfy the condition, and the printed conjecture (both
sentences together, as one statement) does not hold. The counterexample sits just
outside the range the authors checked (they went up to k = 5; this needs k = 6).

## Idea of the proof

Expand the product, read off the ten coefficients, and check the two chains of
inequalities by cases. The "not the condition" part is arithmetic.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=qanalog_product_unimodality  result : Claim  (Claim as defined in conjectures/qanalog_product_unimodality/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: fb9e680cbb2b788a   proof sha256: dacc03d38c9b1855   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Who had it first

The same counterexample with a Lean proof, in `the-omega-institute/trureturing`, merged 10 September 2026.

This result is kept here because the proof was found and checked independently, before the earlier work was known to this repository. It is not claimed as new.

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`result.json`](result.json): the data behind this result's row on the front page
