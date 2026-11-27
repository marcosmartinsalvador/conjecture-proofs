# Only 24 and 40 are Δ-primitive among numbers with two prime factors

**Proved.** A full resolution of the conjecture as stated in the source.

| | |
|---|---|
| Kind | Full resolution |
| Outcome | Proved |
| Source | [V. N. Schvöllner, "The Δ property: a bridge between split graphs and Number Theory", arXiv:2605.25264v1 (24 May 2026). The conjecture is already in the author's 2025 thesis (arXiv:2507.13479)](https://arxiv.org/abs/2605.25264) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | Fairly sure. See [is it new?](#is-it-new) |

## In plain words

A number n has the "Δ property" when one difference of two divisors that multiply to n is the sum of two such differences (for 24: 12 − 2 = 10 = 5 + 5, where 5 = 8 − 3). It is "Δ-primitive" when it is not a square times a smaller number with the property. The conjecture says that among the numbers pˣqʸ built from two different primes, only 24 and 40 are Δ-primitive. The paper itself proves only the case y = 1.

## The statement as printed

V. N. Schvöllner, "The Δ property: a bridge between split graphs and Number Theory", arXiv:2605.25264v1 (24 May 2026). The conjecture is already in the author's 2025 thesis (arXiv:2507.13479).

> Based on experimental evidence, we conjecture that 24 and 40 are the only
> $\Delta$-primitive numbers using exactly two primes in their decomposition.
>
> Let $n$ be a natural number of the form $p^x q^y$, where $p$ and $q$ are distinct
> primes and $x, y\in\mathbb{N}$. If $n$ is $\Delta$-primitive, then $n \in \{24, 40\}$.

## What is proved here

`Claim`: if n = pˣqʸ with p ≠ q primes and x, y ≥ 1 is Δ-primitive, then n is 24 or 40. `Statement.lean` follows the paper's definitions word for word. The exponents are at least 1 because the paper's ℕ starts at 1; allowing 0 would not change the truth of the statement, since a prime power never has the Δ property.

## Idea of the proof

The proof shows slightly more than the claim: if n = pˣqʸ is primitive and has the Δ property, then the three divisor pairs involved force n ∈ {24, 40, 216}, and 216 = 3² · 24 is not primitive. The full argument on paper, in seven steps, is in [`PROOF_NOTES.md`](PROOF_NOTES.md); `Proof.lean` follows those steps. `check.py` tests each step of the paper proof that can be tested by computer.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=delta_primitive_two_primes  result : Claim  (Claim as defined in conjectures/delta_primitive_two_primes/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: 79fdbcb32663f560   proof sha256: 59b55b16a6d1534d   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Is it new?

**Fairly sure.** Nothing was found on arXiv, the web or GitHub. Another public group started work on the author's follow-up paper the day before this proof was checked.

What was searched, and what could not be, is in [the prior-art note](../../docs/prior-art.md). No search can show that nobody did this before; if you know of earlier work, please [open an issue](../../README.md#corrections).

## Files

- [`PROOF_NOTES.md`](PROOF_NOTES.md): the proof on paper, step by step
- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`check.py`](check.py): an independent numerical check in plain Python (not part of the Lean proof)
- [`result.json`](result.json): the data behind this result's row on the front page
