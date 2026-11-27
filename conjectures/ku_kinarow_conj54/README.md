# Ku's Conjecture 5.4 on the torus board is false

**Disproved.** A full resolution of the conjecture as stated in the source.

| | |
|---|---|
| Kind | Full resolution |
| Outcome | Disproved |
| Source | [K.-H. Ku, "Monochromatic k in a row", arXiv:2606.12880v1 (June 2026), Conjecture 5.4](https://arxiv.org/abs/2606.12880) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | Fairly sure. See [is it new?](#is-it-new) |

## In plain words

The conjecture says: when k is a multiple of 3, no set of at most 2k+2 points on the k × k torus board meets every row, column and diagonal at least twice. Such sets with exactly 2k+2 points exist for k = 6 (14 points) and k = 9 (20 points).

This closes one route the paper proposed. It does not refute the paper's Conjectures 5.1 or 5.2.

## The statement as printed

K.-H. Ku, "Monochromatic k in a row", arXiv:2606.12880v1 (June 2026), Conjecture 5.4.

> **Conjecture 5.4.** For every $k\in 3\mathbb{N}$, there is no subset $A\subseteq (\mathbb{Z}/k\mathbb{Z})^2$ with $|A|\leq 2k+2$ satisfying $|L\cap A|\geq 2$ for every axis-parallel or diagonal line $L$.

## What is proved here

`Claim` = (a set with at most 2k+2 points meeting every line at least twice exists for
k = 6) and (the same for k = 9) and (the conjecture, quantified over all positive
multiples k of 3, is false).

**How the Lean statement reads the source.**

- "$k \in 3\mathbb{N}$" is read as "k is a positive multiple of 3" (`0 < k` and `3 ∣ k`
  in `KuConjecture`).
- k = 3: here 2k+2 = 8 and the whole board has 9 points. Removing any one point leaves 8
  points, and every line (3 points) still has at least 2 of them. So the conjecture is
  false at k = 3 for a trivial reason. The paper itself notes D(3, (ℤ/3ℤ)²) = 1/9 and,
  in the sentence before the conjecture, speaks of "every k ∈ 3ℕ \ {3}". This is why
  `Claim` gives k = 6 and k = 9 explicitly: the disproof does not rest on k = 3 or on
  how one reads 3ℕ.
- The eight directions are listed twice up to sign (d and −d give the same line), as in
  the paper. This changes nothing.
- The failure of 5.4 does not refute Conjecture 5.1 or 5.2. It only closes the route the
  paper proposed for proving 5.2.

## Idea of the proof

**The counterexamples.**

`#` marks a point of A; rows are y = 0, 1, ..., columns are x = 0, 1, ....

k = 6, 14 = 2k+2 points:

```
##....
##....
..###.
#....#
.##...
...###
```

k = 9, 20 = 2k+2 points:

```
.#......#
...#..#..
#..#..#..
..#....#.
..#..#...
....#..#.
#.....#..
.#.##....
.....#..#
```

Sets of size 2k+2 were also found for k = 12 (26 points) and k = 15 (32 points). They
are in `search/verify.py`, which re-checks all four sets with plain Python. They are not
in the Lean proof (k = 6 and 9 are enough).

Give the two sets and let Lean check every line by computation (`decide`), then apply
the conjecture's own statement at k = 6 to get a contradiction.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=ku_kinarow_conj54  result : Claim  (Claim as defined in conjectures/ku_kinarow_conj54/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: ca2c5350a0b65be7   proof sha256: c256d43b198eb606   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Is it new?

**Fairly sure.** Nothing was found anywhere. The one other public project known to have worked on this paper wrote that it had not taken this conjecture up.

What was searched, and what could not be, is in [the prior-art note](../../docs/prior-art.md). No search can show that nobody did this before; if you know of earlier work, please [open an issue](../../README.md#corrections).

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`search/`](search): the programs that found the examples (not part of the Lean proof)
- [`result.json`](result.json): the data behind this result's row on the front page
