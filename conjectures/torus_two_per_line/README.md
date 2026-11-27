# No set meets every line of the k × k torus exactly twice when 3 divides k

**Proved here, but someone else had it first.** This is a known result, not a new one.

| | |
|---|---|
| Kind | Known result |
| Outcome | Proved |
| Source | [K.-H. Ku, "Monochromatic k in a row", arXiv:2606.12880v1 (June 2026), the restatement of Conjecture 5.1](https://arxiv.org/abs/2606.12880) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | No. See [who had it first](#who-had-it-first). |

## In plain words

When k is a multiple of 3, no set of points on the k × k torus board meets every row, column and diagonal exactly twice. Proved.

## The statement as printed

K.-H. Ku, "Monochromatic k in a row", arXiv:2606.12880v1 (June 2026), the restatement of Conjecture 5.1.

> **Conjecture (Restatement of Conjecture \ref{conj:D(k,Z2)}).** For every $k\in 3\N$,
> there is no subset $A\subseteq (\Z/k\Z)^2$ satisfying $|L\cap A|=2$ for every
> axis-parallel or diagonal line $L$.

## What is proved here

Conjecture 5.1 is "For every $k\in 3\mathbb{N}$, $D(k,\mathbb{Z}^2)<1-\frac{2}{k}$" ($D$ = the largest
density of a set of the grid with no $k-1$ points on a $k$-line). Just before the
restatement the paper argues, using its Theorem on the torus, that for each $k \in 3\mathbb{N}$
these are equivalent: (a) $D(k,\mathbb{Z}^2)<1-2/k$; (b) $D(k,(\mathbb{Z}/k\mathbb{Z})^2)<1-2/k$; (c) the
statement above. **Only (c) is formalized and proved here.** That (c) gives (a) rests on
the paper's own argument, which is not checked in Lean.

## Idea of the proof

This is Polya's argument for queens on a torus. The four kinds of line are the level
sets of $x$, $y$, $x-y$ and $x+y$. If each level set meets $A$ in exactly 2 points, then
the sum over $A$ of $x^2$ is $2S$ with $S = 0^2+1^2+\dots+(k-1)^2$ (in $\mathbb{Z}/k\mathbb{Z}$), and the
same for $y^2$, $(x-y)^2$, $(x+y)^2$. Since $(x+y)^2+(x-y)^2 = 2x^2+2y^2$, we get
$4S = 8S$, so $k$ divides $4S = 2k(k-1)(2k-1)/3$. Then $3$ divides $2(k-1)(2k-1)$, which
is $2$ modulo 3 when $3 \mid k$. Contradiction.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=torus_two_per_line  result : Claim  (Claim as defined in conjectures/torus_two_per_line/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: 6eed629d22b9adbd   proof sha256: 5098ced8389cfef8   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Who had it first

A proof in words in `the-omega-institute/trureturing`, 4 November 2026. The proof here is the first machine-checked one known to this repository.

This result is kept here because the proof was found and checked independently, before the earlier work was known to this repository. It is not claimed as new.

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`result.json`](result.json): the data behind this result's row on the front page
