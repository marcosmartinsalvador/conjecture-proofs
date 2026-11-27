# Random equations on a cycle: the printed formula is wrong, the corrected one is proved

**Disproved as printed; corrected formula proved.** A full resolution of the conjecture as stated in the source.

| | |
|---|---|
| Kind | Full resolution |
| Outcome | Disproved as printed; corrected formula proved |
| Source | [P. Horak, I. Semaev, "Inconsistency Probability of Sparse Equations over F2", arXiv:2603.24890v1 (26 March 2026), the conjecture of the last subsection](https://arxiv.org/abs/2603.24890) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | Fairly sure. See [is it new?](#is-it-new) |

## In plain words

Put one random equation in two variables on each edge of a cycle with n edges. The paper conjectures an exact formula for the chance that the system has a solution. The formula as printed is false for every n ≥ 3, and the correct formula is proved here: the last term must be 1/(2·8ⁿ), not 1/8ⁿ⁻¹.

This should not be described as "the paper's conjecture proved": the corrected formula is a statement made here, and it is not known which formula the authors meant. Most likely the last term is a misprint.

## The statement as printed

P. Horak, I. Semaev, "Inconsistency Probability of Sparse Equations over F2", arXiv:2603.24890v1 (26 March 2026), the conjecture of the last subsection.

> **Conjecture.** The consistency probability of the cycle $C_{n}$ is given by
> $$q(C_{n})=s^{n}+t^{n}-\frac{1}{4^{n}}-\frac{1}{8^{n-1}},$$
> where $s=\frac{17+\sqrt{97}}{32},t=\frac{17-\sqrt{97}}{32}.$

## What is proved here

The formula as printed is **false**, and the true value is

$$q(C_{n})=s^{n}+t^{n}-\frac{1}{4^{n}}-\frac{1}{2\cdot 8^{n}}\qquad(n\ge 3).$$

The last term in the paper is 16 times too large. For example the triangle has
$q(C_3)=2397/4096$ (direct count over all $16^3$ systems), while the printed formula gives
$2337/4096$. So the paper's statement that the computed values for $n=3,\dots,7$ agree with
the printed formula cannot be right as printed; most likely the last term is a misprint.

`Claim` in `Statement.lean` says both things for every $n\ge3$: the exact value above, and
that the printed formula is not equal to $q(C_n)$.

**How the Lean statement reads the source.**

- Vertices of $C_n$ are `ZMod n`; edge `i` joins `i` and `i + 1`. For `n ≥ 3` this is the
  simple cycle with `n` vertices and `n` edges.
- The equation on edge `i` is `f i (x i) (x (i + 1)) = 0` with `f i : ZMod 2 → ZMod 2 → ZMod 2`
  arbitrary. Every function $\mathbb F_2^2\to\mathbb F_2$ is a polynomial function, and there
  are 16 of them, as in the paper. Which endpoint is the first argument does not matter,
  because all 16 functions are allowed.
- `qCycle n` is the number of consistent systems (as `Nat.card` of a subtype) divided by
  `16 ^ n` $=2^{4m}$ with $m=n$ edges.

## Idea of the proof

Record each equation as a 2x2 Boolean matrix (entry $(a,b)$ is 1 when $f(a,b)=0$). The
system on the cycle is consistent exactly when the Boolean product of the $n$ matrices has
a nonzero diagonal entry. The number of sequences of $n\ge1$ Boolean matrices with a given
product has a closed form in terms of $16^n, 4^n, 2^n$ and the sequence
$u_0=0,u_1=1,u_{n+2}=17u_{n+1}-48u_n$ (table `G` in `Proof.lean`); it is proved by induction,
the step being one finite identity. Adding up gives
$\#\{\text{consistent}\} = 2u_{n+1}-17u_n-4^n-2^{n-1}$, and
$2u_{n+1}-17u_n=\big(\tfrac{17+\sqrt{97}}2\big)^n+\big(\tfrac{17-\sqrt{97}}2\big)^n$.

**Independent numerical check.**

`python3 conjectures/cycle_consistency_probability/check.py` counts consistent systems
directly for $n=3,4$ (all $16^n$ systems, all $2^n$ assignments) and by multiplying Boolean
matrices for $n\le 15$, and compares with both formulas. The corrected formula matches every
value; the printed one matches none.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=cycle_consistency_probability  result : Claim  (Claim as defined in conjectures/cycle_consistency_probability/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: b264571a2bd44263   proof sha256: 5078ae5fe4304fd0   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Is it new?

**Fairly sure.** Nothing was found anywhere on this conjecture.

What was searched, and what could not be, is in [the prior-art note](../../docs/prior-art.md). No search can show that nobody did this before; if you know of earlier work, please [open an issue](../../README.md#corrections).

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`check.py`](check.py): an independent numerical check in plain Python (not part of the Lean proof)
- [`result.json`](result.json): the data behind this result's row on the front page
