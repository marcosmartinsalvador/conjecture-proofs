# Ultra-Euclidean functions: the refinement conjecture is false

**Disproved.** A full resolution of the conjecture as stated in the source.

| | |
|---|---|
| Kind | Full resolution |
| Outcome | Disproved |
| Source | [S. Sekhon, "A Necessary and Sufficient Condition for Uniqueness of Euclidean Division", arXiv:2604.24399v2 (April 2026), section "Further investigation"](https://arxiv.org/abs/2604.24399) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | Fairly sure, with one gap. See [is it new?](#is-it-new) |

## In plain words

The paper calls a Euclidean function f "ultra-Euclidean" when f(a+b) ≤ max(f(a), f(b)), and conjectures that the "refinement" of such an f (the smallest value f takes on the multiples of a) is ultra-Euclidean too. It is not: an explicit function on the Laurent polynomials ℚ[T, T⁻¹] is a counterexample. The author writes that he could not prove or disprove the conjecture.

## The statement as printed

S. Sekhon, "A Necessary and Sufficient Condition for Uniqueness of Euclidean Division", arXiv:2604.24399v2 (April 2026), section "Further investigation".

> **Conjecture.** If $f$ is ultra-Euclidean on $R$, so is $\tilde f$.

## What is proved here

**Both statements are false.** `Statement.lean` here states the negation of the "Conjecture", and
`Proof.lean` proves it.

**How the Lean statement reads the source.**

- `Statement.lean` is the plain negation of the paper's sentence, quantified over all
  integral domains `R : Type` (`[CommRing R] [IsDomain R]`), with the paper's definitions
  copied literally.
- The paper's `f` is defined on `R ∖ {0}` with values in `ℤ≥0`. `Statement.lean` uses a
  total `f : R → ℕ`. The value `f 0` never matters: in the Euclidean condition it only
  appears as `f r` in a disjunction whose other side is `r = 0`, the ultra inequality is
  only asked for nonzero `a, b, a + b`, and (R being a domain) `f̃(a)` for `a ≠ 0` only
  looks at `f` on nonzero elements.
- The refinement is written as `sInf` of the set `{f (a b) | b ≠ 0}` of natural numbers.
  For `a ≠ 0` (indeed for any `a`) the set is nonempty, so `sInf` is its minimum, as in
  the paper.
- The counterexample is a specific ring in `Type`, so restricting `R` to `Type` (rather
  than any universe) loses nothing for a disproof.

## Idea of the proof

Take the Laurent polynomials `R = ℚ[T, T⁻¹]` (any field works in place of ℚ). For
`n = 0, 1, 2, ...` let `B_n` be the Laurent polynomials whose exponents all lie in the
window `[-⌊n/2⌋, ⌈n/2⌉]`, a run of `n + 1` consecutive integers:
`{0}`, `{0,1}`, `{-1,0,1}`, `{-1,0,1,2}`, ... The windows grow by one exponent at a time
and cover all of ℤ. Put `f(a) = ` the least `n` with `a ∈ B_n`.

- **Ultra inequality.** Each `B_n` is closed under addition and the `B_n` increase, so
  `f(a+b) ≤ max(f(a), f(b))`.
- **Euclidean.** Let `b ≠ 0` with `f(b) = n`. Up to a power of `T` (a unit), `b` is an
  ordinary polynomial `Q` with nonzero constant term and degree `d ≤ n`. Since `T` is
  invertible modulo `Q`, every Laurent polynomial is congruent modulo `Q` to an ordinary
  polynomial, hence to one of degree `< d`. Applying this to `a·T^s` and shifting back,
  `a ≡ r (mod b)` with `r` having exponents in any chosen window of `d ≤ n` consecutive
  integers, in particular inside `B_{n-1}` when `n ≥ 1`; so `r = 0` or `f(r) ≤ n-1 < f(b)`.
  If `n = 0` then `d = 0`, `b` is a unit and `r = 0`.
- **The refinement is not ultra-Euclidean.** `f̃(1) = f(1) = 0` and
  `f̃(-T) ≤ f((-T)(-T⁻¹)) = f(1) = 0`. But `1 - T` is not a unit (it is killed by `T ↦ 1`),
  so no nonzero multiple of it is a constant, so `f̃(1 - T) ≥ 1 > max(f̃(1), f̃(-T))`.
- **`R` is not a field and not a polynomial ring over a field.** `1 - T` is a nonzero
  non-unit, so `R` is not a field. In `K[x]` the units together with `0` are closed under
  addition (they are the constants); in `R` the units `1` and `-T` add up to the nonzero
  non-unit `1 - T`. So no ring isomorphism `R ≅ K[x]` exists.

This matches the paper's own remark: here `f` is not strongly Euclidean
(`f(T) = 1 > 0 = f(T·T⁻¹)`), and `f̃` is strongly Euclidean but not ultra-Euclidean.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=ultra_euclidean_refinement_false  result : Claim  (Claim as defined in conjectures/ultra_euclidean_refinement_false/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: 82dc275a0cbc53e6   proof sha256: 895c2e106a082941   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Is it new?

**Fairly sure, with one gap.** Nothing was found anywhere. The gap: the older papers on unique Euclidean division (from the 1960s on) could not be searched, and a similar example could sit there.

What was searched, and what could not be, is in [the prior-art note](../../docs/prior-art.md). No search can show that nobody did this before; if you know of earlier work, please [open an issue](../../README.md#corrections).

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`result.json`](result.json): the data behind this result's row on the front page
