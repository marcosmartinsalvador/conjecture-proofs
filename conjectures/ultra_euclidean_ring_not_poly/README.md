# Ultra-Euclidean functions: such rings need not be fields or polynomial rings

**Disproved.** A full resolution of the conjecture as stated in the source.

| | |
|---|---|
| Kind | Full resolution |
| Outcome | Disproved |
| Source | [S. Sekhon, "A Necessary and Sufficient Condition for Uniqueness of Euclidean Division", arXiv:2604.24399v2 (April 2026), section "Further investigation"](https://arxiv.org/abs/2604.24399) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | Fairly sure, with one gap. See [is it new?](#is-it-new) |

## In plain words

The paper hoped that a ring with an ultra-Euclidean function must be a field or a polynomial ring K[x] over a field, and prints this as a corollary that would follow from its conjecture. The same example that disproves the conjecture disproves this too: the Laurent polynomial ring ℚ[T, T⁻¹] has such a function and is neither a field nor a polynomial ring.

This is a companion of the refinement result, not a separate conjecture.

## The statement as printed

S. Sekhon, "A Necessary and Sufficient Condition for Uniqueness of Euclidean Division", arXiv:2604.24399v2 (April 2026), section "Further investigation".

> **Corollary.** If $R$ has an ultra-Euclidean function, then either $R$ is a field or
> $R\cong\mathbb K[x]$ for some field $\mathbb K$.

The paper prints this as a corollary that would follow from its conjecture (see [the companion result](../ultra_euclidean_refinement_false/)), so it was open as well. It is not a separately named conjecture.

## What is proved here

**Both statements are false.** `Statement.lean` here states the negation of the "Corollary", and
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
- "`R` is a field" is `IsField R`. "`R ≅ K[x]` for some field `K`" is a ring isomorphism
  `R ≃+* Polynomial K` with `K : Type` a field. Taking `K : Type` loses nothing: if
  `R : Type` were isomorphic to `K[x]` for a field `K` in a larger universe, then `K` is
  isomorphic to the subring of constants inside `R`, which lives in `Type`.
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
ACCEPTED  slug=ultra_euclidean_ring_not_poly  result : Claim  (Claim as defined in conjectures/ultra_euclidean_ring_not_poly/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: bbe34e2d9be72f68   proof sha256: c8be5e485874bd5d   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Is it new?

**Fairly sure, with one gap.** Nothing was found anywhere. The gap is the same as for the companion result: the older papers on unique Euclidean division (from the 1960s on) could not be searched.

What was searched, and what could not be, is in [the prior-art note](../../docs/prior-art.md). No search can show that nobody did this before; if you know of earlier work, please [open an issue](../../README.md#corrections).

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`result.json`](result.json): the data behind this result's row on the front page
