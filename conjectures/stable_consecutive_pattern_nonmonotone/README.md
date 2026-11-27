# Stable consecutive patterns need not be monotone

**Disproved.** A full resolution of the conjecture as stated in the source.

| | |
|---|---|
| Kind | Full resolution |
| Outcome | Disproved |
| Source | [S. Chen, H. Fang, S. Kitaev, "Stable patterns on permutations of multisets", arXiv:2602.13566v2 (v1 February 2026, v2 1 September 2026), Conjecture 6.1](https://arxiv.org/abs/2602.13566) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | Less sure. See [is it new?](#is-it-new) |

## In plain words

Take all words with a given number of 1s, 2s, 3s and so on, and count how often a short pattern of ups and downs appears in consecutive letters. The pattern is "stable" if these counts do not change when the numbers of copies are handed to the letters in another order. The paper conjectures that only the steadily rising and steadily falling patterns are stable. That is false: the pattern 12435 is stable too, on every multiset.

This does not say which patterns are stable; it only shows that the monotone ones are not the only ones.

## The statement as printed

S. Chen, H. Fang, S. Kitaev, "Stable patterns on permutations of multisets", arXiv:2602.13566v2 (v1 February 2026, v2 1 September 2026), Conjecture 6.1.

> **Conjecture.** A consecutive pattern is stable if and only if it is monotone.

## What is proved here

`Statement.lean` states the counterexample itself: `Claim` says that the
pattern 12435 (`p12435`, the permutation of `Fin 5` that exchanges 2 and 3,
letters counted from zero) is `PatternStable` and is neither strictly
increasing nor strictly decreasing.

How the definitions compare with the paper:

- A word is a map `w : Fin m → Fin n`; the permutations of `M(k_1, ..., k_n)`
  are the words with `mult w a = k a` for all `a`. The length `m` is a free
  variable: when `m` is not `k_1 + ... + k_n` both sets are empty.
- `OccAt p w i`: the `ℓ` adjacent letters from position `i` are in the same
  relative order as `p` (for all `a`, `b`: `p a < p b` iff the letters at
  `i + a`, `i + b` are in that order). For a pattern with distinct letters this
  is "the reduction of the factor is `p`". `occ p w` counts such positions.
- `PatternStable p` quantifies over every `m`, `n`, every `k : Fin n → ℕ`
  (zeros allowed), every permutation `σ` of the letters and every `s`, and
  compares `M(k)` with `M(k ∘ σ)`. The paper acts by `σ⁻¹`; over all `σ` that
  is the same. Allowing zero multiplicities makes the Lean notion at least as
  strong as the paper's under either reading of its `N`, and the claim is a
  positive stability statement, so the stronger notion is the safe side.
- "Monotone" for a pattern with distinct letters is `StrictMono p ∨
  StrictAnti p`.
- The name `PatternStable` was forced: Mathlib already has an `IsStable`.

A guard the checker does not give: the definitions are not degenerate. The
brute-force program uses the same definitions and separates patterns (132,
1324, 1243, 21435 unstable; 12435 stable). A Lean proof that some pattern is
*not* `PatternStable` would be an extra guard; it was not done.

`Proof.lean` (655 lines) follows the steps above: Part 1 the core fact on value
sequences (`distinct`), Part 2 the exchange map `flp` (`flp_flp`, `marked_flp`,
`mult_flp`), Part 3 the counting (`moebius`, `count_by_card`, `adj`,
`all_perm`, `stable`).

## Idea of the proof

Counterexample: the consecutive pattern **12435** (and its mirror images 13245,
53421, 54231). An occurrence at position i means
`w_i < w_{i+1} < w_{i+3} < w_{i+2} < w_{i+4}`.

1. Two occurrences can only overlap in one letter (starts 4 apart) or two
   letters (starts 3 apart). Starts 1 or 2 apart contradict each other.
2. In both cases every letter of the later occurrence that is new is larger
   than every earlier letter. So in a run of overlapping marked occurrences all
   letters are different and their order is forced: it is the order of the
   positions, with the two middle positions of each occurrence swapped.
3. So the number of words with given letter counts in which a given set S of
   positions are occurrences depends on the letter counts only through
   symmetric data. Concretely, for two neighbouring letters a and a+1 there is
   an involution on words that keeps "S are occurrences" and swaps the counts
   of a and a+1: in every run that contains exactly one of the two letters,
   replace it by the other.
4. Inclusion-exclusion over S turns "S are occurrences" into "exactly s
   occurrences". Neighbouring swaps generate all rearrangements.

This is the Goulden-Jackson cluster method with the observation that every
cluster weight of 12435 is an elementary symmetric function.

The Lean proof carries out steps 1 to 4 as written.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=stable_consecutive_pattern_nonmonotone  result : Claim  (Claim as defined in conjectures/stable_consecutive_pattern_nonmonotone/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: 2285eca669eab78c   proof sha256: f55e065184ba6c54   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Is it new?

**Less sure.** Nothing public was found saying the conjecture is false. Two reasons for doubt remain. First, the search log of another public project, dated 26 November 2026 at 20:20 UTC (about forty minutes after this proof was accepted), looks for this paper together with "12435", so that project may hold the same counterexample independently. Second, the property of 12435 that the proof rests on is in a 2012 paper (Elizalde and Noy, on "chain patterns"), so a specialist could call this a short step.

What was searched, and what could not be, is in [the prior-art note](../../docs/prior-art.md). No search can show that nobody did this before; if you know of earlier work, please [open an issue](../../README.md#corrections).

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`check.py`](check.py): an independent numerical check in plain Python (not part of the Lean proof)
- [`check_bf.cpp`](check_bf.cpp): a brute-force program used to test the definitions (not part of the Lean proof)
- [`result.json`](result.json): the data behind this result's row on the front page
