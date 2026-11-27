# A divisor sum over shifted squares is always a multiple of 4

**Proved here, but someone else published it first.** This is a known result, not a new one.

| | |
|---|---|
| Kind | Known result |
| Outcome | Proved |
| Source | [S. Jirattikansakul, T. Kittipassorn, K. Kongsiri, N. Moonwichit, K. Sriamorn, "Congruences via Partitions with Exactly Two Part Sizes", arXiv:2604.25394v1 (28 April 2026), first conjecture of the concluding remarks](https://arxiv.org/abs/2604.25394) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | No. See [who had it first](#who-had-it-first). |

## In plain words

For N = 16n + 6, add up the number of divisors of N − k² over all k with 1 ≤ k < √N. The conjecture says the total is always divisible by 4. It is proved here, as a special case of a more general statement.

## The statement as printed

S. Jirattikansakul, T. Kittipassorn, K. Kongsiri, N. Moonwichit, K. Sriamorn, "Congruences via Partitions with Exactly Two Part Sizes", arXiv:2604.25394v1 (28 April 2026), first conjecture of the concluding remarks.

> **Conjecture.** Let $N = 16n+6$ for some nonnegative integer $n$. Then
> $$\sum_{1 \leq k < \sqrt{N}} \sigma_0(N - k^2) \equiv 0 \pmod 4.$$

Here $\sigma_0(m)$ is the number of positive divisors of $m$.

## What is proved here

`Claim`: for every natural number n, with N = 16n + 6, the sum of σ₀(N − k²) over the integers k with k ≥ 1 and k² < N is congruent to 0 modulo 4.

**How the Lean statement reads the source.**

- "$1 \le k < \sqrt N$" with $k$ an integer is "$k \ge 1$ and $k^2 < N$". In
  `Statement.lean` this is `(Finset.range N).filter (fun k => 1 ≤ k ∧ k ^ 2 < N)`
  (every such `k` is below `N`, so `range N` loses nothing).
- For these `k`, `N - k^2 > 0`, so natural-number subtraction is the true difference.
- `σ₀(m)` is `(Nat.divisors m).card`. For `m > 0` this is the number of positive divisors.
- "≡ 0 (mod 4)" is `≡ 0 [MOD 4]` (`Nat.ModEq`).
- `n` ranges over all natural numbers including 0 (`N = 6`: `σ₀(5) + σ₀(2) = 4`).
- Numerical check outside Lean (Python, plain definition): the sum is divisible by 4
  for every `N = 16n + 6` up to 20,000; first values `N = 6, 22, 38`: 4, 16, 20.

## Idea of the proof

`Proof.lean` proves more than the conjecture (theorem `general`):

> If `N ≡ 2 (mod 4)` and `N` is not a sum of two squares, then
> `∑_{k ≥ 1, k² < N} σ₀(N - k²) ≡ 0 (mod 4)`.

Every `N ≡ 6 (mod 8)` qualifies, so this covers the conjecture (`16n+6`) and also the
paper's Theorem 1 (all five pairs), without partitions.

Write `N = 2m`, `m` odd. No `N - k²` is a square (else `N` is a sum of two squares),
so every `σ₀(N - k²)` is even, and the question is the parity of half of each term.

1. `k` even, `k = 2j`: `N - k² = 2(m - 2j²)` with `m - 2j²` odd, so
   `σ₀(N - k²) = 2 σ₀(m - 2j²)`, and `σ₀(u)` is odd exactly when `u` is a square.
   So half of the term is odd exactly when `m - 2j² = i²`.
2. `k` odd: `n = N - k² ≡ 1 (mod 4)`. Zagier's two involutions on
   `{(x,y,z) > 0 : x² + 4yz = n}` show that the number of divisors of `n` below `√n`
   (which is `σ₀(n)/2`) has the same parity as the number of `(x,y) > 0` with
   `x² + 4y² = n`.
3. So half of the odd-`k` part has the parity of `#{(k,x,y) > 0 : k² + x² + 4y² = N}`
   (here `k`, `x` are automatically odd). Swapping `k` and `x` is an involution; its
   fixed points are `2k² + 4y² = N`, that is `k² + 2y² = m`.
4. Half of the even-`k` part has the parity of `#{(i,j) > 0 : i² + 2j² = m}` by step 1.
   That is the same set as in step 3. The two parities cancel.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=sigma0_shifted_squares_mod4  result : Claim  (Claim as defined in conjectures/sigma0_shifted_squares_mod4/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: 69431112bebbe486   proof sha256: d4a0f5172bcca37b   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Who had it first

Qianghao Wu, `KenWuqianghao/kenwu-lab`, folder `results/square-plus-product-divisors` (Zenodo DOI 10.5281/zenodo.24580854): a public Lean proof of a stronger statement (every N that leaves remainder 6 when divided by 8), first committed on 27 November 2026 at 01:44 UTC and released that morning. The proof here was checked on 26 November, about fourteen hours earlier, and the two were found independently; but the proof here was not public then, so theirs is the first published proof.

This result is kept here because the proof was found and checked independently, before the earlier work was known to this repository. It is not claimed as new.

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`result.json`](result.json): the data behind this result's row on the front page
