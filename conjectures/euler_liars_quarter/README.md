# Euler liars: the half and quarter cases

**Proved here, but someone else had it first.** This is a known result, not a new one.

| | |
|---|---|
| Kind | Known result |
| Outcome | Proved |
| Source | [A. Alcantarilla Sánchez, J. Cottaar, T. Lange, B. de Weger, "Ours go to 211: Euler pseudoprimes to 47 prime bases (from Carmichael numbers)", arXiv:2602.21840v1 (25 February 2026), the conjecture closing the appendix on "Sophie Germinus pseudoprimes"](https://arxiv.org/abs/2602.21840) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | No. See [who had it first](#who-had-it-first). |

## In plain words

For an odd squarefree composite number n: if exactly half of the numbers coprime to n are "Euler liars", then n is a Carmichael number; if exactly a quarter are, then n is a Carmichael number or of the form p(2p − 1). Proved.

## The statement as printed

A. Alcantarilla Sánchez, J. Cottaar, T. Lange, B. de Weger, "Ours go to 211: Euler pseudoprimes to 47 prime bases (from Carmichael numbers)", arXiv:2602.21840v1 (25 February 2026), the conjecture closing the appendix on "Sophie Germinus pseudoprimes".

> **Conjecture.** If an odd squarefree composite integer $n$ has $\varphi(n)/2$ Euler
> liars in $\mathbb{Z}_n^*$ then it is a Carmichael number, and if it has $\varphi(n)/4$
> Euler liars in $\mathbb{Z}_n^*$ then it is either a Carmichael number or a Sophie
> Germinus pseudoprime.

## What is proved here

`Claim`: for every odd squarefree composite n, if 2·(number of Euler liars) = φ(n) then n is a Carmichael number, and if 4·(number of Euler liars) = φ(n) then n is a Carmichael number or a product p(2p − 1) of two primes.

**How the Lean statement reads the source.**

- `IsEulerLiar n a` is the paper's congruence, read in `ZMod n`:
  `(jacobiSym a n : ZMod n) = (a : ZMod n) ^ ((n - 1) / 2)`.
- `numEulerLiars n` counts the residues `0 ≤ a < n` that are coprime to `n` and are
  Euler liars. This is "Euler liars in $\mathbb{Z}_n^*$": one count per residue class.
- "has $\varphi(n)/2$ Euler liars" is written `2 * numEulerLiars n = φ(n)`, and
  "$\varphi(n)/4$" is `4 * numEulerLiars n = φ(n)`. No rounding question arises: for an
  odd squarefree composite `n` there are at least two odd prime factors, so `4 ∣ φ(n)`.
- `Claim` quantifies over `n` with `Odd n`, `Squarefree n`, `1 < n`, `¬ n.Prime`
  ("odd squarefree composite integer").
- `IsCarmichael n` is `1 < n ∧ ¬ n.Prime ∧ ∀ a, a.Coprime n → a^(n-1) ≡ 1 [MOD n]`.
- `IsSophieGerminusPsp n` is `∃ p₁ p₂, p₁.Prime ∧ p₂.Prime ∧ p₂ = 2 p₁ - 1 ∧ n = p₁ p₂`
  (natural-number subtraction is harmless: `p₁ ≥ 2`).
- The paper's Lemma on Sophie Germinus pseudoprimes (they have $\varphi(n)/4$ Euler liars
  when $p_1 > 3$) is the converse direction. It is not part of the conjecture and is not
  formalized here.
- Sanity check by computer (Python, not part of the proof): for every odd composite
  `n < 6000` the Euler liars were counted directly. Exactly half: 2 numbers, both
  Carmichael. Exactly a quarter: 8 numbers, each Carmichael or of the form `p(2p-1)`.
  All five numbers `p(2p-1)` below 6000 (15, 91, 703, 1891, 2701) have exactly a
  quarter. No counterexample, also none among non-squarefree `n`.

## Idea of the proof

Work in the group `G` of units modulo `n`. The Euler liars form a subgroup `E`, so
"$\varphi(n)/2$ liars" means index 2 and "$\varphi(n)/4$" means index 4. Every Euler liar
`u` satisfies `u^(n-1) = 1`, and if `u²` is an Euler liar then `u^(n-1) = 1` too.

- Index 2: every square lies in `E`, so `u^(n-1) = 1` for every unit. That is Carmichael.
- Index 4 and not Carmichael: some prime `q ∣ n` has `(q-1) ∤ (n-1)`. Take `g` that is a
  generator modulo `q` and `1` modulo the other primes. Then `g^(n-1) ≠ 1`, and `g²` is
  not a liar, which pins down the chain `E < K < G` (`K` = units with `u^(n-1) = 1`) with
  both steps of index 2. For any other prime `p ∣ n`, take `h` a generator modulo `p` and
  `1` elsewhere. Index 2 forces `h ∈ K`, so `(p-1) ∣ (n-1)`. The Jacobi symbol of `h` is
  `-1`, so `h` is not a liar, and then `h·g²` must be a liar. Looking at that modulo a
  third prime would give `1 = -1`. So `n = p·q`, and the two divisibility facts
  `(p-1) ∣ (pq-1)`, `(q-1) ∣ 2(pq-1)`, `(q-1) ∤ (pq-1)` force `q = 2p - 1`.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=euler_liars_quarter  result : Claim  (Claim as defined in conjectures/euler_liars_quarter/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: b59f6b69974fc265   proof sha256: 41f275163c96818a   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Who had it first

The half case is in a 2011 paper (Di Biagio, arXiv:1109.3596). The quarter case is reported to be stated as a theorem on the web page of the paper's own authors, which says a proof exists and a write-up is in preparation; that page could not be opened from here and its content is as reported by a public record. No earlier machine-checked proof was found.

This result is kept here because the proof was found and checked independently, before the earlier work was known to this repository. It is not claimed as new.

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`result.json`](result.json): the data behind this result's row on the front page
