# Kourovka problem 20.52: the odd half

**Partial result. The problem is still open.**

| | |
|---|---|
| Kind | Partial result |
| Outcome | Odd half proved; the problem is still open |
| Source | [*Unsolved Problems in Group Theory. The Kourovka Notebook*, No. 21, edited by E. I. Khukhro and V. D. Mazurov, arXiv:1401.0300v50 (November 2026), problem 20.52, posed by D. MacHale](https://arxiv.org/abs/1401.0300) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-27 |
| New? | Fairly sure; the proof is short. See [is it new?](#is-it-new) |

## In plain words

For a group G of odd order, the number of elements minus the number of conjugacy classes is always a multiple of 16 (Burnside). The problem asks whether every multiple 16m is reached by some non-abelian group of odd order.

**What is proved.** Yes for every odd m, and for every m in which 2 occurs to an odd power (m = 2, 6, 8, 10, 14, 18, 22, 24, …). That is five sixths of all m. One family of groups does it.

**What is not proved.** Anything for m = 4, 12, 16, 20, 28, … (2 to an even power, at least 2), beyond what was already known. **The problem is not solved.** Computer searches found no group for the first open case, m = 2¹⁴ = 16384, so this half is not a formality and could even be false.

## The statement as printed

*Unsolved Problems in Group Theory. The Kourovka Notebook*, No. 21, edited by E. I. Khukhro and V. D. Mazurov, arXiv:1401.0300v50 (November 2026), problem 20.52, posed by D. MacHale.

> **20.52.** A famous result of Burnside states that if $k(G)$ is the number of
> conjugacy classes of a finite group $G$ of odd order, then $|G|- k(G)$ is
> divisible by 16. Is it true that for every integer $m > 0$ there exists a
> finite non-abelian group $G(m)$ of odd order such that
> $|G(m)| - k(G(m)) = 16m$? *D. MacHale*

## What is proved here

`Statement.lean` defines `Attained m`: there is a type `G` with a group
structure, finite, with `Nat.card G` odd, with two elements that do not
commute, and with `Nat.card G = Nat.card (ConjClasses G) + 16 * m`. `Claim`
says: every `m > 0` that is odd, or with `padicValNat 2 m` odd, is attained.

How the definitions compare with the Notebook:

- `Claim` is **not** the problem. The problem asks for every `m > 0`; `Claim`
  covers odd `m` and `m` in which 2 occurs to an odd power. Nothing is said
  about `m = 4, 12, 16, 20, ...`.
- "Non-abelian" is `∃ x y, x * y ≠ y * x`. "Odd order" is `Odd (Nat.card G)`
  together with `Finite G`. `k(G)` is `Nat.card (ConjClasses G)`, Mathlib's
  type of conjugacy classes. The equation is written with `+` because natural
  subtraction would hide nothing here (k(G) <= |G|) but is easier to misread.
- `G : Type` (the lowest universe) is no loss: every finite group has a copy
  there, and the claim is an existence statement.
- `padicValNat 2 m` is the exponent of 2 in `m` (Mathlib's definition; in this
  Mathlib it equals `multiplicity 2 m` by `Nat.padicValNat_def`).

`Proof.lean` (about 290 lines): Part 1 builds the group on triples
`(x, y, s)` in `Z/n x Z/a x Z/3` with `(x,y,s)(x',y',t) = (x + u^s x', y + y',
s + t)`. Part 2 counts commuting pairs, `a^2 (n^2 + 8n)` (`card_comm`), by
splitting on `(s, t)`: `n^2` pairs `(x, x')` for `s = t = 0` and `n` otherwise,
because `1 - u` and `1 - u^2` are units (their product is 3). Mathlib's
`card_comm_eq_card_conjClasses_mul_card` turns that into `3 k(G) = a (n + 8)`.
Part 3 (`attained_of`, `result`) plugs in `n = 7, u = 2` for odd `m` and
`n = 12y^2 + 1, u = 6y^2 + 3y, y = 2^i` for `m = 2^(2i+1) b`.

A guard the checker does not give: `check.g` builds the same groups in GAP for
j = 1, 3, ..., 11 and gets the same class numbers.

## Idea of the proof

Write m = 2ʲa with a odd. If a group G works for m, then G × ℤ/a′ works for ma′ (a′ odd), so the question is exactly whether 2ʲ⁺⁴ has the form |G| − k(G) for every j ≥ 0.

Take an odd n and a residue u of multiplicative order 3 modulo n for which 1 − u and 1 − u² are units (their product is 3). Let ℤ/3 act on ℤ/n by multiplication by u and form G = (ℤ/n ⋊ ℤ/3) × ℤ/a with a odd. Counting commuting pairs gives a²(n² + 8n), so 3·k(G) = a(n + 8), and therefore

$$|G| - k(G) = 3an - \frac{a(n+8)}{3} = \frac{8a(n-1)}{3}.$$

- n = 7, u = 2 gives 16a: every odd m.
- n = 12y² + 1, u = 6y² + 3y with y = 2ⁱ gives 32ay² = 16 · 2²ⁱ⁺¹ · a: every m in which 2 occurs to the odd power 2i + 1.

`check.g` builds the same groups in GAP for j = 1, 3, …, 11 and gets the same class numbers; its output is in `check_output.txt`.

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=kourovka_20_52_class_deficiency  result : Claim  (Claim as defined in conjectures/kourovka_20_52_class_deficiency/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: fd8e24fd1fb928ba   proof sha256: 52426f813183083e   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Is it new?

**Fairly sure; the proof is short.** The question comes from a 2013 paper: S. M. Buckley and D. MacHale, "Conjugate deficiency in finite groups", Irish Math. Soc. Bulletin 71 (2013), 13 to 19, Problem 5. That paper was read in full. It already gives a group for every m below 512, by nine single examples, so below 512 nothing here is new. Four of those examples are the first groups of the family used here, but the paper says it sees no clear enough pattern, and does not have the family. What is added here is that pattern: one proof for all odd powers of two, with first new value m = 512.

Another public project, `JUrban/kour1`, read the 2013 paper, checked every group of odd order up to 1727 and found every m ≤ 64. Its notes describe the same kind of group for m = 1, 2, 4, 8, 16, 32 and say that the general question remains unresolved there. Those notes are how the 2013 paper was found for this result. No other public project was found with an answer.

Not searched: papers that cite the 2013 paper, MathSciNet and zbMATH. The step is short, which is the usual reason for doubt.

What was searched, and what could not be, is in [the prior-art note](../../docs/prior-art.md). No search can show that nobody did this before; if you know of earlier work, please [open an issue](../../README.md#corrections).

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`check.g`](check.g): a GAP script that rebuilds the groups and counts their classes (not part of the Lean proof)
- [`check_output.txt`](check_output.txt): the output of `check.g`
- [`result.json`](result.json): the data behind this result's row on the front page
