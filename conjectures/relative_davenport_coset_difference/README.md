# A conjecture on Davenport constants of cosets is false as stated

**Disproved as stated here, but someone else published it first.** This is a known result, not a new one.

| | |
|---|---|
| Kind | Known result |
| Outcome | Disproved as stated |
| Source | [J. Kettinger, G. Moles, "Elasticity of Orders from the S-relative Davenport Constant: an Arithmetic Application of a Number-Theoretic Investigation", arXiv:2605.17595v2 (v1 17 May 2026, v2 14 July 2026), Conjecture 2.17](https://arxiv.org/abs/2605.17595) |
| Machine check | Lean 4.36.0 with Mathlib v4.36.0; accepted on 2026-11-26 |
| New? | No. See [who had it first](#who-had-it-first). |

## In plain words

A conjecture on Davenport constants of cosets. It is disproved as stated, reading the paper's "for some g" as "for every g". The case the paper uses later (g inside the subgroup) is not refuted.

## The statement as printed

J. Kettinger, G. Moles, "Elasticity of Orders from the S-relative Davenport Constant: an Arithmetic Application of a Number-Theoretic Investigation", arXiv:2605.17595v2 (v1 17 May 2026, v2 14 July 2026), Conjecture 2.17.

> Let $G$ be a finite abelian group and $H_1<H_2\leq G$. For some $g\in G$, we denote
> $\alpha=g+H_1$ and $\beta=g+H_2$; in particular, note that $\alpha\subsetneq \beta$.
> Then $d_\beta(G)=d_{\beta\backslash\alpha}(G)$.

## What is proved here

**How the Lean statement reads the source.**

- A sequence is taken up to order, as a `Multiset`; a subsequence is a sub-multiset;
  "no zero-sum subsequence" means no nonempty sub-multiset with sum 0. `smallDav S`
  is the supremum of the lengths, which is 0 when no such sequence exists.
- **Reading choice: "For some $g\in G$, we denote ..." is read as "for every $g$".**
  Reasons: the proof of Corollary 2.15 treats an arbitrary coset $\beta$ ("we let
  $1\leq g\leq m_2$ be an element of $\beta$"); and under the reading "there is a
  $g$" the cyclic case would be immediate with $g=0$ (a generator of $H_2$ is not in
  $H_1$), which does not fit a page-long proof.
- **Not refuted: the subgroup case $\alpha=H_1$** (that is $g\in H_1$,
  $d_{H_2}(G)=d_{H_2\setminus H_1}(G)$). This is the only case the paper uses later
  (the definition of the constants $d_j$, TeX label `dj`, where $H_2\setminus H_1$ is a
  difference of two kernels), so the paper's applications are not affected by this counterexample.
  This case is still open as far as is known here.
- Evidence from `check.py` (19 small groups, the largest being $\mathbb{Z}_5^2$): the
  statement fails **only** when the index $[H_2:H_1]$ is 2 and $\alpha\neq H_1$. It
  never fails for $\alpha=H_1$, and never for index 3 or more. Reason for index 2:
  $\beta$ is then the union of two cosets of $H_1$, and the statement applied to
  each of them would force both to have the same constant.
- So a corrected conjecture would add "$g\in H_1$, or $[H_2:H_1]\geq 3$". That
  corrected statement is not proved here.
- The paper's other conjecture (2.16: $d_\alpha(G)\ge d_\beta(G)$ when
  $\beta\in\langle\alpha\rangle$) holds on the same groups; no proof found, not
  claimed.

## Idea of the proof

**The conjecture is false as stated.** Take $G=\mathbb{Z}/4$, $H_1=\{0,2\}$, $H_2=G$,
$g=1$. Then $\beta=G$, $\alpha=\{1,3\}$ and $\beta\setminus\alpha=\{0,2\}$.

- $d_\beta(G)=d(\mathbb{Z}/4)=3$: the sequence $1,1,1$ has no zero-sum subsequence, and
  four elements of $\mathbb{Z}/4$ always have one.
- $d_{\beta\setminus\alpha}(G)=2$: the only zero-sum free sequences of length 3 are
  $1,1,1$ and $3,3,3$, with sums 3 and 1; $1,1$ has sum 2.

So $3\neq 2$. In the "equivalently" form: the only zero-sum free sequences of length
$d_\beta(G)=3$ have their sum in $\alpha$.

`Claim` in `Statement.lean` states: $\{0,2\}$ is a proper subgroup of $\mathbb{Z}/4$,
the two values are 3 and 2, and therefore the conjecture (`PaperConjecture`) fails.

Under the reading above, the same example also contradicts the paper's **Corollary 2.15**, the same statement for cyclic $G$, which the paper presents as proved. This remark is not machine-checked and rests on that reading. The paper's own Theorem 2.13
($d_\alpha(G)=n-\gcd(g,m)$ for a coset of $\langle m\rangle$ in $\mathbb{Z}/n$) gives
$d_\beta=4-1=3$ and $d_{\{0,2\}}=4-2=2$. The suspected gap in the proof of Corollary 2.15: it
replaces $g_1$ by $g_1'=g_1+p_1^{b_1}$ and uses
$\gcd(g_1',p_1^{b_1})=\gcd(g_1',p_1^{a_1})$; this fails when $p_1=2$ and
$g_1=2^{b_1}$ (here $2^{b_1}+2^{b_1}=2^{b_1+1}$).

## Machine check

The checker in [`tools/check_lean.sh`](../../tools/check_lean.sh) printed:

```
ACCEPTED  slug=relative_davenport_coset_difference  result : Claim  (Claim as defined in conjectures/relative_davenport_coset_difference/Statement.lean)
          axioms: Classical.choice Quot.sound propext   kernel replay: slug files   sandbox: on
          statement sha256: 06caa5645ec3b9cd   proof sha256: 36465c081cb40664   files:Statement Proof
          lean: v4.36.0 (611c117bfaf7)   mathlib: fc4f59e577fe   checker: b28f6f42387a1525 (same as main)
          not checked here: that Claim says what the paper says. That is REVIEW.md.
```

This says that Lean's kernel accepts `result : Claim`, that the proof rests on no axioms beyond the three standard ones, and which versions were used. It does not say that `Claim` is a faithful reading of the source; that was compared by hand in a separate review, and the reading choices are listed above. See [how results are checked](../../docs/verification.md).

## Who had it first

The same counterexample in words in `the-omega-institute/trureturing`, 5 November 2026. The version here is the first machine-checked one known to this repository.

This result is kept here because the proof was found and checked independently, before the earlier work was known to this repository. It is not claimed as new.

## Files

- [`Proof.lean`](Proof.lean): the proof, `theorem result : Claim`
- [`Statement.lean`](Statement.lean): the statement, as a Lean definition `Claim : Prop`
- [`check.py`](check.py): an independent numerical check in plain Python (not part of the Lean proof)
- [`result.json`](result.json): the data behind this result's row on the front page
