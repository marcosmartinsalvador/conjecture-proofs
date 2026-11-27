# Δ-primitive numbers with two prime factors: the proof on paper

This is the argument on paper, in seven steps. `Proof.lean` in this folder follows the same steps and is the version that was machine-checked; `check.py` tests every step that can be tested by computer. Where this note and `Proof.lean` differ, `Proof.lean` is the one that counts.

## Statement

n = p^x q^y with p != q primes and x, y >= 1. If n is Delta-primitive then n is 24 or
40. (`Statement.lean` states this in Lean; the definitions are the paper's.)

Result of the analysis, slightly stronger: the numbers p^x q^y that have a Delta
triple "not divisible by p and not divisible by q" (see Step 1) are exactly 24, 40
and 216. Since 216 = 3^2 * 24 is not primitive, the conjecture follows.

## Notation

A *pair* is (d, D) with d * D = n and d < D; its *difference* is D - d > 0.
n has the Delta property iff there are pairs (a,A), (b,B), (c,C) with

    A - a = (B - b) + (C - c),      i.e.   A + b + c = a + B + C.      (E)

(Direct from the definition: an element of D*_n that is a sum of two nonzero elements
of D*_n.) P = p^x, Q = q^y.

## Step 1. Primitive => not all six numbers are divisible by p (same for q)

If p divides a, A, b, B, c, C, divide all six by p: they are pairs of n/p^2 and (E)
still holds, so n/p^2 has the Delta property, and n = p^2 * (n/p^2) with
n/p^2 >= 2. This contradicts primitivity.

## Step 2. At most one pair has both members divisible by p (same for q)

Call a pair *p-nonsplit* if p divides both members, *p-split* otherwise. (For a
p-split pair one member is prime to p and the other is divisible by p^x.)
If two pairs are p-nonsplit, p divides two of the three differences, so by (E) it
divides the third, D - d. As p | d*D, p divides d or D, hence both. Then all six
are divisible by p, against Step 1.

## Step 3. The pair (1, n) does not occur

- a = 1: then b, c >= 2 (b = 1 would force C = c), so B, C <= n/2 and
  n + b + c = 1 + B + C <= 1 + n, impossible.
- b = 1 (or c = 1): A + 1 + c = a + n + C with A <= n gives a + C <= c + 1 <= C,
  so a = 0, impossible.

## Step 4. Shapes of the pairs

For a pair (d, D) other than (1, n):

- p-split and q-split: {d, D} = {P, Q}. Difference |P - Q|. ("FS")
- p-nonsplit, q-split: {d, D} = {p^i, p^i' * Q} with i, i' >= 1, i + i' = x.
  Difference |p^i' Q - p^i|. ("Np")
- p-split, q-nonsplit: {d, D} = {q^j, q^j' * P} with j, j' >= 1, j + j' = y.
  Difference |q^j' P - q^j|. ("Nq")
- both nonsplit: p and q divide the difference. ("Npq")

By Step 2 the three pairs are, in some order, one of:
(FS,FS,FS), (FS,FS,Np), (FS,FS,Nq), (FS,FS,Npq), (FS,Np,Nq).
(E) says one of the three differences is the sum of the other two.

## Step 5. The easy cases

- (FS,FS,FS): h = h + h with h = |P - Q| > 0. Impossible.
- (FS,FS,X): the two FS differences are equal (h0 = |P - Q|), so the third is
  h' = 2 h0 (the other option h0 = h0 + h' is impossible).
  - X = Npq: p | h' = 2 h0 = +-2(P - Q), so p | 2Q, so p = 2. The same way q = 2.
    Contradiction.
  - X = Np: h' = +-(p^i' Q - p^i) is divisible by p, so p | 2(P - Q), so p = 2.
    With signs: 2^i' Q - 2^i = +-2(2^(i+i') - Q).
    - Minus sign: Q(2^i' - 2) = 2^i - 2^(i+i'+1) < 0, impossible.
    - Plus sign: Q(2^i' + 2) = 2^i (2^(i'+1) + 1). Put M = 2^(i'-1), K = 2^(i-1):
      Q (M + 1) = K (4M + 1), Q odd.
      - i' = 1 (M = 1): 2Q = 5K, so K = 2, Q = 5: i = 2, x = 3, **n = 40**.
      - i' >= 2 (M even): left side odd, so K = 1 (i = 1) and
        Q(M+1) = 4(M+1) - 3, so M + 1 divides 3: M = 2, Q = 3, x = 3, **n = 24**.
  - X = Nq: the same with p and q exchanged: n is 24 or 40.

This part is the same method as the paper's own lemma for p^k q.

## Step 6. The case (FS, Np, Nq)

Write R = p^i, R' = p^i', S = q^j, S' = q^j' (all >= 2), so P = R R', Q = S S'.
The three differences are, up to sign,

    X1 = R R' - S S',   X2 = R' S S' - R,   X3 = S' R R' - S,

and e1 X1 + e2 X2 + e3 X3 = 0 for some signs e1, e2, e3. Collecting R and S:

    R (e1 R' - e2 + e3 R' S') = S (e1 S' - e2 R' S' + e3).

Both brackets are nonzero with the sign of e3 and of -e2 (because R', S' >= 2), so
e3 = -e2. With eps = e1 e3 = +-1 this becomes

    R (R' S' + eps R' + 1) = S (R' S' + eps S' + 1).            (*)

(In terms of the four sign patterns up to a global sign: (+,+,+) and (+,-,-) are
impossible, (+,-,+) gives eps = +1, (+,+,-) gives eps = -1.)

Put X = R'S' + eps R' + 1 and Y = R'S' + eps S' + 1 (both positive). R and S are
coprime, so X = S t and Y = R t for an integer t >= 1. Subtracting:

    (R - S) t = eps (S' - R').                                   (**)

R != S, so t <= |S' - R'|, and in particular S' != R'.
Also p^min(i,i') divides Y and R'S', hence divides eps S' + 1; and q^min(j,j')
divides eps R' + 1.

Four subcases.

**(d) i < i' and j < j'** (so R' >= 2R and S' >= 2S). No solution:
- if S' > R': Y = R t <= R (S' - R'), but Y >= R'S' - S' + 1 >= 2RS' - S' + 1 > RS'.
- if S' < R': X = S t <= S (R' - S'), but X >= R'S' - R' + 1 >= 2SR' - R' + 1 > SR'.

**(a) i' <= i and j' <= j** (so R' | eps S' + 1 and S' | eps R' + 1). No solution:
- eps = -1: R' <= S' - 1 and S' <= R' - 1, impossible.
- eps = +1: R' <= S' + 1, S' <= R' + 1, R' != S', so they differ by 1.
  If S' = R' + 1 then R' | R' + 2, so R' = 2, S' = 3 (p = 2, q = 3) and (*) reads
  9 R = 10 S, impossible for R a power of 2 and S a power of 3 (5 divides the right
  side). If R' = S' + 1, the same with the roles exchanged (10 R = 9 S).

**(b) i' <= i and j < j'** (so R' | R, R' | eps S' + 1, S | eps R' + 1, S | S',
S' >= 2S). Exactly one solution:
- eps = -1: R' <= S' - 1 and S <= R' - 1. Then t <= S' - R' and
  X = S t <= S(S' - R'), i.e. R'S' - R' + 1 <= SS' - SR' <= (R'-1)S' - SR',
  impossible.
- eps = +1: R' <= S' + 1 and S <= R' + 1.
  - If S' < R': R' = S' + 1 and by (**) t = 1, so X = S <= R' + 1, but
    X = R'S' + R' + 1. Impossible.
  - If S' > R': X = S t <= S (S' - R') gives S'(S - R') >= R' + 1 + S R' > 0, so
    S > R', so S = R' + 1. Write S' = S k with k >= 2. From X = S t:
    t = R' k + 1. From Y = R t:

        R (R' k + 1) = (R' + 1)^2 k + 1 = (R' + 2)(R' k + 1) + (k - R' - 1).

    Since |k - R' - 1| < R' k + 1, this forces R = R' + 2 and k = R' + 1.
    R' | R gives R' | 2, so R' = 2, R = 4, S = 3, S' = 9.
    That is p = 2, x = 3, q = 3, y = 3: **n = 216**.

**(c) i < i' and j' <= j**: subcase (b) with (p, R, R') and (q, S, S') exchanged
((*) is symmetric under this exchange). Solution S' = 2, S = 4, R = 3, R' = 9,
again n = 216.

## Step 7. Conclusion

A Delta-primitive n = p^x q^y is 24, 40 or 216. But 216 = 3^2 * 24 and 24 has the
Delta property (12 - 2 = (8 - 3) + (8 - 3)), so 216 is not primitive.
(216 does have a triple not coming from 24: 72 - 3 = (54 - 4) + (27 - 8).)

## Computer checks (check.py)

- Every n <= 60000 with exactly two prime factors: Delta property iff n is 24 or
  40 times a square. No mismatch.
- Primes p < q < 300, n <= 10^40 (425892 cases): the only n with the property are
  2^a 3^b and 2^a 5^b with a >= 3 odd and b odd; the only primitive ones are 24 and
  40. This was run on 2026-11-26 with an earlier scratch script of the same logic;
  `python3 check.py wide` is meant to repeat it (several minutes) and its result
  was not waited for before this note was committed.
- Equation (*) in prime powers, primes < 120, R'S' <= 10^30: the only solution is
  (R, R', S, S') = (4, 2, 3, 9) and its mirror.

## How the Lean proof is laid out (`Proof.lean`)

1. `exists_triple`, `hasDelta_of_triple`: the Delta property in the form (E), with the
   differences as signed integers; `SumRel` is "one difference is, up to signs, the sum
   of the other two", which is symmetric in the three pairs.
2. `descent` (Step 1), `not_two_both` (Step 2), `no_one` (Step 3).
3. `pair_shape`, `classify` (Step 4): a 4-way disjunction with the shape of the
   difference (`FS`, `NS`) and the flags `p | d /\ p | D`, `q | d /\ q | D`.
4. `case_fff`, `case_ffn`, `case_ffm`, `case_ffb` (Step 5); `two_fs_arith` is the
   arithmetic that produces 24 and 40.
5. `star_sign`, `star_t`, `star_a`, `star_b`, `star_d`, `star`, `case_fnm` (Step 6),
   over the integers; subcase (c) is `star_b` with the arguments exchanged. The fact
   "9R = 10S is impossible" uses only `5 | R -> 5 | R'`.
6. `main` (Step 7): the 64 combinations of shapes, 48 killed by Step 2 and 16 by the
   case lemmas.
