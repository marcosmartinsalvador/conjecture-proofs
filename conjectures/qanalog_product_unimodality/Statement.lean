import Mathlib

/-- The `q`-analog of `a` in the variable `q^s`:
`[a]_{q^s} = 1 + q^s + q^(2s) + ... + q^((a-1)s)`,
a polynomial in `q` with integer coefficients. The usual `[a]_q` is the case `s = 1`. -/
noncomputable def qAnalog (s a : ℕ) : Polynomial ℤ :=
  ∑ i ∈ Finset.range a, Polynomial.X ^ (s * i)

/-- A polynomial `c_0 + c_1 q + ... + c_N q^N`, with `N` its degree, is unimodal when
`c_0 ≤ c_1 ≤ ... ≤ c_M ≥ c_{M+1} ≥ ... ≥ c_N` for some `M` (the paper's definition,
introduction of arXiv:2605.12822). -/
def Unimodal (P : Polynomial ℤ) : Prop :=
  ∃ M, M ≤ P.natDegree ∧
    (∀ i j, i ≤ j → j ≤ M → P.coeff i ≤ P.coeff j) ∧
    (∀ i j, M ≤ i → i ≤ j → j ≤ P.natDegree → P.coeff j ≤ P.coeff i)

/-- The product `[a_1]_q [a_2]_q ... [a_k]_q [b]_{q^p}`, for the list `a = [a_1, ..., a_k]`. -/
noncomputable def qProduct (a : List ℕ) (b p : ℕ) : Polynomial ℤ :=
  (a.map (qAnalog 1)).prod * qAnalog p b

/-- The condition in the conjecture: `p ∣ a_i` for some `i`, or
`b ≤ 1 + ⌊a_1 / p⌋ + ... + ⌊a_k / p⌋` (`x / p` on natural numbers rounds down). -/
def Condition (a : List ℕ) (b p : ℕ) : Prop :=
  (∃ x ∈ a, p ∣ x) ∨ b ≤ 1 + (a.map (fun x => x / p)).sum

/-- The conjecture exactly as printed (Conjecture `conj:unimodalitylemma`, Section 5 of
B. B. Connelly, E. Ito, T. C. Martinez, O. Shevchenko, K. Yang, "Unimodality of
q-Fibonomial coefficients for small cases", arXiv:2605.12822v1):

"Let `p ≥ 2`, `k ≥ 1` and let `a_1, ..., a_k, b` be positive integers. Then if
`p ∣ a_i` for any `1 ≤ i ≤ k` or `b ≤ 1 + ∑ ⌊a_i / p⌋`, the polynomial
`[a_1]_q ... [a_k]_q [b]_{q^p}` is unimodal. Moreover, if `k ≤ 3` or `p ≤ 3`, this
condition is also necessary."

Here `k` is the length of the list `a`. The first part of the conjunction is the
"if" sentence, the second part is the "Moreover" sentence. -/
def Conjecture : Prop :=
  ∀ (p : ℕ) (a : List ℕ) (b : ℕ), 2 ≤ p → 1 ≤ a.length → (∀ x ∈ a, 1 ≤ x) → 1 ≤ b →
    (Condition a b p → Unimodal (qProduct a b p)) ∧
    ((a.length ≤ 3 ∨ p ≤ 3) → Unimodal (qProduct a b p) → Condition a b p)

/-- The conjecture as printed is false, because its "Moreover" sentence fails for
`p = 3`, `k = 6`: the polynomial `[2]_q^6 [2]_{q^3} = (1 + q)^6 (1 + q^3)` is unimodal
(its coefficients are 1, 6, 15, 21, 21, 21, 21, 15, 6, 1), although `3` divides no
`a_i = 2` and `b = 2 > 1 + 6 * ⌊2 / 3⌋ = 1`.

The claim has three parts: the counterexample is unimodal, the counterexample does
not satisfy the condition, and (therefore) the conjecture as printed does not hold.
Nothing is claimed about the "if" sentence of the conjecture, which stays open. -/
def Claim : Prop :=
  Unimodal (qProduct [2, 2, 2, 2, 2, 2] 2 3) ∧
  ¬ Condition [2, 2, 2, 2, 2, 2] 2 3 ∧
  ¬ Conjecture
