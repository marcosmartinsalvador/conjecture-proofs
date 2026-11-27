import conjectures.qanalog_product_unimodality.Statement

open Polynomial

/-- The counterexample written out: `(1 + q)^6 (1 + q^3)`. -/
theorem qProduct_example :
    qProduct [2, 2, 2, 2, 2, 2] 2 3 =
      (X : Polynomial ℤ) ^ 9 + 6 * X ^ 8 + 15 * X ^ 7 + 21 * X ^ 6 + 21 * X ^ 5 + 21 * X ^ 4
        + 21 * X ^ 3 + 15 * X ^ 2 + 6 * X + 1 := by
  simp only [qProduct, qAnalog, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Finset.sum_range_succ, Finset.sum_range_zero]
  ring

theorem natDegree_example : (qProduct [2, 2, 2, 2, 2, 2] 2 3).natDegree = 9 := by
  rw [qProduct_example]
  compute_degree!

theorem coeff_example (n : ℕ) (hn : n ≤ 9) :
    (qProduct [2, 2, 2, 2, 2, 2] 2 3).coeff n = [1, 6, 15, 21, 21, 21, 21, 15, 6, 1].getD n 0 := by
  rw [qProduct_example]
  interval_cases n <;>
    simp [coeff_X_pow, coeff_X, coeff_one, coeff_ofNat_mul]

theorem unimodal_example : Unimodal (qProduct [2, 2, 2, 2, 2, 2] 2 3) := by
  refine ⟨3, by rw [natDegree_example]; norm_num, ?_, ?_⟩
  · intro i j hij hj
    rw [coeff_example i (by omega), coeff_example j (by omega)]
    interval_cases j <;> interval_cases i <;> simp
  · intro i j hi hij hj
    rw [natDegree_example] at hj
    rw [coeff_example i (by omega), coeff_example j (by omega)]
    interval_cases j <;> interval_cases i <;> simp

theorem not_condition_example : ¬ Condition [2, 2, 2, 2, 2, 2] 2 3 := by
  simp [Condition]

theorem result : Claim := by
  refine ⟨unimodal_example, not_condition_example, ?_⟩
  intro h
  have h1 := (h 3 [2, 2, 2, 2, 2, 2] 2 (by norm_num) (by simp) (by simp) (by norm_num)).2
    (Or.inr le_rfl) unimodal_example
  exact not_condition_example h1
