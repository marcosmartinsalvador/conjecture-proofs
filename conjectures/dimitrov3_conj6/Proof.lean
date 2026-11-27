import conjectures.dimitrov3_conj6.Basic

theorem result : Claim := by
  intro k n hk hn φ ψ σ N
  have ha : 0 < φ := (basic_bounds n hn).1
  have hat : φ ≤ N - 1 := (basic_bounds n hn).2.1
  have hb : N + 1 ≤ ψ := (basic_bounds n hn).2.2.1
  have hc : N + 1 ≤ σ := (basic_bounds n hn).2.2.2
  have hN : (2 : ℚ) ≤ N := by
    have h : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
    exact h
  clear_value φ ψ σ N
  obtain ⟨hA, hAu, huv, hvB, hvC⟩ := pow_bounds k N φ ψ σ hN ha hat hb hc
  obtain ⟨e1, e2, e3, -⟩ := pow_ids k N
  rw [e1, e2, e3]
  generalize φ ^ k = A at hA hAu ⊢
  generalize ψ ^ k = B at hvB ⊢
  generalize σ ^ k = C at hvC ⊢
  generalize (N - 1) ^ k = u at hAu huv ⊢
  generalize (N + 1) ^ k = v at huv hvB hvC ⊢
  have hu : 0 < u := lt_of_lt_of_le hA hAu
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hB : 0 < B := lt_of_lt_of_le hv hvB
  have hC : 0 < C := lt_of_lt_of_le hv hvC
  have h1 := hypB A B C u v hA hAu huv hvB hvC
  have h2 := hypB A C B u v hA hAu huv hvC hvB
  rw [add_comm C B] at h2
  have rhs : (4 * u ^ 2 + u * v + v ^ 2) / (2 * (u ^ 2 + u * v))
      = v / (2 * u) + 2 * u / (u + v) := by
    field_simp
    ring
  have lhs : A * B / (C * (A + B)) + A * C / (B * (A + C)) + B * C / (A * (B + C))
      = (1 / B) / (1 / C + 1 / A) + (1 / C) / (1 / B + 1 / A) + (1 / A) / (1 / B + 1 / C) := by
    field_simp
    ring
  rw [rhs, lhs]
  refine nesbitt_big (1 / B) (1 / C) (1 / A) u v (by positivity) (by positivity) (by positivity)
    hu huv ?_ ?_
  · rw [mul_one_div, mul_one_div, div_le_div_iff₀ hB hA]
    nlinarith
  · rw [mul_one_div, mul_one_div, div_le_div_iff₀ hC hA]
    nlinarith
