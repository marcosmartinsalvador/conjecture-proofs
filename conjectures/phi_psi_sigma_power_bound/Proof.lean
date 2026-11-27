import conjectures.phi_psi_sigma_power_bound.Statement

/-- A product of sums is at least the product of the first summands. -/
theorem prod_add_ge (s : Finset ℕ) (f g : ℕ → ℕ) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ s, (f i + g i) :=
  Finset.prod_le_prod fun _ _ => Nat.le_add_right _ _

/-- Over a nonempty index set, with every second summand at least one, a product of
sums exceeds the product of the first summands by at least one. -/
theorem prod_add_ge_succ (s : Finset ℕ) (f g : ℕ → ℕ) (hs : s.Nonempty)
    (hg : ∀ i ∈ s, 1 ≤ g i) : ∏ i ∈ s, f i + 1 ≤ ∏ i ∈ s, (f i + g i) := by
  obtain ⟨a, ha⟩ := hs
  rw [← Finset.mul_prod_erase s _ ha, ← Finset.mul_prod_erase s (fun i => f i + g i) ha]
  have h1 : ∏ i ∈ s.erase a, f i ≤ ∏ i ∈ s.erase a, (f i + g i) := prod_add_ge _ f g
  have h2 : 1 ≤ ∏ i ∈ s.erase a, (f i + g i) :=
    Finset.one_le_prod fun i hi => le_trans (hg i (Finset.mem_of_mem_erase hi)) (Nat.le_add_left _ _)
  have h3 : 1 ≤ g a := hg a ha
  calc f a * ∏ i ∈ s.erase a, f i + 1
      ≤ f a * ∏ i ∈ s.erase a, (f i + g i) + 1 * ∏ i ∈ s.erase a, (f i + g i) := by
        have := Nat.mul_le_mul_left (f a) h1
        omega
    _ ≤ f a * ∏ i ∈ s.erase a, (f i + g i) + g a * ∏ i ∈ s.erase a, (f i + g i) := by
        have := Nat.mul_le_mul_right (∏ i ∈ s.erase a, (f i + g i)) h3
        omega
    _ = (f a + g a) * ∏ i ∈ s.erase a, (f i + g i) := by ring

/-- `ψ(n) ≥ n + 1` for `n ≥ 2`. -/
theorem psi_ge (n : ℕ) (hn : 2 ≤ n) : n + 1 ≤ dedekindPsi n := by
  have hn0 : n ≠ 0 := by omega
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  have key := prod_add_ge_succ n.primeFactors (fun p => p ^ n.factorization p)
    (fun p => p ^ (n.factorization p - 1)) hne
    (fun p hp => Nat.one_le_pow _ _ (Nat.pos_of_mem_primeFactors hp))
  have hprod : ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
    have := Nat.prod_factorization_pow_eq_self hn0
    simpa [Finsupp.prod, Nat.support_factorization] using this
  have hpsi : dedekindPsi n
      = ∏ p ∈ n.primeFactors, (p ^ n.factorization p + p ^ (n.factorization p - 1)) := by
    unfold dedekindPsi
    refine Finset.prod_congr rfl fun p hp => ?_
    have hpos : 0 < n.factorization p :=
      (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn0 (Nat.dvd_of_mem_primeFactors hp)
    obtain ⟨m, hm⟩ : ∃ m, n.factorization p = m + 1 := ⟨n.factorization p - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    ring
  rw [hpsi]
  simpa [hprod] using key

/-- `σ(n) ≥ n + 1` for `n ≥ 2`. -/
theorem sigma_ge (n : ℕ) (hn : 2 ≤ n) : n + 1 ≤ sumDivisors n := by
  unfold sumDivisors
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.one_mem_divisors.mpr (by omega)
    · exact Nat.mem_divisors_self _ (by omega)
  have h1n : (1 : ℕ) ≠ n := by omega
  calc n + 1 = ∑ d ∈ ({1, n} : Finset ℕ), d := by
        rw [Finset.sum_pair h1n]; ring
    _ ≤ ∑ d ∈ n.divisors, d := Finset.sum_le_sum_of_subset hsub

/-- The two-variable step: `x + 1/x` grows on `[1, ∞)`. -/
theorem ratio_step (A B u v : ℚ) (hA : 0 < A) (hAu : A ≤ u) (huv : u ≤ v) (hvB : v ≤ B) :
    v / u + u / v ≤ B / A + A / B := by
  have hu : 0 < u := lt_of_lt_of_le hA hAu
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hB : 0 < B := lt_of_lt_of_le hv hvB
  rw [div_add_div _ _ hu.ne' hv.ne', div_add_div _ _ hA.ne' hB.ne',
    div_le_div_iff₀ (mul_pos hu hv) (mul_pos hA hB)]
  have h1 : 0 ≤ B * u - A * v := by nlinarith
  have h2 : 0 ≤ B * v - A * u := by nlinarith
  nlinarith [mul_nonneg h1 h2]

theorem result : Claim := by
  intro k n _ hn
  have hn' : (2 : ℚ) ≤ n := by exact_mod_cast hn
  -- the three functions
  have hphi_pos : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
  have hphi_le : Nat.totient n ≤ n - 1 := Nat.le_sub_one_of_lt (Nat.totient_lt n (by omega))
  have hpsi := psi_ge n hn
  have hsig := sigma_ge n hn
  have ha_pos : (0 : ℚ) < (Nat.totient n : ℚ) := by exact_mod_cast hphi_pos
  have ha_le : (Nat.totient n : ℚ) ≤ (n : ℚ) - 1 := by
    have h : (Nat.totient n : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by exact_mod_cast hphi_le
    rw [Nat.cast_sub (by omega)] at h
    simpa using h
  have hb_ge : (n : ℚ) + 1 ≤ (dedekindPsi n : ℚ) := by exact_mod_cast hpsi
  have hc_ge : (n : ℚ) + 1 ≤ (sumDivisors n : ℚ) := by exact_mod_cast hsig
  generalize (Nat.totient n : ℚ) = a at ha_pos ha_le ⊢
  generalize (dedekindPsi n : ℚ) = b at hb_ge ⊢
  generalize (sumDivisors n : ℚ) = c at hc_ge ⊢
  -- k-th powers
  set A : ℚ := a ^ k with hA
  set B : ℚ := b ^ k with hB
  set C : ℚ := c ^ k with hC
  set u : ℚ := ((n : ℚ) - 1) ^ k with hu
  set v : ℚ := ((n : ℚ) + 1) ^ k with hv
  have hA_pos : 0 < A := pow_pos ha_pos k
  have hAu : A ≤ u := pow_le_pow_left₀ ha_pos.le ha_le k
  have huv : u ≤ v := pow_le_pow_left₀ (by linarith) (by linarith) k
  have hvB : v ≤ B := pow_le_pow_left₀ (by linarith) hb_ge k
  have hvC : v ≤ C := pow_le_pow_left₀ (by linarith) hc_ge k
  have hu_pos : 0 < u := lt_of_lt_of_le hA_pos hAu
  have hv_pos : 0 < v := lt_of_lt_of_le hu_pos huv
  have hB_pos : 0 < B := lt_of_lt_of_le hv_pos hvB
  have hC_pos : 0 < C := lt_of_lt_of_le hv_pos hvC
  -- the right-hand side in terms of u and v
  have e1 : ((n : ℚ) ^ 2 - 1) ^ k = u * v := by
    rw [hu, hv, ← mul_pow]; congr 1; ring
  have e2 : ((n : ℚ) + 1) ^ (2 * k) = v ^ 2 := by rw [hv, ← pow_mul, mul_comm]
  have e3 : ((n : ℚ) - 1) ^ (2 * k) = u ^ 2 := by rw [hu, ← pow_mul, mul_comm]
  rw [e1, e2, e3]
  have rhs : (5 * (u * v) + 2 * v ^ 2 + 2 * u ^ 2) / (u * v) = 5 + 2 * (v / u + u / v) := by
    field_simp
    ring
  have lhs : (A + B + C) * (1 / A + 1 / B + 1 / C)
      = 3 + (B / A + A / B) + (C / A + A / C) + (B / C + C / B) := by
    field_simp
    ring
  rw [rhs, lhs]
  have s1 := ratio_step A B u v hA_pos hAu huv hvB
  have s2 := ratio_step A C u v hA_pos hAu huv hvC
  have s3 : 2 ≤ B / C + C / B := by
    rw [div_add_div _ _ hC_pos.ne' hB_pos.ne', le_div_iff₀ (mul_pos hC_pos hB_pos)]
    nlinarith [sq_nonneg (B - C)]
  linarith
