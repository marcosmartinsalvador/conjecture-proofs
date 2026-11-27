import conjectures.dimitrov3_conj5.Statement

/-!
Helper lemmas. This file is the same for the seven slugs `dimitrov3_conj2`, `dimitrov3_conj4`,
..., `dimitrov3_conj9`, apart from the line above. Not every lemma is used by every slug.
-/

/-- `x + 1/x` grows on `[1, ∞)`, in ratio form. -/
theorem ratio_step' (A B u v : ℚ) (hA : 0 < A) (hB : 0 < B) (hu : 0 < u) (huv : u ≤ v)
    (h : v * A ≤ u * B) : v / u + u / v ≤ B / A + A / B := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  rw [div_add_div _ _ hu.ne' hv.ne', div_add_div _ _ hA.ne' hB.ne',
    div_le_div_iff₀ (mul_pos hu hv) (mul_pos hA hB)]
  have h1 : 0 ≤ u * B - v * A := by linarith
  have h2 : 0 ≤ v * B - u * A := by nlinarith
  nlinarith [mul_nonneg h1 h2]

/-- The sum of two Nesbitt terms is smallest when the two variables are equal. -/
theorem nesbitt_sym (x y z : ℚ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) :
    2 * (y + z) / (2 * x + (y + z)) ≤ y / (x + z) + z / (x + y) := by
  rw [div_add_div _ _ (by positivity) (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (add_pos hx (add_pos hy hz)).le (sq_nonneg (y - z))]

/-- One small term `x`, two big terms `y, z` (each at least `P/Q ≥ 1` times `x`). -/
theorem nesbitt_small (x y z P Q : ℚ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hQ : 0 < Q)
    (hQP : Q ≤ P) (h1 : P * x ≤ Q * y) (h2 : P * x ≤ Q * z) :
    Q / (2 * P) + 2 * P / (P + Q) ≤ x / (y + z) + y / (x + z) + z / (x + y) := by
  have hP : 0 < P := lt_of_lt_of_le hQ hQP
  have hs := nesbitt_sym x y z hx hy hz
  have hS : 0 < y + z := add_pos hy hz
  have h12 : 2 * P * x ≤ Q * (y + z) := by linarith
  have key : Q / (2 * P) + 2 * P / (P + Q) ≤ x / (y + z) + 2 * (y + z) / (2 * x + (y + z)) := by
    generalize y + z = S at hS h12 ⊢
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have ha : 0 ≤ Q * S - 2 * P * x := by linarith
    have hSx : 2 * x ≤ S := by nlinarith
    have hb : 0 ≤ 3 * S * P - 2 * x * Q - 2 * x * P - S * Q := by nlinarith
    nlinarith [mul_nonneg ha hb]
  linarith

/-- One big term `z`, two small terms `x, y` (`z` at least `V/U ≥ 1` times each). -/
theorem nesbitt_big (x y z U V : ℚ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hU : 0 < U)
    (hUV : U ≤ V) (h1 : V * x ≤ U * z) (h2 : V * y ≤ U * z) :
    V / (2 * U) + 2 * U / (U + V) ≤ x / (y + z) + y / (x + z) + z / (x + y) := by
  have hV : 0 < V := lt_of_lt_of_le hU hUV
  have hs := nesbitt_sym z x y hz hx hy
  have hS : 0 < x + y := add_pos hx hy
  have h12 : V * (x + y) ≤ 2 * U * z := by linarith
  have key : V / (2 * U) + 2 * U / (U + V) ≤ z / (x + y) + 2 * (x + y) / (2 * z + (x + y)) := by
    generalize x + y = S at hS h12 ⊢
    rw [div_add_div _ _ (by positivity) (by positivity),
      div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    have ha : 0 ≤ 2 * z * U - V * S := by linarith
    have hSz : S ≤ 2 * z := by nlinarith
    have hb : 0 ≤ (S + 2 * z) * (U + V) - 4 * S * U := by nlinarith
    nlinarith [mul_nonneg ha hb]
  have e1 : x / (y + z) + y / (x + z) = x / (z + y) + y / (z + x) := by
    rw [add_comm y z, add_comm x z]
  linarith

theorem prod_pow_factorization (n : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ n.primeFactors, p ^ n.factorization p = n := by
  have := Nat.prod_factorization_pow_eq_self hn
  simpa [Finsupp.prod, Nat.support_factorization] using this

/-- `φ(n) ≤ n - n/q` when `q ≥ 2` divides `n`: the multiples of `q` are not coprime to `n`. -/
theorem totient_add_div_le (n q : ℕ) (hq2 : 2 ≤ q) (hqn : q ∣ n) : Nat.totient n + n / q ≤ n := by
  obtain ⟨m, rfl⟩ := hqn
  have hq0 : 0 < q := by omega
  rw [Nat.mul_div_cancel_left m hq0]
  have hcard := Finset.card_filter_add_card_filter_not
    (s := Finset.range (q * m)) (p := fun a => (q * m).Coprime a)
  rw [Finset.card_range] at hcard
  have hsub : (Finset.range m).image (fun i => q * i)
      ⊆ (Finset.range (q * m)).filter (fun a => ¬ (q * m).Coprime a) := by
    intro a ha
    simp only [Finset.mem_image, Finset.mem_range] at ha
    obtain ⟨i, hi, rfl⟩ := ha
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mul_lt_mul_of_pos_left hi hq0, ?_⟩
    intro hc
    have hd : q ∣ Nat.gcd (q * m) (q * i) := Nat.dvd_gcd (dvd_mul_right _ _) (dvd_mul_right _ _)
    rw [Nat.Coprime] at hc
    rw [hc] at hd
    have := Nat.le_of_dvd one_pos hd
    omega
  have hle := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hq0 h),
    Finset.card_range] at hle
  rw [Nat.totient_eq_card_coprime]
  omega

/-- `ψ(n) ≥ n + n/q` for a prime `q` dividing `n`. -/
theorem psi_ge_add_div (n q : ℕ) (hn : n ≠ 0) (hq : q.Prime) (hqn : q ∣ n) :
    n + n / q ≤ dedekindPsi n := by
  have hmem : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn⟩
  have he1 : 0 < n.factorization q := hq.factorization_pos_of_dvd hn hqn
  obtain ⟨e, he⟩ : ∃ e, n.factorization q = e + 1 := ⟨n.factorization q - 1, by omega⟩
  have hsplit : q ^ (e + 1) * ∏ p ∈ n.primeFactors.erase q, p ^ n.factorization p = n := by
    have := Finset.mul_prod_erase n.primeFactors (fun p => p ^ n.factorization p) hmem
    simp only [he] at this
    rw [this]
    exact prod_pow_factorization n hn
  have hle : ∏ p ∈ n.primeFactors.erase q, p ^ n.factorization p
      ≤ ∏ p ∈ n.primeFactors.erase q, p ^ (n.factorization p - 1) * (p + 1) := by
    refine Finset.prod_le_prod fun p hp => ?_
    have hp' := Finset.mem_of_mem_erase hp
    have hpos : 0 < n.factorization p :=
      (Nat.prime_of_mem_primeFactors hp').factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors hp')
    obtain ⟨m, hm⟩ : ∃ m, n.factorization p = m + 1 := ⟨n.factorization p - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel, pow_succ]
    exact Nat.mul_le_mul_left _ (Nat.le_succ p)
  have hpsi : dedekindPsi n = q ^ e * (q + 1)
      * ∏ p ∈ n.primeFactors.erase q, p ^ (n.factorization p - 1) * (p + 1) := by
    unfold dedekindPsi
    rw [← Finset.mul_prod_erase n.primeFactors _ hmem, he, Nat.add_sub_cancel]
  set r := ∏ p ∈ n.primeFactors.erase q, p ^ n.factorization p with hr
  have hdiv : n / q = q ^ e * r := by
    apply Nat.div_eq_of_eq_mul_right hq.pos
    rw [← hsplit]; ring
  rw [hpsi, hdiv]
  calc n + q ^ e * r = q ^ e * (q + 1) * r := by rw [← hsplit]; ring
    _ ≤ _ := Nat.mul_le_mul_left _ hle

/-- `σ(n) ≤ n + m(m+1)/2`, where `m = n / minFac n` bounds every proper divisor. -/
theorem sigma_le (n : ℕ) (hn : 2 ≤ n) :
    sumDivisors n * 2 ≤ 2 * n + (n / n.minFac + 1) * (n / n.minFac) := by
  unfold sumDivisors
  rw [Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have hsub : n.properDivisors ⊆ Finset.range (n / n.minFac + 1) := by
    intro d hd
    rw [Nat.mem_properDivisors] at hd
    obtain ⟨⟨c, hc⟩, hlt⟩ := hd
    rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_div_iff_mul_le (Nat.minFac_pos n)]
    have hc2 : 2 ≤ c := by
      by_contra h
      have : c = 0 ∨ c = 1 := by omega
      rcases this with rfl | rfl <;> simp at hc <;> omega
    have hmf : n.minFac ≤ c := Nat.minFac_le_of_dvd hc2 ⟨d, by rw [hc]; ring⟩
    calc d * n.minFac ≤ d * c := Nat.mul_le_mul_left _ hmf
      _ = n := hc.symm
  have h1 := Finset.sum_le_sum_of_subset (f := fun d => d) hsub
  have h2 := Finset.sum_range_id_mul_two (n / n.minFac + 1)
  simp only [Nat.add_sub_cancel] at h2
  have h3 : (∑ i ∈ n.properDivisors, i) * 2 ≤ (∑ i ∈ Finset.range (n / n.minFac + 1), i) * 2 :=
    Nat.mul_le_mul_right 2 h1
  linarith

/-- `ψ(n) ≤ σ(n)`. -/
theorem psi_le_sigma (n : ℕ) (hn : n ≠ 0) : dedekindPsi n ≤ sumDivisors n := by
  have hs : sumDivisors n = ArithmeticFunction.sigma 1 n := by
    rw [ArithmeticFunction.sigma_one_apply]; rfl
  rw [hs, ArithmeticFunction.IsMultiplicative.multiplicative_factorization _
    ArithmeticFunction.isMultiplicative_sigma hn]
  unfold dedekindPsi
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_le_prod fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpos : 0 < n.factorization p :=
    hpp.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨m, hm⟩ : ∃ m, n.factorization p = m + 1 := ⟨n.factorization p - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel, ArithmeticFunction.sigma_one_apply_prime_pow hpp,
    Finset.sum_range_succ, Finset.sum_range_succ]
  have : p ^ m * (p + 1) = p ^ m + p ^ (m + 1) := by ring
  omega

/-- The key inequality: `(n+1) φ(n) + σ(n) ≤ n ψ(n)` for `n ≥ 2`, with equality at primes. -/
theorem key_ineq (n : ℕ) (hn : 2 ≤ n) :
    (n + 1) * Nat.totient n + sumDivisors n ≤ n * dedekindPsi n := by
  have hn0 : n ≠ 0 := by omega
  by_cases hp : n.Prime
  · have h1 : Nat.totient n = n - 1 := Nat.totient_prime hp
    have h2 : sumDivisors n = n + 1 := by
      unfold sumDivisors
      rw [hp.divisors, Finset.sum_pair (by omega)]; ring
    have h3 := psi_ge_add_div n n hn0 hp dvd_rfl
    rw [Nat.div_self (by omega)] at h3
    rw [h1, h2]
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
    have hj : j + 2 - 1 = j + 1 := by omega
    have : (j + 2 + 1) * (j + 2 - 1) + (j + 2 + 1) = (j + 2) * (j + 2 + 1) := by
      rw [hj]; ring
    rw [this]
    exact Nat.mul_le_mul_left _ h3
  · have hq : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hqn : n.minFac ∣ n := Nat.minFac_dvd n
    have hlt : n.minFac < n := (Nat.not_prime_iff_minFac_lt hn).mp hp
    have ha := totient_add_div_le n n.minFac hq.two_le hqn
    have hb := psi_ge_add_div n n.minFac hn0 hq hqn
    have hc := sigma_le n hn
    obtain ⟨m, hm⟩ := hqn
    have hdiv : n / n.minFac = m := Nat.div_eq_of_eq_mul_right hq.pos hm
    rw [hdiv] at ha hb hc
    have hq2 := hq.two_le
    have hm2 : 2 ≤ m := by
      by_contra h
      have : m = 0 ∨ m = 1 := by omega
      rcases this with rfl | rfl <;> omega
    have hmn : 2 * m ≤ n := by rw [hm]; exact Nat.mul_le_mul_right m hq2
    generalize Nat.totient n = a at ha ⊢
    generalize dedekindPsi n = b at hb ⊢
    generalize sumDivisors n = c at hc ⊢
    clear hm hdiv hlt hp hq
    nlinarith [Nat.mul_le_mul_left (n + 1) ha, Nat.mul_le_mul_left n hb]

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

/-- `ψ(n) ≥ n + 1` for `n ≥ 2`. -/
theorem psi_ge (n : ℕ) (hn : 2 ≤ n) : n + 1 ≤ dedekindPsi n := by
  have hq : n.minFac.Prime := Nat.minFac_prime (by omega)
  have h := psi_ge_add_div n n.minFac (by omega) hq (Nat.minFac_dvd n)
  have h1 : 0 < n / n.minFac := Nat.div_pos (Nat.minFac_le (by omega)) hq.pos
  omega

/-- The three basic bounds, as rational numbers:
`0 < φ(n) ≤ n - 1`, `ψ(n) ≥ n + 1`, `σ(n) ≥ n + 1` for `n ≥ 2`. -/
theorem basic_bounds (n : ℕ) (hn : 2 ≤ n) :
    (0 : ℚ) < (Nat.totient n : ℚ) ∧ (Nat.totient n : ℚ) ≤ (n : ℚ) - 1
      ∧ (n : ℚ) + 1 ≤ (dedekindPsi n : ℚ) ∧ (n : ℚ) + 1 ≤ (sumDivisors n : ℚ) := by
  have hphi_pos : 0 < Nat.totient n := Nat.totient_pos.mpr (by omega)
  have hphi_le : Nat.totient n ≤ n - 1 := Nat.le_sub_one_of_lt (Nat.totient_lt n (by omega))
  refine ⟨by exact_mod_cast hphi_pos, ?_, by exact_mod_cast psi_ge n hn,
    by exact_mod_cast sigma_ge n hn⟩
  have h : (Nat.totient n : ℚ) ≤ ((n - 1 : ℕ) : ℚ) := by exact_mod_cast hphi_le
  rw [Nat.cast_sub (by omega)] at h
  simpa using h

/-- The two consequences of the key inequality used for sums of two of the functions. -/
theorem key_bounds (n : ℕ) (hn : 2 ≤ n) :
    ((n : ℚ) + 1) * ((Nat.totient n : ℚ) + (sumDivisors n : ℚ))
        ≤ (n : ℚ) * ((dedekindPsi n : ℚ) + (sumDivisors n : ℚ))
      ∧ ((n : ℚ) + 1) * ((Nat.totient n : ℚ) + (dedekindPsi n : ℚ))
        ≤ (n : ℚ) * ((dedekindPsi n : ℚ) + (sumDivisors n : ℚ)) := by
  have h1 : (((n + 1) * Nat.totient n + sumDivisors n : ℕ) : ℚ) ≤ ((n * dedekindPsi n : ℕ) : ℚ) := by
    exact_mod_cast key_ineq n hn
  have h2 : (dedekindPsi n : ℚ) ≤ (sumDivisors n : ℚ) := by
    exact_mod_cast psi_le_sigma n (by omega)
  have hn0 : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
  push_cast at h1
  constructor
  · nlinarith
  · nlinarith [mul_le_mul_of_nonneg_left h2 hn0]

/-- Powers keep the basic bounds. -/
theorem pow_bounds (k : ℕ) (N a b c : ℚ) (hN : 2 ≤ N) (ha : 0 < a) (hat : a ≤ N - 1)
    (hb : N + 1 ≤ b) (hc : N + 1 ≤ c) :
    0 < a ^ k ∧ a ^ k ≤ (N - 1) ^ k ∧ (N - 1) ^ k ≤ (N + 1) ^ k ∧ (N + 1) ^ k ≤ b ^ k
      ∧ (N + 1) ^ k ≤ c ^ k :=
  ⟨pow_pos ha k, pow_le_pow_left₀ ha.le hat k, pow_le_pow_left₀ (by linarith) (by linarith) k,
    pow_le_pow_left₀ (by linarith) hb k, pow_le_pow_left₀ (by linarith) hc k⟩

/-- The power identities used to read the right-hand sides. -/
theorem pow_ids (k : ℕ) (N : ℚ) :
    (N ^ 2 - 1) ^ k = (N - 1) ^ k * (N + 1) ^ k ∧ (N + 1) ^ (2 * k) = ((N + 1) ^ k) ^ 2
      ∧ (N - 1) ^ (2 * k) = ((N - 1) ^ k) ^ 2 ∧ N ^ (2 * k) = (N ^ k) ^ 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← mul_pow]; congr 1; ring
  · rw [← pow_mul, mul_comm]
  · rw [← pow_mul, mul_comm]
  · rw [← pow_mul, mul_comm]

/-- Product form with one small term `x` and two big terms `y, z`. -/
theorem cauchy_small (x y z P Q : ℚ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hQ : 0 < Q)
    (hQP : Q ≤ P) (h1 : P * x ≤ Q * y) (h2 : P * x ≤ Q * z) :
    5 + 2 * (P / Q + Q / P) ≤ (x + y + z) * (1 / x + 1 / y + 1 / z) := by
  have e : (x + y + z) * (1 / x + 1 / y + 1 / z)
      = 3 + (y / x + x / y) + (z / x + x / z) + (y / z + z / y) := by
    field_simp
    ring
  rw [e]
  have s1 := ratio_step' x y Q P hx hy hQ hQP h1
  have s2 := ratio_step' x z Q P hx hz hQ hQP h2
  have s3 : 2 ≤ y / z + z / y := by
    rw [div_add_div _ _ hz.ne' hy.ne', le_div_iff₀ (mul_pos hz hy)]
    nlinarith [sq_nonneg (y - z)]
  linarith

/-- Product form with one big term `z` and two small terms `x, y`. -/
theorem cauchy_big (x y z U V : ℚ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hU : 0 < U)
    (hUV : U ≤ V) (h1 : V * x ≤ U * z) (h2 : V * y ≤ U * z) :
    5 + 2 * (V / U + U / V) ≤ (x + y + z) * (1 / x + 1 / y + 1 / z) := by
  have e : (x + y + z) * (1 / x + 1 / y + 1 / z)
      = 3 + (z / x + x / z) + (z / y + y / z) + (x / y + y / x) := by
    field_simp
    ring
  rw [e]
  have s1 := ratio_step' x z U V hx hz hU hUV h1
  have s2 := ratio_step' y z U V hy hz hU hUV h2
  have s3 : 2 ≤ x / y + y / x := by
    rw [div_add_div _ _ hy.ne' hx.ne', le_div_iff₀ (mul_pos hy hx)]
    nlinarith [sq_nonneg (x - y)]
  linarith

/-- Ratio bound for the terms `φ^k (ψ + σ)` and `ψ^k (φ + σ)` (exponent `k = j + 1`). -/
theorem hypA (t a b c : ℚ) (j : ℕ) (ht : 2 ≤ t) (ha : 0 < a) (hat : a ≤ t - 1)
    (hb : t + 1 ≤ b) (hc : t + 1 ≤ c) :
    t * (t + 1) ^ j * (a ^ (j + 1) * (b + c)) ≤ (t - 1) ^ (j + 1) * (b ^ (j + 1) * (a + c)) := by
  have h0 : ((t + 1) * a) ^ j ≤ ((t - 1) * b) ^ j :=
    pow_le_pow_left₀ (by nlinarith) (by nlinarith) j
  have hα : 0 ≤ t - 1 - a := by linarith
  have hβ : 0 ≤ b - (t + 1) := by linarith
  have hγ : 0 ≤ c - (t + 1) := by linarith
  have ht1 : 0 ≤ t - 1 := by linarith
  have hc1 : 0 ≤ c - 1 := by linarith
  have hc0 : 0 ≤ c := by linarith
  have h1 : t * a * (b + c) ≤ (t - 1) * b * (a + c) := by
    nlinarith [mul_nonneg hγ ht1, mul_nonneg (mul_nonneg hc1 ht1) hβ,
      mul_nonneg (mul_nonneg hc0 (by linarith : (0 : ℚ) ≤ t)) hα, mul_nonneg hα hβ]
  have e1 : t * (t + 1) ^ j * (a ^ (j + 1) * (b + c)) = ((t + 1) * a) ^ j * (t * a * (b + c)) := by
    rw [mul_pow]; ring
  have e2 : (t - 1) ^ (j + 1) * (b ^ (j + 1) * (a + c))
      = ((t - 1) * b) ^ j * ((t - 1) * b * (a + c)) := by
    rw [mul_pow]; ring
  rw [e1, e2]
  exact mul_le_mul h0 h1 (mul_nonneg (mul_nonneg (by linarith) ha.le) (by linarith))
    (pow_nonneg (mul_nonneg ht1 (by linarith)) j)

/-- Ratio bound for the terms `A (B + C)` and `B (A + C)`. -/
theorem hypB (A B C u v : ℚ) (hA : 0 < A) (hAu : A ≤ u) (huv : u ≤ v) (hvB : v ≤ B)
    (hvC : v ≤ C) : (u + v) * (A * (B + C)) ≤ 2 * u * (B * (A + C)) := by
  have hu : 0 < u := lt_of_lt_of_le hA hAu
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have hB : 0 < B := lt_of_lt_of_le hv hvB
  have hC : 0 < C := lt_of_lt_of_le hv hvC
  have t1 : 0 ≤ (u - A) * B * C := by
    have : 0 ≤ u - A := by linarith
    positivity
  have t2 : 0 ≤ (v - u) * (C - v) * A * B := by
    have h1 : 0 ≤ v - u := by linarith
    have h2 : 0 ≤ C - v := by linarith
    positivity
  have t3 : 0 ≤ (u + v) * (B - v) * A * C := by
    have h1 : 0 ≤ B - v := by linarith
    positivity
  have h : v * ((u + v) * (A * (B + C))) ≤ v * (2 * u * (B * (A + C))) := by
    nlinarith [mul_nonneg hv.le t1]
  exact le_of_mul_le_mul_left h hv
