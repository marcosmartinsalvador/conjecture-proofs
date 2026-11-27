import conjectures.ultra_euclidean_ring_not_poly.Statement

/-!
The counterexample is the ring `ℚ[T;T⁻¹]` of Laurent polynomials. Level `n` consists of the
Laurent polynomials whose exponents lie in a window of `n + 1` consecutive integers that
grows by one step at a time, alternately to the right and to the left:
`{0}`, `{0,1}`, `{-1,0,1}`, `{-1,0,1,2}`, ... The function `lvl a` is the first level that
contains `a`. It is ultra-Euclidean. But the ring is not a field, because `1 - T` is not zero
and not a unit. And it is not a polynomial ring `K[x]` over a field: there the sum of two units
is zero or a unit (the units are the nonzero constants), while here `1` and `-T` are units and
their sum `1 - T` is neither.
-/

open Polynomial LaurentPolynomial

namespace UltraEuclid

/-- The `n`-th level: Laurent polynomials whose exponents lie in the window of
`n + 1` consecutive integers starting at `-(n / 2)`. -/
def lev (n : ℕ) : Set ℚ[T;T⁻¹] :=
  {a | ∃ P : ℚ[X], P.natDegree ≤ n ∧ a = T (-((n / 2 : ℕ) : ℤ)) * toLaurent P}

theorem lev_add {n : ℕ} {a b : ℚ[T;T⁻¹]} (ha : a ∈ lev n) (hb : b ∈ lev n) :
    a + b ∈ lev n := by
  obtain ⟨P, hP, rfl⟩ := ha
  obtain ⟨Q, hQ, rfl⟩ := hb
  refine ⟨P + Q, (natDegree_add_le P Q).trans (max_le hP hQ), ?_⟩
  rw [map_add, mul_add]

theorem lev_succ {n : ℕ} {a : ℚ[T;T⁻¹]} (ha : a ∈ lev n) : a ∈ lev (n + 1) := by
  obtain ⟨P, hP, rfl⟩ := ha
  rcases Nat.even_or_odd n with he | ho
  · have e : (n + 1) / 2 = n / 2 := by
      obtain ⟨k, rfl⟩ := he
      omega
    exact ⟨P, by omega, by rw [e]⟩
  · have e : (n + 1) / 2 = n / 2 + 1 := by
      obtain ⟨k, rfl⟩ := ho
      omega
    refine ⟨X * P, ?_, ?_⟩
    · have h1 := natDegree_mul_le (p := (X : ℚ[X])) (q := P)
      have h2 : (X : ℚ[X]).natDegree ≤ 1 := natDegree_X_le
      omega
    · rw [e, map_mul, toLaurent_X, ← mul_assoc, ← T_add]
      congr 2
      push_cast
      ring

theorem lev_mono {m n : ℕ} (h : m ≤ n) {a : ℚ[T;T⁻¹]} (ha : a ∈ lev m) : a ∈ lev n := by
  induction n, h using Nat.le_induction with
  | base => exact ha
  | succ k _ ih => exact lev_succ ih

theorem exists_lev (a : ℚ[T;T⁻¹]) : ∃ n, a ∈ lev n := by
  obtain ⟨N, A, hA⟩ := exists_T_pow a
  refine ⟨2 * (N + A.natDegree), X ^ A.natDegree * A, ?_, ?_⟩
  · have h1 := natDegree_mul_le (p := (X : ℚ[X]) ^ A.natDegree) (q := A)
    have h2 : ((X : ℚ[X]) ^ A.natDegree).natDegree ≤ A.natDegree := natDegree_X_pow_le _
    omega
  · have e : 2 * (N + A.natDegree) / 2 = N + A.natDegree := by omega
    have hT : (T (-((N + A.natDegree : ℕ) : ℤ)) : ℚ[T;T⁻¹]) * T (A.natDegree : ℤ) * T (N : ℤ)
        = 1 := by
      rw [← T_add, ← T_add]
      have : (-((N + A.natDegree : ℕ) : ℤ) + (A.natDegree : ℤ) + (N : ℤ)) = 0 := by
        push_cast
        ring
      rw [this, T_zero]
    rw [e, map_mul, toLaurent_X_pow, hA]
    linear_combination (-a) * hT

/-- The candidate ultra-Euclidean function: the first level containing `a`. -/
noncomputable def lvl (a : ℚ[T;T⁻¹]) : ℕ := sInf {n | a ∈ lev n}

theorem lvl_mem (a : ℚ[T;T⁻¹]) : a ∈ lev (lvl a) :=
  Nat.sInf_mem (s := {n | a ∈ lev n}) (exists_lev a)

theorem lvl_le {a : ℚ[T;T⁻¹]} {n : ℕ} (h : a ∈ lev n) : lvl a ≤ n :=
  Nat.sInf_le (s := {n | a ∈ lev n}) h

theorem lvl_add (a b : ℚ[T;T⁻¹]) : lvl (a + b) ≤ max (lvl a) (lvl b) :=
  lvl_le (lev_add (lev_mono (le_max_left _ _) (lvl_mem a))
    (lev_mono (le_max_right _ _) (lvl_mem b)))

/-- Division by a polynomial with nonzero constant term, inside the Laurent ring:
every Laurent polynomial is congruent to a polynomial of smaller degree. -/
theorem exists_rem (P : ℚ[X]) (hP : P.coeff 0 ≠ 0) (c : ℚ[T;T⁻¹]) :
    ∃ R : ℚ[X], R.degree < P.degree ∧ toLaurent P ∣ c - toLaurent R := by
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  obtain ⟨N, A, hA⟩ := exists_T_pow c
  set u : ℚ[X] := -(Polynomial.C (P.coeff 0)⁻¹ * P.divX) with hu
  -- `X` is invertible modulo `P`, with inverse `u`
  have h1 : P ∣ 1 - X * u := by
    refine ⟨Polynomial.C (P.coeff 0)⁻¹, ?_⟩
    have h := divX_mul_X_add P
    have hc : (Polynomial.C (P.coeff 0)⁻¹ : ℚ[X]) * Polynomial.C (P.coeff 0) = 1 := by
      rw [← Polynomial.C_mul, inv_mul_cancel₀ hP, Polynomial.C_1]
    rw [hu]
    linear_combination (Polynomial.C (P.coeff 0)⁻¹ : ℚ[X]) * h - hc
  have h2 : P ∣ 1 - (X * u) ^ N := by
    have := sub_dvd_pow_sub_pow (1 : ℚ[X]) (X * u) N
    rw [one_pow] at this
    exact h1.trans this
  refine ⟨(u ^ N * A) % P, degree_mod_lt _ hP0, ?_⟩
  have h3 := EuclideanDomain.mod_add_div (u ^ N * A) P
  have hT : (T (-(N : ℤ)) : ℚ[T;T⁻¹]) * T 1 ^ N = 1 := by
    rw [T_pow, ← T_add]
    simp
  have hc : c = toLaurent A * T (-(N : ℤ)) := by
    rw [hA, mul_assoc, ← T_add]
    simp
  have key : c - toLaurent ((u ^ N * A) % P)
      = T (-(N : ℤ)) * toLaurent (A * (1 - (X * u) ^ N))
        + toLaurent (P * (u ^ N * A / P)) := by
    have h4 : toLaurent ((u ^ N * A) % P)
        = toLaurent (u ^ N * A) - toLaurent (P * (u ^ N * A / P)) := by
      rw [← map_sub]
      congr 1
      linear_combination h3
    rw [h4, hc]
    simp only [map_mul, map_sub, map_pow, map_one, toLaurent_X]
    linear_combination (toLaurent A * toLaurent u ^ N) * hT
  rw [key]
  exact dvd_add (Dvd.dvd.mul_left (map_dvd toLaurent (Dvd.dvd.mul_left h2 A)) _)
    (map_dvd toLaurent (dvd_mul_right _ _))

theorem lvl_euclid : IsEuclideanFn lvl := by
  intro a b hb
  obtain ⟨P, hPn, hPb⟩ := lvl_mem b
  have hP0 : P ≠ 0 := by
    rintro rfl
    apply hb
    rw [hPb, map_zero, mul_zero]
  obtain ⟨Q, hQ, hXQ⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hP0 0
  rw [Polynomial.C_0, sub_zero] at hQ hXQ
  set k := rootMultiplicity 0 P
  have hQ0 : Q.coeff 0 ≠ 0 := fun h => hXQ (X_dvd_iff.2 h)
  have hQn : Q.natDegree ≤ lvl b :=
    (natDegree_le_of_dvd (Dvd.intro_left _ hQ.symm) hP0).trans hPn
  -- `b` is a unit times `Q`
  have hbQ : b = (T (-((lvl b / 2 : ℕ) : ℤ)) * T (k : ℤ)) * toLaurent Q :=
    hPb.trans (by rw [hQ, map_mul, toLaurent_X_pow, mul_assoc])
  have hw : IsUnit (T (-((lvl b / 2 : ℕ) : ℤ)) * T (k : ℤ) : ℚ[T;T⁻¹]) :=
    (isUnit_T _).mul (isUnit_T _)
  set m := lvl b - 1 with hm
  obtain ⟨R, hR, hdvd⟩ := exists_rem Q hQ0 (a * T ((m / 2 : ℕ) : ℤ))
  set r : ℚ[T;T⁻¹] := T (-((m / 2 : ℕ) : ℤ)) * toLaurent R with hr
  have hdvd2 : b ∣ a - r := by
    rw [hbQ, hw.mul_left_dvd]
    have e : a - r = (a * T ((m / 2 : ℕ) : ℤ) - toLaurent R) * T (-((m / 2 : ℕ) : ℤ)) := by
      have hT : (T ((m / 2 : ℕ) : ℤ) : ℚ[T;T⁻¹]) * T (-((m / 2 : ℕ) : ℤ)) = 1 := by
        rw [← T_add]
        simp
      rw [hr]
      linear_combination (-a) * hT
    rw [e]
    exact Dvd.dvd.mul_right hdvd _
  obtain ⟨q, hq⟩ := hdvd2
  refine ⟨q, r, by linear_combination hq, ?_⟩
  by_cases hR0 : R = 0
  · left
    rw [hr, hR0, map_zero, mul_zero]
  · right
    have h1 : R.natDegree < Q.natDegree := natDegree_lt_natDegree hR0 hR
    have h2 : r ∈ lev m := ⟨R, by omega, rfl⟩
    have h3 := lvl_le h2
    omega

theorem lvl_ultra : IsUltraEuclidean lvl :=
  ⟨lvl_euclid, fun a b _ _ _ => lvl_add a b⟩

theorem lvl_one : lvl (1 : ℚ[T;T⁻¹]) = 0 := by
  have : (1 : ℚ[T;T⁻¹]) ∈ lev 0 := ⟨1, by simp, by simp⟩
  exact Nat.le_zero.1 (lvl_le this)

/-- The ring map sending `T` to `1` (sum of the coefficients). -/
noncomputable def aug : ℚ[T;T⁻¹] →+* ℚ := LaurentPolynomial.eval₂ (RingHom.id ℚ) 1

theorem aug_T (n : ℤ) : aug (T n) = 1 := by
  simp [aug, LaurentPolynomial.eval₂_T]

theorem aug_one_sub_T : aug (1 - T 1) = 0 := by
  rw [map_sub, map_one, aug_T, sub_self]

theorem one_sub_T_ne_zero : (1 - T 1 : ℚ[T;T⁻¹]) ≠ 0 := by
  intro h
  have h1 : (T 0 : ℚ[T;T⁻¹]) = T 1 := by
    rw [T_zero]
    linear_combination h
  have h2 : (T 0 : ℚ[T;T⁻¹]).coeff 1 = (T 1 : ℚ[T;T⁻¹]).coeff 1 := by rw [h1]
  rw [T_apply, T_apply] at h2
  norm_num at h2

theorem not_isUnit_one_sub_T : ¬ IsUnit (1 - T 1 : ℚ[T;T⁻¹]) := by
  intro h
  have := h.map aug
  rw [aug_one_sub_T] at this
  exact not_isUnit_zero this

theorem lvl_mul_pos {c : ℚ[T;T⁻¹]} (hc : c ≠ 0) : 0 < lvl ((1 - T 1) * c) := by
  by_contra h0
  have h0' : lvl ((1 - T 1) * c) = 0 := by omega
  have hmem := lvl_mem ((1 - T 1) * c)
  rw [h0'] at hmem
  obtain ⟨P, hP, hPe⟩ := hmem
  have hPC := eq_C_of_natDegree_le_zero hP
  have h1 := congrArg aug hPe
  rw [map_mul, aug_one_sub_T, zero_mul, map_mul, aug_T, one_mul, hPC, toLaurent_C] at h1
  have h2 : aug (LaurentPolynomial.C (P.coeff 0)) = P.coeff 0 := by
    simp [aug, LaurentPolynomial.eval₂_C]
  rw [h2] at h1
  have h3 : (1 - T 1) * c = 0 := by
    rw [hPe, hPC, ← h1]
    simp
  exact (mul_ne_zero one_sub_T_ne_zero hc) h3

end UltraEuclid

open UltraEuclid

theorem result : Claim := by
  intro h
  rcases h ℚ[T;T⁻¹] ⟨lvl, lvl_ultra⟩ with hf | ⟨K, _, ⟨e⟩⟩
  · obtain ⟨b, hb⟩ := hf.mul_inv_cancel one_sub_T_ne_zero
    exact not_isUnit_one_sub_T (IsUnit.of_mul_eq_one _ hb)
  · have hu : IsUnit (e (-T 1)) := ((isUnit_T (R := ℚ) 1).neg).map e
    obtain ⟨r, _, hr⟩ := Polynomial.isUnit_iff.1 hu
    have he : e (1 - T 1) = Polynomial.C (1 + r) := by
      rw [sub_eq_add_neg, map_add, map_one, ← hr, Polynomial.C_add, Polynomial.C_1]
    have hne : e (1 - T 1) ≠ 0 := (map_ne_zero_iff e e.injective).2 one_sub_T_ne_zero
    have hr0 : 1 + r ≠ 0 := by
      intro h0
      rw [he, h0, Polynomial.C_0] at hne
      exact hne rfl
    have hu2 : IsUnit (e (1 - T 1)) := by
      rw [he]
      exact Polynomial.isUnit_C.2 (IsUnit.mk0 _ hr0)
    have hu3 : IsUnit (e.symm (e (1 - T 1))) := hu2.map e.symm
    rw [RingEquiv.symm_apply_apply] at hu3
    exact not_isUnit_one_sub_T hu3
