import conjectures.euler_liars_quarter.Statement

/-!
Proof of the Euler liars conjecture of arXiv:2602.21840.

Plan. `G = (ℤ/n)ˣ`, `E ≤ G` the Euler liars, `K ≤ G` the Fermat liars (`u^(n-1) = 1`).
`E ≤ K`, and `u * u ∈ E` forces `u ∈ K`.
* Index 2: every square is in `E`, so `K = G`, so `n` is Carmichael.
* Index 4, `n` not Carmichael: some prime `q ∣ n` has `(q-1) ∤ (n-1)`. Lift a generator
  mod `q` to a unit `g` that is `1` mod `n/q`. Then `g ∉ K`, `g² ∈ K \ E`, so
  `[G:K] = [K:E] = 2`. For another prime `p ∣ n` lift a generator mod `p` to `h`. Index 2
  of `K` gives `h ∈ K`, so `(p-1) ∣ (n-1)`. The Jacobi symbol of `h` is `-1`, so `h ∉ E`,
  and index 2 of `E` in `K` gives `h g² ∈ E`. Reading that modulo a third prime gives
  `1 = -1`. So `n = p q`, and the divisibilities force `q = 2p - 1`.
-/

/-- A generator of the units modulo an odd prime, as an element of `ZMod p`. -/
theorem exists_gen (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ∃ x : ZMod p, x ≠ 0 ∧ (∀ k : ℕ, x ^ k = 1 → (p - 1) ∣ k) ∧ ¬ IsSquare x := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨γ, hγ⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hord : orderOf γ = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hγ, Nat.card_eq_fintype_card, ZMod.card_units]
  have hk : ∀ k : ℕ, (γ : ZMod p) ^ k = 1 → (p - 1) ∣ k := by
    intro k hk
    rw [← hord, orderOf_dvd_iff_pow_eq_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hk, Units.val_one]
  refine ⟨γ, γ.ne_zero, hk, ?_⟩
  rintro ⟨y, hy⟩
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hy
    exact γ.ne_zero hy
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have h1 : (γ : ZMod p) ^ ((p - 1) / 2) = 1 := by
    rw [hy, ← pow_two, ← pow_mul]
    have : 2 * ((p - 1) / 2) = p - 1 := by omega
    rw [this]
    exact ZMod.pow_card_sub_one_eq_one hy0
  have h4 := Nat.le_of_dvd (by omega) (hk _ h1)
  omega

/-- Chinese remainder lift: a residue `x ≠ 0` modulo a prime `p ∣ n` (with `n`
squarefree) lifts to a natural number that is `1` modulo `n / p` and coprime to `n`. -/
theorem exists_lift (n p : ℕ) (hn : Squarefree n) (hp : p.Prime) (hpn : p ∣ n)
    (x : ZMod p) (hx : x ≠ 0) :
    ∃ a : ℕ, (a : ZMod p) = x ∧ a ≡ 1 [MOD n / p] ∧ a.Coprime n := by
  haveI := Fact.mk hp
  obtain ⟨m, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left m hp.pos]
  have hco : p.Coprime m := (Nat.squarefree_mul_iff.mp hn).1
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hco x.val 1
  have hkx : (k : ZMod p) = x := by
    rw [(ZMod.natCast_eq_natCast_iff k x.val p).mpr hk1, ZMod.natCast_zmod_val]
  refine ⟨k, hkx, hk2, ?_⟩
  apply Nat.Coprime.mul_right
  · rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    apply hx
    rw [← hkx, (ZMod.natCast_eq_zero_iff k p).mpr hd]
  · have := hk2.gcd_eq
    rw [Nat.gcd_one_left] at this
    exact this

/-- The Jacobi symbol of such a lift of a non-square is `-1`. -/
theorem jacobi_lift (n p : ℕ) (hodd : Odd n) (hp : p.Prime) (hpn : p ∣ n) (a : ℕ)
    (h1 : a ≡ 1 [MOD n / p]) (hns : ¬ IsSquare (a : ZMod p)) : jacobiSym (a : ℤ) n = -1 := by
  haveI := Fact.mk hp
  obtain ⟨m, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left m hp.pos] at h1
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hodd
  haveI : NeZero m := ⟨hm0⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  rw [jacobiSym.mul_right]
  have e1 : jacobiSym (a : ℤ) m = 1 := by
    rw [jacobiSym.mod_left' (a₂ := 1) (by exact_mod_cast h1), jacobiSym.one_left]
  have e2 : jacobiSym (a : ℤ) p = -1 := by
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    rw [Int.cast_natCast]
    exact hns
  rw [e1, e2]
  rfl

/-- The Jacobi symbol of a unit of `ZMod n`. -/
def jac (n : ℕ) (u : (ZMod n)ˣ) : ℤ := jacobiSym (((u : ZMod n).val : ℕ) : ℤ) n

theorem jac_mul (n : ℕ) (u v : (ZMod n)ˣ) : jac n (u * v) = jac n u * jac n v := by
  unfold jac
  rw [Units.val_mul, ZMod.val_mul, ← jacobiSym.mul_left]
  apply jacobiSym.mod_left'
  push_cast
  exact Int.emod_emod_of_dvd _ dvd_rfl

theorem jac_sq (n : ℕ) (u : (ZMod n)ˣ) : jac n u * jac n u = 1 := by
  have h : (((u : ZMod n).val : ℕ) : ℤ).gcd (n : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact ZMod.val_coe_unit_coprime u
  rcases jacobiSym.eq_one_or_neg_one h with h | h <;> (unfold jac; rw [h]; rfl)

theorem jac_one (n : ℕ) : jac n 1 = 1 := by
  have h := jac_sq n 1
  rw [← jac_mul, mul_one] at h
  exact h

theorem jac_unitOfCoprime (n : ℕ) [NeZero n] (a : ℕ) (h : a.Coprime n) :
    jac n (ZMod.unitOfCoprime a h) = jacobiSym (a : ℤ) n := by
  unfold jac
  rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast]
  apply jacobiSym.mod_left'
  push_cast
  exact Int.emod_emod_of_dvd _ dvd_rfl

/-- The Euler liars as a subgroup of the units. -/
def liarSubgroup (n : ℕ) : Subgroup (ZMod n)ˣ where
  carrier := {u | ((jac n u : ℤ) : ZMod n) = (u : ZMod n) ^ ((n - 1) / 2)}
  mul_mem' := by
    intro u v hu hv
    simp only [Set.mem_ofPred_eq] at *
    rw [jac_mul, Int.cast_mul, hu, hv, Units.val_mul, mul_pow]
  one_mem' := by
    simp only [Set.mem_ofPred_eq]
    rw [jac_one, Units.val_one, one_pow, Int.cast_one]
  inv_mem' := by
    intro u hu
    simp only [Set.mem_ofPred_eq] at *
    have h1 : ((jac n u⁻¹ : ℤ) : ZMod n) * ((jac n u : ℤ) : ZMod n) = 1 := by
      rw [← Int.cast_mul, ← jac_mul, inv_mul_cancel, jac_one, Int.cast_one]
    have h2 : ((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2) * (u : ZMod n) ^ ((n - 1) / 2) = 1 := by
      rw [← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
    rw [hu] at h1
    linear_combination
      ((u⁻¹ : (ZMod n)ˣ) : ZMod n) ^ ((n - 1) / 2) * h1 - ((jac n u⁻¹ : ℤ) : ZMod n) * h2

theorem mem_liarSubgroup (n : ℕ) (u : (ZMod n)ˣ) :
    u ∈ liarSubgroup n ↔ ((jac n u : ℤ) : ZMod n) = (u : ZMod n) ^ ((n - 1) / 2) :=
  Iff.rfl

/-- The number of Euler liars is the order of the subgroup. -/
theorem card_liars (n : ℕ) [NeZero n] : numEulerLiars n = Nat.card (liarSubgroup n) := by
  unfold numEulerLiars
  rw [← Nat.card_eq_finsetCard]
  let S := (Finset.range n).filter fun a => Nat.Coprime a n ∧ IsEulerLiar n a
  have hS : ∀ a : S, (a : ℕ) < n ∧ Nat.Coprime (a : ℕ) n ∧ IsEulerLiar n (a : ℕ) := by
    intro a
    have := a.2
    simp only [S, Finset.mem_filter, Finset.mem_range] at this
    exact this
  let f : S → liarSubgroup n := fun a =>
    ⟨ZMod.unitOfCoprime (a : ℕ) (hS a).2.1, by
      rw [mem_liarSubgroup, jac_unitOfCoprime, ZMod.coe_unitOfCoprime]
      exact (hS a).2.2⟩
  apply Nat.card_congr
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b hab
    have h1 := congrArg (fun w : liarSubgroup n => ((w : (ZMod n)ˣ) : ZMod n).val) hab
    simp only [f, ZMod.coe_unitOfCoprime] at h1
    rw [ZMod.val_natCast_of_lt (hS a).1, ZMod.val_natCast_of_lt (hS b).1] at h1
    exact Subtype.ext h1
  · rintro ⟨u, hu⟩
    have hco : ((u : ZMod n).val).Coprime n := ZMod.val_coe_unit_coprime u
    have hu' : ZMod.unitOfCoprime (u : ZMod n).val hco = u := by
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, ZMod.natCast_zmod_val]
    have hmem : (u : ZMod n).val ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt _, hco, ?_⟩
      rw [mem_liarSubgroup, ← hu', jac_unitOfCoprime, ZMod.coe_unitOfCoprime] at hu
      exact hu
    refine ⟨⟨(u : ZMod n).val, hmem⟩, ?_⟩
    apply Subtype.ext
    exact hu'

/-- If the square of a unit is an Euler liar, the unit is a Fermat liar. -/
theorem pow_eq_one_of_sq_mem (n : ℕ) (hodd : Odd n) (u : (ZMod n)ˣ)
    (h : u * u ∈ liarSubgroup n) : u ^ (n - 1) = 1 := by
  rw [mem_liarSubgroup, jac_mul, jac_sq, Int.cast_one] at h
  have h2 : 2 * ((n - 1) / 2) = n - 1 := by
    obtain ⟨t, rfl⟩ := hodd
    omega
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, ← h2, pow_mul, pow_two, ← Units.val_mul, ← h]

/-- Euler liars are Fermat liars. -/
theorem pow_eq_one_of_mem (n : ℕ) (hodd : Odd n) (u : (ZMod n)ˣ)
    (h : u ∈ liarSubgroup n) : u ^ (n - 1) = 1 :=
  pow_eq_one_of_sq_mem n hodd u ((liarSubgroup n).mul_mem h h)

/-- Reading an identity of units modulo a divisor of `n`. -/
theorem cast_unit_pow {n d : ℕ} (hd : d ∣ n) (a : ℕ) (ha : a.Coprime n) (k : ℕ)
    (h : ZMod.unitOfCoprime a ha ^ k = 1) : (a : ZMod d) ^ k = 1 := by
  have h1 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h1
  have h2 := congrArg (ZMod.castHom hd (ZMod d)) h1
  rw [map_pow, map_natCast, map_one] at h2
  exact h2

/-- One direction of Korselt's criterion, for units. -/
theorem korselt_aux (n : ℕ) (hsq : Squarefree n) (hn1 : 1 < n)
    (h : ∀ q : ℕ, q.Prime → q ∣ n → (q - 1) ∣ (n - 1)) (u : (ZMod n)ˣ) : u ^ (n - 1) = 1 := by
  haveI : NeZero n := ⟨by omega⟩
  have hco : ((u : ZMod n).val).Coprime n := ZMod.val_coe_unit_coprime u
  have hpos : 1 ≤ (u : ZMod n).val ^ (n - 1) := by
    apply Nat.one_le_pow
    rcases Nat.eq_zero_or_pos (u : ZMod n).val with h0 | h0
    · rw [h0, Nat.coprime_zero_left] at hco
      omega
    · exact h0
  have hdvd : n ∣ (u : ZMod n).val ^ (n - 1) - 1 := by
    conv_lhs => rw [← Nat.prod_primeFactors_of_squarefree hsq]
    apply Finset.prod_primes_dvd
    · intro q hq
      exact (Nat.prime_of_mem_primeFactors hq).prime
    · intro q hq
      have hqp := Nat.prime_of_mem_primeFactors hq
      have hqn := Nat.dvd_of_mem_primeFactors hq
      haveI := Fact.mk hqp
      obtain ⟨t, ht⟩ := h q hqp hqn
      have ha0 : (((u : ZMod n).val : ℕ) : ZMod q) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro hd
        have := Nat.eq_one_of_dvd_coprimes hco hd hqn
        exact hqp.one_lt.ne' this
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpos, Nat.cast_pow, ht, pow_mul,
        ZMod.pow_card_sub_one_eq_one ha0, one_pow, Nat.cast_one, sub_self]
  have h0 : (((u : ZMod n).val ^ (n - 1) - 1 : ℕ) : ZMod n) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  rw [Nat.cast_sub hpos, Nat.cast_pow, ZMod.natCast_zmod_val, Nat.cast_one, sub_eq_zero] at h0
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact h0

theorem dvd_div_of_ne {n p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpn : p ∣ n) (hrn : r ∣ n)
    (hne : r ≠ p) : r ∣ n / p := by
  obtain ⟨m, rfl⟩ := hpn
  rw [Nat.mul_div_cancel_left m hp.pos]
  rcases (Nat.Prime.dvd_mul hr).mp hrn with h | h
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).mp h) hne
  · exact h

/-- A lift that is `1` modulo `n / p` is `1` modulo every other prime factor. -/
theorem cast_eq_one {n p r : ℕ} (hp : p.Prime) (hr : r.Prime) (hpn : p ∣ n) (hrn : r ∣ n)
    (hne : r ≠ p) (a : ℕ) (h1 : a ≡ 1 [MOD n / p]) : (a : ZMod r) = 1 := by
  have h2 : a ≡ 1 [MOD r] := h1.of_dvd (dvd_div_of_ne hp hr hpn hrn hne)
  have h3 := (ZMod.natCast_eq_natCast_iff a 1 r).mpr h2
  rw [Nat.cast_one] at h3
  exact h3

theorem neg_one_ne_one_of_odd_prime {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    (-1 : ZMod r) ≠ 1 := by
  haveI : Fact (2 < r) := ⟨by
    have := hr.two_le
    omega⟩
  exact ZMod.neg_one_ne_one

/-- The final piece of arithmetic. -/
theorem arith (p q : ℕ) (hp : 2 ≤ p) (hq : 2 ≤ q) (h1 : (p - 1) ∣ (p * q - 1))
    (h2 : (q - 1) ∣ 2 * (p * q - 1)) (h3 : ¬ (q - 1) ∣ (p * q - 1)) : q = 2 * p - 1 := by
  obtain ⟨s, rfl⟩ : ∃ s, p = s + 1 := ⟨p - 1, by omega⟩
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 1 := ⟨q - 1, by omega⟩
  have e : (s + 1) * (t + 1) - 1 = s * t + s + t := by
    have : (s + 1) * (t + 1) = s * t + s + t + 1 := by ring
    omega
  rw [e] at h1 h2 h3
  simp only [Nat.add_sub_cancel] at h1 h2 h3
  have hst : s ∣ t := by
    have h : s ∣ s * t + s := Dvd.dvd.add (dvd_mul_right s t) dvd_rfl
    exact (Nat.dvd_add_right h).mp h1
  obtain ⟨c, rfl⟩ := hst
  have hc : c ∣ 2 := by
    have h : s * c ∣ 2 * (s * (s * c)) + 2 * (s * c) :=
      Dvd.dvd.add ⟨2 * s, by ring⟩ ⟨2, by ring⟩
    have h' : s * c ∣ 2 * s := by
      have e2 : 2 * (s * (s * c) + s + s * c) = (2 * (s * (s * c)) + 2 * (s * c)) + 2 * s := by
        ring
      rw [e2] at h2
      exact (Nat.dvd_add_right h).mp h2
    have h'' : s * c ∣ s * 2 := by
      rw [mul_comm s 2]
      exact h'
    exact Nat.dvd_of_mul_dvd_mul_left (by omega) h''
  have hc2 : c ≤ 2 := Nat.le_of_dvd (by norm_num) hc
  interval_cases c
  · omega
  · exfalso
    apply h3
    rw [mul_one]
    exact Dvd.dvd.add (Dvd.dvd.add (dvd_mul_left s s) dvd_rfl) dvd_rfl
  · omega

theorem result : Claim := by
  intro n hodd hsq hn1 hnp
  haveI : NeZero n := ⟨by omega⟩
  have hcardG : Nat.card (ZMod n)ˣ = n.totient := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hcardE : numEulerLiars n = Nat.card (liarSubgroup n) := card_liars n
  have hidx : Nat.card (liarSubgroup n) * (liarSubgroup n).index = n.totient := by
    rw [(liarSubgroup n).card_mul_index, hcardG]
  have hEpos : 0 < Nat.card (liarSubgroup n) := Nat.card_pos
  -- Carmichael from "every unit is a Fermat liar"
  have hcar : (∀ u : (ZMod n)ˣ, u ^ (n - 1) = 1) → IsCarmichael n := by
    intro h
    refine ⟨hn1, hnp, fun a ha => ?_⟩
    have h1 := congrArg Units.val (h (ZMod.unitOfCoprime a ha))
    rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, Units.val_one] at h1
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, Nat.cast_one]
    exact h1
  constructor
  · -- index 2
    intro h2
    apply hcar
    intro u
    have hi : (liarSubgroup n).index = 2 := by
      rw [hcardE] at h2
      have : Nat.card (liarSubgroup n) * (liarSubgroup n).index = Nat.card (liarSubgroup n) * 2 := by
        rw [hidx, ← h2, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hEpos this
    have hmem := (liarSubgroup n).pow_index_mem u
    rw [hi, pow_two] at hmem
    exact pow_eq_one_of_sq_mem n hodd u hmem
  · -- index 4
    intro h4
    by_contra hcon
    rw [not_or] at hcon
    obtain ⟨hnc, hnsg⟩ := hcon
    have hi : (liarSubgroup n).index = 4 := by
      rw [hcardE] at h4
      have : Nat.card (liarSubgroup n) * (liarSubgroup n).index = Nat.card (liarSubgroup n) * 4 := by
        rw [hidx, ← h4, mul_comm]
      exact Nat.eq_of_mul_eq_mul_left hEpos this
    -- every unit satisfies u^(2(n-1)) = 1
    have hF1 : ∀ u : (ZMod n)ˣ, u ^ (2 * (n - 1)) = 1 := by
      intro u
      have hmem := (liarSubgroup n).pow_index_mem u
      rw [hi, show u ^ 4 = (u ^ 2) * (u ^ 2) by rw [← pow_add]] at hmem
      have := pow_eq_one_of_sq_mem n hodd (u ^ 2) hmem
      rw [← pow_mul] at this
      exact this
    -- a prime q with (q-1) ∤ (n-1)
    obtain ⟨q, hq, hqn, hq1⟩ : ∃ q : ℕ, q.Prime ∧ q ∣ n ∧ ¬ (q - 1) ∣ (n - 1) := by
      by_contra hall
      apply hnc
      apply hcar
      intro u
      apply korselt_aux n hsq hn1 _ u
      intro q hq hqn
      by_contra hd
      exact hall ⟨q, hq, hqn, hd⟩
    have hn2 : ¬ 2 ∣ n := by
      obtain ⟨t, rfl⟩ := hodd
      omega
    have hq2 : q ≠ 2 := by
      rintro rfl
      exact hn2 hqn
    haveI := Fact.mk hq
    obtain ⟨x, hx0, hxord, -⟩ := exists_gen q hq2
    obtain ⟨a, hax, ha1, haco⟩ := exists_lift n q hsq hq hqn x hx0
    -- the unit g and its properties
    have hgord : ∀ k : ℕ, ZMod.unitOfCoprime a haco ^ k = 1 → (q - 1) ∣ k := by
      intro k hk
      apply hxord
      rw [← hax]
      exact cast_unit_pow hqn a haco k hk
    have hq2n : (q - 1) ∣ 2 * (n - 1) := hgord _ (hF1 _)
    -- the Fermat liars K
    let K : Subgroup (ZMod n)ˣ := (powMonoidHom (n - 1) : (ZMod n)ˣ →* (ZMod n)ˣ).ker
    have hK : ∀ u : (ZMod n)ˣ, u ∈ K ↔ u ^ (n - 1) = 1 := by
      intro u
      simp only [K, MonoidHom.mem_ker, powMonoidHom_apply]
    have hEK : liarSubgroup n ≤ K := by
      intro u hu
      rw [hK]
      exact pow_eq_one_of_mem n hodd u hu
    have hgK : ZMod.unitOfCoprime a haco ∉ K := by
      rw [hK]
      intro h
      exact hq1 (hgord _ h)
    have hg2K : ZMod.unitOfCoprime a haco ^ 2 ∈ K := by
      rw [hK, ← pow_mul]
      exact hF1 _
    have hg2E : ZMod.unitOfCoprime a haco ^ 2 ∉ liarSubgroup n := by
      intro h
      rw [pow_two] at h
      exact hq1 (hgord _ (pow_eq_one_of_sq_mem n hodd _ h))
    have hrel := Subgroup.relIndex_mul_index hEK
    rw [hi] at hrel
    have hKi1 : K.index ≠ 1 := by
      intro h
      rw [Subgroup.index_eq_one] at h
      apply hgK
      rw [h]
      exact Subgroup.mem_top _
    have hrel1 : (liarSubgroup n).relIndex K ≠ 1 := by
      intro h
      rw [Subgroup.relIndex_eq_one] at h
      exact hg2E (h hg2K)
    have hKi : K.index = 2 ∧ (liarSubgroup n).relIndex K = 2 := by
      have hd : K.index ∣ 4 := ⟨(liarSubgroup n).relIndex K, by rw [← hrel, mul_comm]⟩
      have hle : K.index ≤ 4 := Nat.le_of_dvd (by norm_num) hd
      have hd' : (liarSubgroup n).relIndex K ∣ 4 := ⟨K.index, hrel.symm⟩
      have hle' : (liarSubgroup n).relIndex K ≤ 4 := Nat.le_of_dvd (by norm_num) hd'
      generalize K.index = i at *
      generalize (liarSubgroup n).relIndex K = j at *
      interval_cases i <;> interval_cases j <;> simp_all
    obtain ⟨hKi2, hrel2⟩ := hKi
    -- another prime factor
    obtain ⟨p, hp, hpn, hpq⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p ≠ q := by
      by_contra hall
      apply hnp
      have hpf : n.primeFactors = {q} := by
        ext r
        rw [Nat.mem_primeFactors, Finset.mem_singleton]
        constructor
        · rintro ⟨hr, hrn, -⟩
          by_contra hne
          exact hall ⟨r, hr, hrn, hne⟩
        · rintro rfl
          exact ⟨hq, hqn, by omega⟩
      have := Nat.prod_primeFactors_of_squarefree hsq
      rw [hpf, Finset.prod_singleton] at this
      rw [← this]
      exact hq
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact hn2 hpn
    haveI := Fact.mk hp
    obtain ⟨y, hy0, hyord, hyns⟩ := exists_gen p hp2
    obtain ⟨b, hby, hb1, hbco⟩ := exists_lift n p hsq hp hpn y hy0
    have hbq : (b : ZMod q) = 1 := cast_eq_one hp hq hpn hqn (Ne.symm hpq) b hb1
    -- h is a Fermat liar
    have hhK : ZMod.unitOfCoprime b hbco ∈ K := by
      by_contra hnK
      have hmem : ZMod.unitOfCoprime a haco * ZMod.unitOfCoprime b hbco ∈ K :=
        (Subgroup.mul_mem_iff_of_index_two hKi2).mpr (iff_of_false hgK hnK)
      rw [hK] at hmem
      have h1 := congrArg Units.val hmem
      rw [Units.val_pow_eq_pow_val, Units.val_mul, ZMod.coe_unitOfCoprime,
        ZMod.coe_unitOfCoprime, Units.val_one] at h1
      have h2 := congrArg (ZMod.castHom hqn (ZMod q)) h1
      rw [map_pow, map_mul, map_natCast, map_natCast, map_one, hbq, mul_one, hax] at h2
      exact hq1 (hxord _ h2)
    have hp1 : (p - 1) ∣ (n - 1) := by
      apply hyord
      rw [← hby]
      exact cast_unit_pow hpn b hbco (n - 1) ((hK _).mp hhK)
    -- the Jacobi symbol of h is -1, so h is not an Euler liar
    have hjb : jac n (ZMod.unitOfCoprime b hbco) = -1 := by
      rw [jac_unitOfCoprime]
      apply jacobi_lift n p hodd hp hpn b hb1
      rw [hby]
      exact hyns
    have hhE : ZMod.unitOfCoprime b hbco ∉ liarSubgroup n := by
      intro h
      rw [mem_liarSubgroup, hjb, ZMod.coe_unitOfCoprime] at h
      have h2 := congrArg (ZMod.castHom hqn (ZMod q)) h
      rw [map_intCast, map_pow, map_natCast, hbq, one_pow, Int.cast_neg, Int.cast_one] at h2
      exact neg_one_ne_one_of_odd_prime hq hq2 h2
    -- so h * g^2 is an Euler liar
    have hprod : ZMod.unitOfCoprime b hbco * ZMod.unitOfCoprime a haco ^ 2 ∈ liarSubgroup n := by
      have hsub : ((liarSubgroup n).subgroupOf K).index = 2 := hrel2
      have := (Subgroup.mul_mem_iff_of_index_two hsub
        (a := (⟨ZMod.unitOfCoprime b hbco, hhK⟩ : K))
        (b := (⟨ZMod.unitOfCoprime a haco ^ 2, hg2K⟩ : K))).mpr
        (iff_of_false (fun h => hhE (Subgroup.mem_subgroupOf.mp h))
          (fun h => hg2E (Subgroup.mem_subgroupOf.mp h)))
      exact Subgroup.mem_subgroupOf.mp this
    rw [mem_liarSubgroup, jac_mul, hjb, pow_two, jac_mul, jac_sq, mul_one,
      Units.val_mul, Units.val_mul, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime] at hprod
    -- no third prime
    have hpf : n.primeFactors = {p, q} := by
      ext r
      rw [Nat.mem_primeFactors, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hr, hrn, -⟩
        by_contra hne
        rw [not_or] at hne
        have hr2 : r ≠ 2 := by
          rintro rfl
          exact hn2 hrn
        have har : (a : ZMod r) = 1 := cast_eq_one hq hr hqn hrn hne.2 a ha1
        have hbr : (b : ZMod r) = 1 := cast_eq_one hp hr hpn hrn hne.1 b hb1
        have h2 := congrArg (ZMod.castHom hrn (ZMod r)) hprod
        rw [map_intCast, map_pow, map_mul, map_mul, map_natCast, map_natCast, har, hbr,
          mul_one, mul_one, one_pow, Int.cast_neg, Int.cast_one] at h2
        exact neg_one_ne_one_of_odd_prime hr hr2 h2
      · rintro (rfl | rfl)
        · exact ⟨hp, hpn, by omega⟩
        · exact ⟨hq, hqn, by omega⟩
    have hnpq : n = p * q := by
      have := Nat.prod_primeFactors_of_squarefree hsq
      rw [hpf, Finset.prod_pair hpq] at this
      exact this.symm
    apply hnsg
    refine ⟨p, q, hp, hq, ?_, hnpq⟩
    rw [hnpq] at hp1 hq2n hq1
    exact arith p q hp.two_le hq.two_le hp1 hq2n hq1
