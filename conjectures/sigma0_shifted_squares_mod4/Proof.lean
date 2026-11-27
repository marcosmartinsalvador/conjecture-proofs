import conjectures.sigma0_shifted_squares_mod4.Statement

open Finset

/-- The size of a finite set has the same parity as the number of fixed points of
any involution of the set. -/
theorem card_fixed_modEq {α : Type*} [DecidableEq α] (s : Finset α) (g : α → α)
    (hmem : ∀ a ∈ s, g a ∈ s) (hinv : ∀ a ∈ s, g (g a) = a) :
    #s ≡ #(s.filter (fun a => g a = a)) [MOD 2] := by
  have h : ∑ x ∈ s.filter (fun a => ¬ g a = a), (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution (fun a _ => g a) ?_ ?_ ?_ ?_
    · intro a _; decide
    · intro a ha _; exact (Finset.mem_filter.mp ha).2
    · intro a ha
      rw [Finset.mem_filter] at ha ⊢
      refine ⟨hmem a ha.1, ?_⟩
      rw [hinv a ha.1]
      exact fun h => ha.2 h.symm
    · intro a ha; exact hinv a (Finset.mem_filter.mp ha).1
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, ZMod.natCast_eq_zero_iff] at h
  have h2 := Finset.card_filter_add_card_filter_not (s := s) (fun a => g a = a)
  unfold Nat.ModEq
  omega

/-! ### Zagier's set and its two involutions -/

/-- Zagier's set: positive triples `(x, y, z)` with `x * x + 4 * y * z = n`. -/
def zagSet (M n : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  (range M ×ˢ range M ×ˢ range M).filter
    (fun t => 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.1 * t.1 + 4 * t.2.1 * t.2.2 = n)

theorem mem_zagSet {M n : ℕ} (hM : n < M) (x y z : ℕ) :
    (x, y, z) ∈ zagSet M n ↔ 0 < x ∧ 0 < y ∧ 0 < z ∧ x * x + 4 * y * z = n := by
  unfold zagSet
  simp only [mem_filter, mem_product, mem_range]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨hx, hy, hz, h⟩
    refine ⟨⟨?_, ?_, ?_⟩, hx, hy, hz, h⟩ <;> nlinarith [Nat.mul_le_mul hx hx, Nat.mul_le_mul hy hz, Nat.mul_le_mul hx hx]

/-- Zagier's involution. -/
def zag (t : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  if t.1 + t.2.2 < t.2.1 then (t.1 + 2 * t.2.2, t.2.2, t.2.1 - t.1 - t.2.2)
  else if 2 * t.2.1 < t.1 then (t.1 - 2 * t.2.1, t.1 + t.2.2 - t.2.1, t.2.1)
  else (2 * t.2.1 - t.1, t.2.1, t.1 + t.2.2 - t.2.1)

theorem zag_mem {M n : ℕ} (hM : n < M) (hodd : n % 2 = 1) (hsq : ∀ x, x * x ≠ n)
    (t : ℕ × ℕ × ℕ) (ht : t ∈ zagSet M n) : zag t ∈ zagSet M n := by
  obtain ⟨x, y, z⟩ := t
  rw [mem_zagSet hM] at ht
  obtain ⟨hx, hy, hz, h⟩ := ht
  unfold zag
  dsimp only
  split_ifs with h1 h2
  · rw [mem_zagSet hM]
    refine ⟨by omega, hz, by omega, ?_⟩
    rw [← h, Nat.sub_sub]
    zify [h1.le]
    ring
  · rw [mem_zagSet hM]
    refine ⟨by omega, by omega, hy, ?_⟩
    rw [← h]
    zify [h2.le, show y ≤ x + z by omega]
    ring
  · have hne : x ≠ 2 * y := by
      rintro rfl
      have e : (2 * y) * (2 * y) + 4 * y * z = 2 * (2 * (y * y) + 2 * (y * z)) := by ring
      omega
    have hne2 : x + z ≠ y := by
      rintro rfl
      exact hsq (x + z + z) (by rw [← h]; ring)
    rw [mem_zagSet hM]
    refine ⟨by omega, hy, by omega, ?_⟩
    rw [← h]
    zify [show x ≤ 2 * y by omega, show y ≤ x + z by omega]
    ring

theorem zag_invol {M n : ℕ} (hM : n < M) (t : ℕ × ℕ × ℕ) (ht : t ∈ zagSet M n) :
    zag (zag t) = t := by
  obtain ⟨x, y, z⟩ := t
  rw [mem_zagSet hM] at ht
  obtain ⟨hx, hy, hz, -⟩ := ht
  simp only [zag]
  split_ifs <;> dsimp only at * <;> simp only [Prod.mk.injEq, and_true, true_and] <;> omega

theorem zag_fixed {M n : ℕ} (hM : n < M) (t : ℕ × ℕ × ℕ) (ht : t ∈ zagSet M n) :
    zag t = t ↔ t.1 = t.2.1 := by
  obtain ⟨x, y, z⟩ := t
  rw [mem_zagSet hM] at ht
  obtain ⟨hx, hy, hz, -⟩ := ht
  simp only [zag]
  split_ifs <;> simp only [Prod.mk.injEq, true_and] <;> omega

theorem mod4_eq_of_mul {a b : ℕ} (h : a * b % 4 = 1) : a % 4 = b % 4 := by
  have key : ∀ r, r < 4 → ∀ s, s < 4 → r * s % 4 = 1 → r = s := by decide
  rw [Nat.mul_mod] at h
  exact key _ (Nat.mod_lt _ (by norm_num)) _ (Nat.mod_lt _ (by norm_num)) h

/-- The fixed points of Zagier's involution correspond to the divisors below the
square root. -/
theorem card_zag_fixed {M n : ℕ} (hM : n < M) (h4 : n % 4 = 1) :
    #((zagSet M n).filter (fun t => t.1 = t.2.1))
      = #(n.divisors.filter (fun a => a * a < n)) := by
  apply Finset.card_nbij' (fun t => t.1) (fun a => (a, a, (n / a - a) / 4))
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter, mem_zagSet hM] at ht
    obtain ⟨⟨hx, hy, hz, h⟩, hxy⟩ := ht
    dsimp only at hxy
    subst hxy
    rw [mem_coe, mem_filter, Nat.mem_divisors]
    dsimp only
    refine ⟨⟨⟨x + 4 * z, by rw [← h]; ring⟩, by omega⟩, ?_⟩
    nlinarith [Nat.mul_pos hx hz]
  · intro a ha
    rw [mem_coe, mem_filter, Nat.mem_divisors] at ha
    obtain ⟨⟨⟨b, rfl⟩, hn⟩, hlt⟩ := ha
    have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
    have hab : a < b := lt_of_mul_lt_mul_left hlt (Nat.zero_le a)
    have hmod := mod4_eq_of_mul h4
    rw [mem_coe, mem_filter, mem_zagSet hM, Nat.mul_div_cancel_left b ha0]
    obtain ⟨c, hc⟩ : ∃ c, b = a + 4 * c := ⟨(b - a) / 4, by omega⟩
    subst hc
    have e : (a + 4 * c - a) / 4 = c := by omega
    rw [e]
    refine ⟨⟨ha0, ha0, by omega, by ring⟩, rfl⟩
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter, mem_zagSet hM] at ht
    obtain ⟨⟨hx, hy, hz, h⟩, hxy⟩ := ht
    dsimp only at hxy
    subst hxy
    dsimp only
    have e : n / x = x + 4 * z := by
      rw [← h, show x * x + 4 * x * z = x * (x + 4 * z) by ring, Nat.mul_div_cancel_left _ hx]
    rw [e]
    have e2 : (x + 4 * z - x) / 4 = z := by omega
    rw [e2]
  · intro a _
    rfl

/-- For a non-square, the divisors come in pairs, one below the square root. -/
theorem card_divisors_eq_two_mul {n : ℕ} (hsq : ∀ x, x * x ≠ n) :
    #n.divisors = 2 * #(n.divisors.filter (fun a => a * a < n)) := by
  have h := Finset.card_filter_add_card_filter_not (s := n.divisors) (fun a => a * a < n)
  have h2 : #(n.divisors.filter (fun a => ¬ a * a < n))
      = #(n.divisors.filter (fun a => a * a < n)) := by
    apply Finset.card_nbij' (fun a => n / a) (fun a => n / a)
    · intro a ha
      rw [mem_coe, mem_filter, Nat.mem_divisors] at ha ⊢
      obtain ⟨⟨⟨b, rfl⟩, hn⟩, hlt⟩ := ha
      have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      dsimp only
      rw [Nat.mul_div_cancel_left b ha0]
      refine ⟨⟨Dvd.intro_left a rfl, hn⟩, ?_⟩
      have hne : a ≠ b := by rintro rfl; exact hsq a rfl
      have hba : b < a := by
        by_contra hc
        have hab : a < b := by omega
        exact hlt (Nat.mul_lt_mul_of_pos_left hab ha0)
      exact Nat.mul_lt_mul_of_pos_right hba hb0
    · intro a ha
      rw [mem_coe, mem_filter, Nat.mem_divisors] at ha ⊢
      obtain ⟨⟨⟨b, rfl⟩, hn⟩, hlt⟩ := ha
      have ha0 : 0 < a := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hb0 : 0 < b := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      dsimp only
      rw [Nat.mul_div_cancel_left b ha0]
      refine ⟨⟨Dvd.intro_left a rfl, hn⟩, ?_⟩
      have hab : a < b := lt_of_mul_lt_mul_left hlt (Nat.zero_le a)
      have : a * b < b * b := Nat.mul_lt_mul_of_pos_right hab hb0
      omega
    · intro a ha
      rw [mem_coe, mem_filter, Nat.mem_divisors] at ha
      exact Nat.div_div_self ha.1.1 ha.1.2
    · intro a ha
      rw [mem_coe, mem_filter, Nat.mem_divisors] at ha
      exact Nat.div_div_self ha.1.1 ha.1.2
  omega

/-- Positive pairs `(x, y)` with `x * x + 4 * y * y = n`. -/
def rSet (M n : ℕ) : Finset (ℕ × ℕ) :=
  (range M ×ˢ range M).filter (fun p => 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.1 + 4 * (p.2 * p.2) = n)

/-- The fixed points of the swap `(x, y, z) ↦ (x, z, y)` on Zagier's set. -/
theorem card_swap_fixed {M n : ℕ} (hM : n < M) :
    #((zagSet M n).filter (fun t => (t.1, t.2.2, t.2.1) = t)) = #(rSet M n) := by
  apply Finset.card_nbij' (fun t => (t.1, t.2.1)) (fun p => (p.1, p.2, p.2))
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter, mem_zagSet hM] at ht
    obtain ⟨⟨hx, hy, hz, h⟩, hfix⟩ := ht
    simp only [Prod.mk.injEq, true_and] at hfix
    obtain ⟨rfl, -⟩ := hfix
    have hmem := (mem_zagSet hM x z z).2 ⟨hx, hy, hz, h⟩
    unfold zagSet at hmem
    simp only [mem_filter, mem_product, mem_range] at hmem
    unfold rSet
    simp only [mem_coe, mem_filter, mem_product, mem_range]
    exact ⟨⟨hmem.1.1, hmem.1.2.1⟩, hx, hy, by rw [← h]; ring⟩
  · rintro ⟨x, y⟩ hp
    unfold rSet at hp
    simp only [mem_coe, mem_filter, mem_product, mem_range] at hp
    rw [mem_coe, mem_filter, mem_zagSet hM]
    exact ⟨⟨hp.2.1, hp.2.2.1, hp.2.2.1, by rw [← hp.2.2.2]; ring⟩, rfl⟩
  · rintro ⟨x, y, z⟩ ht
    rw [mem_coe, mem_filter] at ht
    have hfix := ht.2
    simp only [Prod.mk.injEq, true_and] at hfix
    obtain ⟨rfl, -⟩ := hfix
    rfl
  · rintro ⟨x, y⟩ _
    rfl

/-- **Odd terms.** For a non-square `n ≡ 1 (mod 4)`, the number of divisors of `n` is,
modulo `4`, twice the number of ways to write `n = x² + 4y²` with `x, y > 0`.
This is Zagier's pair of involutions. -/
theorem card_divisors_modEq_of_one {M n : ℕ} (hM : n < M) (h4 : n % 4 = 1)
    (hsq : ∀ x, x * x ≠ n) : #n.divisors ≡ 2 * #(rSet M n) [MOD 4] := by
  have e1 := card_divisors_eq_two_mul hsq
  have e2 := card_zag_fixed hM h4
  have p1 := card_fixed_modEq (zagSet M n) zag (zag_mem hM (by omega) hsq) (zag_invol hM)
  have e3 : (zagSet M n).filter (fun t => zag t = t)
      = (zagSet M n).filter (fun t => t.1 = t.2.1) :=
    Finset.filter_congr (fun t ht => zag_fixed hM t ht)
  rw [e3, e2] at p1
  have p2 := card_fixed_modEq (zagSet M n) (fun t => (t.1, t.2.2, t.2.1))
    (by
      rintro ⟨x, y, z⟩ ht
      rw [mem_zagSet hM] at ht ⊢
      obtain ⟨hx, hy, hz, h⟩ := ht
      exact ⟨hx, hz, hy, by rw [← h]; ring⟩)
    (by rintro ⟨x, y, z⟩ _; rfl)
  rw [card_swap_fixed hM] at p2
  unfold Nat.ModEq at *
  omega

/-- The solutions `i` of `i * i = u`. -/
def sqSet (M u : ℕ) : Finset ℕ := (range M).filter (fun i => i * i = u)

/-- **Even terms.** For odd `u`, the number of divisors of `2 * u` is, modulo `4`,
twice the number of square roots of `u`. -/
theorem card_divisors_two_mul_modEq {M u : ℕ} (hM : u < M) (hodd : u % 2 = 1) :
    #(2 * u).divisors ≡ 2 * #(sqSet M u) [MOD 4] := by
  have hu0 : u ≠ 0 := by omega
  have hcop : Nat.Coprime 2 u := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)
  have e1 : #(2 * u).divisors = 2 * #u.divisors := by
    rw [Nat.Coprime.card_divisors_mul hcop, Nat.Prime.divisors Nat.prime_two]
    rfl
  have p1 := card_fixed_modEq u.divisors (fun d => u / d)
    (by
      intro d hd
      rw [Nat.mem_divisors] at hd ⊢
      exact ⟨Nat.div_dvd_of_dvd hd.1, hd.2⟩)
    (by
      intro d hd
      rw [Nat.mem_divisors] at hd
      exact Nat.div_div_self hd.1 hd.2)
  have e2 : u.divisors.filter (fun d => u / d = d) = sqSet M u := by
    ext i
    unfold sqSet
    simp only [mem_filter, Nat.mem_divisors, mem_range]
    constructor
    · rintro ⟨⟨hdvd, -⟩, hi⟩
      have h2 : u / i * i = u := Nat.div_mul_cancel hdvd
      rw [hi] at h2
      have hi0 : 0 < i := Nat.pos_of_ne_zero (by rintro rfl; omega)
      refine ⟨?_, h2⟩
      nlinarith
    · rintro ⟨-, hi⟩
      have hi0 : 0 < i := Nat.pos_of_ne_zero (by rintro rfl; omega)
      refine ⟨⟨⟨i, hi.symm⟩, hu0⟩, ?_⟩
      rw [← hi]
      exact Nat.mul_div_cancel i hi0
  rw [e2] at p1
  unfold Nat.ModEq at *
  omega

theorem mul_self_mod_four_of_odd {k : ℕ} (h : k % 2 = 1) : k * k % 4 = 1 := by
  have key : ∀ r, r < 4 → r % 2 = 1 → r * r % 4 = 1 := by decide
  rw [Nat.mul_mod]
  exact key _ (Nat.mod_lt _ (by norm_num)) (by omega)

theorem mul_self_mod_four_of_even {k : ℕ} (h : ¬ k % 2 = 1) : k * k % 4 = 0 := by
  have key : ∀ r, r < 4 → ¬ r % 2 = 1 → r * r % 4 = 0 := by decide
  rw [Nat.mul_mod]
  exact key _ (Nat.mod_lt _ (by norm_num)) (by omega)

/-- A sum of counts of solutions is the count of solutions in the product. -/
theorem sum_card_filter {β : Type*} (K : Finset ℕ) (A : Finset β) (P : ℕ → β → Prop)
    [∀ k b, Decidable (P k b)] :
    ∑ k ∈ K, #(A.filter (P k)) = #((K ×ˢ A).filter (fun q => P q.1 q.2)) := by
  simp only [Finset.card_filter, Finset.sum_product]

/-- **The general statement.** If `N ≡ 2 (mod 4)` and `N` is not a sum of two squares,
then `∑_{1 ≤ k, k² < N} σ₀(N - k²)` is divisible by `4`. -/
theorem general (N : ℕ) (h4 : N % 4 = 2) (hs : ∀ x y, x * x + y * y ≠ N) :
    4 ∣ ∑ k ∈ (range N).filter (fun k => 1 ≤ k ∧ k * k < N), #(N - k * k).divisors := by
  set K := (range N).filter (fun k => 1 ≤ k ∧ k * k < N) with hK
  set M := N + 1 with hMdef
  -- each term, modulo 4
  have step1 : ∀ k ∈ K, #(N - k * k).divisors % 4
      = (2 * (if k % 2 = 1 then #(rSet M (N - k * k)) else #(sqSet M ((N - k * k) / 2)))) % 4 := by
    intro k hk
    rw [hK, mem_filter, mem_range] at hk
    obtain ⟨hkN, hk1, hkk⟩ := hk
    split_ifs with hodd
    · have hm := mul_self_mod_four_of_odd hodd
      exact card_divisors_modEq_of_one (M := M) (by omega) (by omega)
        (fun x hx => hs k x (by omega))
    · have hm := mul_self_mod_four_of_even hodd
      have e : N - k * k = 2 * ((N - k * k) / 2) := by omega
      rw [e]
      have := card_divisors_two_mul_modEq (M := M) (u := (N - k * k) / 2) (by omega) (by omega)
      rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
      exact this
  -- so the sum is twice a sum of counts, modulo 4
  have step2 : (∑ k ∈ K, #(N - k * k).divisors) % 4
      = (2 * ∑ k ∈ K, (if k % 2 = 1 then #(rSet M (N - k * k))
          else #(sqSet M ((N - k * k) / 2)))) % 4 := by
    rw [Finset.sum_nat_mod, Finset.sum_congr rfl step1, ← Finset.sum_nat_mod, Finset.mul_sum]
  -- the two sums of counts are counts of solutions
  have step3 : ∑ k ∈ K, (if k % 2 = 1 then #(rSet M (N - k * k))
        else #(sqSet M ((N - k * k) / 2)))
      = #(((K.filter (fun k => k % 2 = 1)) ×ˢ (range M ×ˢ range M)).filter
            (fun q => 0 < q.2.1 ∧ 0 < q.2.2 ∧ q.2.1 * q.2.1 + 4 * (q.2.2 * q.2.2) = N - q.1 * q.1))
        + #(((K.filter (fun k => ¬ k % 2 = 1)) ×ˢ range M).filter
            (fun q => q.2 * q.2 = (N - q.1 * q.1) / 2)) := by
    rw [Finset.sum_ite]
    congr 1
    · exact sum_card_filter _ (range M ×ˢ range M)
        (fun k p => 0 < p.1 ∧ 0 < p.2 ∧ p.1 * p.1 + 4 * (p.2 * p.2) = N - k * k)
    · exact sum_card_filter _ (range M) (fun k i => i * i = (N - k * k) / 2)
  set W := ((K.filter (fun k => k % 2 = 1)) ×ˢ (range M ×ˢ range M)).filter
    (fun q => 0 < q.2.1 ∧ 0 < q.2.2 ∧ q.2.1 * q.2.1 + 4 * (q.2.2 * q.2.2) = N - q.1 * q.1)
    with hW
  set V := ((K.filter (fun k => ¬ k % 2 = 1)) ×ˢ range M).filter
    (fun q => q.2 * q.2 = (N - q.1 * q.1) / 2) with hV
  -- what it means to be in `W` and in `V`
  have memW : ∀ k x y, (k, x, y) ∈ W
      ↔ (k % 2 = 1 ∧ 0 < x ∧ 0 < y ∧ k * k + x * x + 4 * (y * y) = N) := by
    intro k x y
    rw [hW, hK]
    simp only [mem_filter, mem_product, mem_range]
    constructor
    · rintro ⟨⟨⟨⟨hkN, hk1, hkk⟩, hodd⟩, hxM, hyM⟩, hx, hy, h⟩
      exact ⟨hodd, hx, hy, by omega⟩
    · rintro ⟨hodd, hx, hy, h⟩
      have hxx : x ≤ x * x := Nat.le_mul_self x
      have hyy : y ≤ y * y := Nat.le_mul_self y
      have hkk : k ≤ k * k := Nat.le_mul_self k
      have hx1 : 0 < x * x := Nat.mul_pos hx hx
      exact ⟨⟨⟨⟨by omega, by omega, by omega⟩, hodd⟩, by omega, by omega⟩, hx, hy, by omega⟩
  have memV : ∀ k i, (k, i) ∈ V
      ↔ (¬ k % 2 = 1 ∧ 1 ≤ k ∧ k * k < N ∧ i * i = (N - k * k) / 2) := by
    intro k i
    rw [hV, hK]
    simp only [mem_filter, mem_product, mem_range]
    constructor
    · rintro ⟨⟨⟨⟨hkN, hk1, hkk⟩, hodd⟩, hiM⟩, h⟩
      exact ⟨hodd, hk1, hkk, h⟩
    · rintro ⟨hodd, hk1, hkk, h⟩
      have hkk' : k ≤ k * k := Nat.le_mul_self k
      have hii : i ≤ i * i := Nat.le_mul_self i
      exact ⟨⟨⟨⟨by omega, hk1, hkk⟩, hodd⟩, by omega⟩, h⟩
  -- swapping `k` and `x` is an involution of `W`
  have pW := card_fixed_modEq W (fun q => (q.2.1, q.1, q.2.2))
    (by
      rintro ⟨k, x, y⟩ hq
      dsimp only
      rw [memW] at hq ⊢
      obtain ⟨hodd, hx, hy, h⟩ := hq
      have hm := mul_self_mod_four_of_odd hodd
      have hxodd : x % 2 = 1 := by
        by_contra hc
        have := mul_self_mod_four_of_even hc
        omega
      exact ⟨hxodd, by omega, hy, by omega⟩)
    (by rintro ⟨k, x, y⟩ _; rfl)
  -- its fixed points are in bijection with `V`
  have eW : #(W.filter (fun q => (q.2.1, q.1, q.2.2) = q)) = #V := by
    apply Finset.card_nbij' (fun q => (2 * q.2.2, q.1)) (fun r => (r.2, r.2, r.1 / 2))
    · rintro ⟨k, x, y⟩ hq
      rw [mem_coe, mem_filter, memW] at hq
      obtain ⟨⟨hodd, hx, hy, h⟩, hfix⟩ := hq
      simp only [Prod.mk.injEq, and_true] at hfix
      obtain ⟨rfl, -⟩ := hfix
      dsimp only
      rw [mem_coe, memV]
      have e : 2 * y * (2 * y) = 4 * (y * y) := by ring
      have hx1 : 0 < x * x := Nat.mul_pos hx hx
      exact ⟨by omega, by omega, by omega, by omega⟩
    · rintro ⟨k, i⟩ hr
      rw [mem_coe, memV] at hr
      obtain ⟨heven, hk1, hkk, h⟩ := hr
      obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j := ⟨k / 2, by omega⟩
      have e : 2 * j * (2 * j) = 4 * (j * j) := by ring
      have hm := mul_self_mod_four_of_even heven
      have hiodd : i % 2 = 1 := by
        by_contra hc
        have := mul_self_mod_four_of_even hc
        omega
      rw [mem_coe, mem_filter, memW]
      have e2 : 2 * j / 2 = j := by omega
      dsimp only
      rw [e2]
      exact ⟨⟨hiodd, by omega, by omega, by omega⟩, rfl⟩
    · rintro ⟨k, x, y⟩ hq
      rw [mem_coe, mem_filter] at hq
      have hfix := hq.2
      simp only [Prod.mk.injEq, and_true] at hfix
      obtain ⟨rfl, -⟩ := hfix
      have e2 : 2 * y / 2 = y := by omega
      dsimp only
      rw [e2]
    · rintro ⟨k, i⟩ hr
      rw [mem_coe, memV] at hr
      have e2 : 2 * (k / 2) = k := by omega
      dsimp only
      rw [e2]
  rw [eW] at pW
  rw [step3] at step2
  unfold Nat.ModEq at pW
  omega

theorem mul_self_mod_eight (x : ℕ) : x * x % 8 = 0 ∨ x * x % 8 = 1 ∨ x * x % 8 = 4 := by
  have key : ∀ r, r < 8 → (r * r % 8 = 0 ∨ r * r % 8 = 1 ∨ r * r % 8 = 4) := by decide
  rw [Nat.mul_mod]
  exact key _ (Nat.mod_lt _ (by norm_num))

/-- The conjecture: the case `N = 16 n + 6`. -/
theorem result : Claim := by
  intro n
  have h := general (16 * n + 6) (by omega) (by
    intro x y
    have hx := mul_self_mod_eight x
    have hy := mul_self_mod_eight y
    omega)
  have e : ∀ k : ℕ, k ^ 2 = k * k := fun k => sq k
  simp only [e]
  exact (Nat.modEq_zero_iff_dvd).2 h
