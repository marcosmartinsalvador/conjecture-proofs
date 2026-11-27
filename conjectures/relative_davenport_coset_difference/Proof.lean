import conjectures.relative_davenport_coset_difference.Statement

namespace DavProof

open Multiset

/-- The test subsequence with `i` ones, `j` twos and `k` threes. -/
def tst (i j k : ℕ) : Multiset (ZMod 4) :=
  replicate i 1 + replicate j 2 + replicate k 3

theorem tst_le {T : Multiset (ZMod 4)} {i j k : ℕ}
    (hi : i ≤ T.count 1) (hj : j ≤ T.count 2) (hk : k ≤ T.count 3) : tst i j k ≤ T := by
  rw [Multiset.le_iff_count]
  intro a
  simp only [tst, count_add, count_replicate]
  have h12 : (1 : ZMod 4) ≠ 2 := by decide
  have h13 : (1 : ZMod 4) ≠ 3 := by decide
  have h23 : (2 : ZMod 4) ≠ 3 := by decide
  by_cases h1 : 1 = a
  · subst h1; simp [h12.symm, h13.symm]; exact hi
  · by_cases h2 : 2 = a
    · subst h2; simp [h12, h23.symm]; exact hj
    · by_cases h3 : 3 = a
      · subst h3; simp [h13, h23]; exact hk
      · simp [h1, h2, h3]

theorem tst_sum (i j k : ℕ) : (tst i j k).sum = ((i + 2 * j + 3 * k : ℕ) : ZMod 4) := by
  simp [tst, sum_replicate]
  ring

theorem tst_ne_zero {i j k : ℕ} (h : 0 < i + j + k) : tst i j k ≠ 0 := by
  intro h0
  have := congrArg Multiset.card h0
  simp [tst] at this
  omega

theorem card_eq (T : Multiset (ZMod 4)) :
    T.card = T.count 0 + T.count 1 + T.count 2 + T.count 3 := by
  have h := Multiset.sum_count_eq_card (s := (Finset.univ : Finset (ZMod 4))) (m := T)
    (fun a _ => Finset.mem_univ a)
  rw [← h]
  exact Fin.sum_univ_four (fun a : Fin 4 => count (a : ZMod 4) T)

theorem sum_eq (T : Multiset (ZMod 4)) :
    T.sum = ((T.count 1 + 2 * T.count 2 + 3 * T.count 3 : ℕ) : ZMod 4) := by
  have h := Finset.sum_multiset_count_of_subset T (Finset.univ : Finset (ZMod 4))
    (Finset.subset_univ _)
  rw [h]
  have : (∑ i : ZMod 4, T.count i • i)
      = T.count 0 • (0 : ZMod 4) + T.count 1 • 1 + T.count 2 • 2 + T.count 3 • 3 :=
    Fin.sum_univ_four (fun a : Fin 4 => count (a : ZMod 4) T • (a : ZMod 4))
  rw [this]
  simp
  ring

/-- Every zero-sum free sequence over `ZMod 4` has at most three terms, and at most two if
its sum is `0` or `2`. -/
theorem key (T : Multiset (ZMod 4)) (hT : ZeroSumFree T) :
    T.card ≤ 3 ∧ (T.sum = 0 ∨ T.sum = 2 → T.card ≤ 2) := by
  have h0 : T.count 0 = 0 := by
    by_contra h
    have hle : ({0} : Multiset (ZMod 4)) ≤ T :=
      Multiset.singleton_le.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero h))
    exact hT {0} hle (by simp) (by simp)
  have use : ∀ i j k : ℕ, i ≤ T.count 1 → j ≤ T.count 2 → k ≤ T.count 3 → 0 < i + j + k →
      ((i + 2 * j + 3 * k : ℕ) : ZMod 4) ≠ 0 := by
    intro i j k hi hj hk hpos
    have := hT (tst i j k) (tst_le hi hj hk) (tst_ne_zero hpos)
    rwa [tst_sum] at this
  have h2 : T.count 2 ≤ 1 := by
    by_contra h
    exact use 0 2 0 (Nat.zero_le _) (by omega) (Nat.zero_le _) (by norm_num) (by decide)
  have h1 : T.count 1 ≤ 3 := by
    by_contra h
    exact use 4 0 0 (by omega) (Nat.zero_le _) (Nat.zero_le _) (by norm_num) (by decide)
  have h3 : T.count 3 ≤ 3 := by
    by_contra h
    exact use 0 0 4 (Nat.zero_le _) (Nat.zero_le _) (by omega) (by norm_num) (by decide)
  have h13 : T.count 1 = 0 ∨ T.count 3 = 0 := by
    by_contra h
    have h' := not_or.mp h
    exact use 1 0 1 (by omega) (Nat.zero_le _) (by omega) (by norm_num) (by decide)
  have h112 : 2 ≤ T.count 1 → T.count 2 = 0 := by
    intro h
    by_contra h'
    exact use 2 1 0 h (by omega) (Nat.zero_le _) (by norm_num) (by decide)
  have h332 : 2 ≤ T.count 3 → T.count 2 = 0 := by
    intro h
    by_contra h'
    exact use 0 1 2 (Nat.zero_le _) (by omega) h (by norm_num) (by decide)
  rw [card_eq, sum_eq, h0]
  generalize T.count 1 = a at *
  generalize T.count 2 = b at *
  generalize T.count 3 = c at *
  interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all <;> decide

theorem zsf_ones {n : ℕ} (hn : n ≤ 3) : ZeroSumFree (replicate n (1 : ZMod 4)) := by
  intro U hU hne
  obtain ⟨k, hk, rfl⟩ := Multiset.le_replicate_iff.mp hU
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hne rfl
  rw [sum_replicate]
  have hk3 : k ≤ 3 := le_trans hk hn
  interval_cases k <;> simp_all <;> decide

theorem bdd (S : Set (ZMod 4)) :
    BddAbove {n : ℕ | ∃ T : Multiset (ZMod 4), T.card = n ∧ T.sum ∈ S ∧ ZeroSumFree T} := by
  refine ⟨3, ?_⟩
  rintro n ⟨T, rfl, -, hT⟩
  exact (key T hT).1

theorem one_not_mem : (1 : ZMod 4) ∉ AddSubgroup.zmultiples (2 : ZMod 4) := by
  intro h
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp h
  have hall : ∀ c : ZMod 4, c * 2 ≠ 1 := by decide
  rw [zsmul_eq_mul] at hk
  exact hall _ hk

theorem zero_or_two {x : ZMod 4} (hx : x - 1 ∉ AddSubgroup.zmultiples (2 : ZMod 4)) :
    x = 0 ∨ x = 2 := by
  have hall : ∀ y : ZMod 4, y = 0 ∨ y = 1 ∨ y = 2 ∨ y = 3 := by decide
  rcases hall x with h | h | h | h
  · exact Or.inl h
  · exfalso
    apply hx
    rw [h, sub_self]
    exact AddSubgroup.zero_mem _
  · exact Or.inr h
  · exfalso
    apply hx
    have h31 : (3 : ZMod 4) - 1 = 2 := by decide
    rw [h, h31]
    exact AddSubgroup.mem_zmultiples 2

theorem lt_top' : AddSubgroup.zmultiples (2 : ZMod 4) < ⊤ :=
  lt_top_iff_ne_top.mpr (fun h => one_not_mem (h ▸ AddSubgroup.mem_top 1))

theorem dav_top : smallDav (coset (1 : ZMod 4) ⊤) = 3 := by
  have hmem : (3 : ℕ) ∈ {n : ℕ | ∃ T : Multiset (ZMod 4),
      T.card = n ∧ T.sum ∈ coset (1 : ZMod 4) ⊤ ∧ ZeroSumFree T} :=
    ⟨replicate 3 1, card_replicate 3 1, AddSubgroup.mem_top _, zsf_ones le_rfl⟩
  apply le_antisymm
  · apply csSup_le ⟨3, hmem⟩
    rintro n ⟨T, rfl, -, hT⟩
    exact (key T hT).1
  · exact le_csSup (bdd _) hmem

theorem dav_diff :
    smallDav (coset (1 : ZMod 4) ⊤ \ coset 1 (AddSubgroup.zmultiples 2)) = 2 := by
  have hsum : (replicate 2 (1 : ZMod 4)).sum - 1 = 1 := by
    rw [sum_replicate]
    decide
  have hmem : (2 : ℕ) ∈ {n : ℕ | ∃ T : Multiset (ZMod 4), T.card = n ∧
      T.sum ∈ coset (1 : ZMod 4) ⊤ \ coset 1 (AddSubgroup.zmultiples 2) ∧ ZeroSumFree T} := by
    refine ⟨replicate 2 1, card_replicate 2 1, ⟨AddSubgroup.mem_top _, ?_⟩,
      zsf_ones (by norm_num)⟩
    intro h
    have h' : (replicate 2 (1 : ZMod 4)).sum - 1 ∈ AddSubgroup.zmultiples (2 : ZMod 4) := h
    rw [hsum] at h'
    exact one_not_mem h'
  apply le_antisymm
  · apply csSup_le ⟨2, hmem⟩
    rintro n ⟨T, rfl, hS, hT⟩
    exact (key T hT).2 (zero_or_two hS.2)
  · exact le_csSup (bdd _) hmem

end DavProof

open DavProof in
theorem result : Claim := by
  refine ⟨lt_top', dav_top, dav_diff, ?_⟩
  intro h
  have h4 := h (ZMod 4) (AddSubgroup.zmultiples 2) ⊤ lt_top' 1
  rw [dav_top, dav_diff] at h4
  exact absurd h4 (by norm_num)
