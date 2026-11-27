import conjectures.expansive_restriction_torsion.Statement

open Polynomial Module

section

variable {G : Type} [AddCommGroup G]

theorem sumIterates_mono (φ : G →+ G) (S : AddSubgroup G) {m n : ℕ} (h : m ≤ n) :
    sumIterates φ S m ⊆ sumIterates φ S n := by
  rintro g ⟨s, hs, rfl⟩
  refine ⟨fun k => if k < m + 1 then s k else 0, fun k => ?_, ?_⟩
  · dsimp only
    split_ifs
    · exact hs k
    · exact S.zero_mem
  · rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : m + 1 ≤ n + 1))]
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      simp only [hk, ↓reduceIte]
    · intro k _ hk
      rw [Finset.mem_range] at hk
      simp only [hk, ↓reduceIte]
      exact iterate_map_zero φ k

/-- The union over `n` of the sets `∑_{k=0}^n φ^k S`, as a subgroup. -/
def reachSub (φ : G →+ G) (S : AddSubgroup G) : AddSubgroup G where
  carrier := {g | ∃ n, g ∈ sumIterates φ S n}
  zero_mem' := ⟨0, fun _ => 0, fun _ => S.zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨n, ha⟩ ⟨m, hb⟩
    obtain ⟨s, hs, rfl⟩ := sumIterates_mono φ S (le_max_left n m) ha
    obtain ⟨t, ht, rfl⟩ := sumIterates_mono φ S (le_max_right n m) hb
    refine ⟨max n m, fun k => s k + t k, fun k => S.add_mem (hs k) (ht k), ?_⟩
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => (iterate_map_add φ k _ _).symm
  neg_mem' := by
    rintro a ⟨n, s, hs, rfl⟩
    refine ⟨n, fun k => - s k, fun k => S.neg_mem (hs k), ?_⟩
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun k _ => (iterate_map_neg φ k _).symm

theorem mem_reachSub (φ : G →+ G) (S : AddSubgroup G) (g : G) :
    g ∈ reachSub φ S ↔ ∃ n, g ∈ sumIterates φ S n := Iff.rfl

theorem le_reachSub (φ : G →+ G) (S : AddSubgroup G) : S ≤ reachSub φ S := by
  intro g hg
  exact ⟨0, fun _ => g, fun _ => hg, by simp⟩

/-- Shift a sequence by one place, putting `0` first. -/
def shiftSeq (s : ℕ → G) : ℕ → G
  | 0 => 0
  | j + 1 => s j

theorem map_mem_reachSub (φ : G →+ G) (S : AddSubgroup G) (g : G) (hg : g ∈ reachSub φ S) :
    φ g ∈ reachSub φ S := by
  obtain ⟨n, s, hs, rfl⟩ := hg
  refine ⟨n + 1, shiftSeq s, fun k => ?_, ?_⟩
  · cases k with
    | zero => exact S.zero_mem
    | succ j => exact hs j
  · rw [map_sum]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [shiftSeq, Function.iterate_succ_apply', Function.iterate_zero, id_eq, add_zero]

end

section

variable {G : Type} [AddCommGroup G]

/-- Elements of `∑_{k=0}^n φ^k S` lie in the `ℤ[X]`-span of `S`, where `X` acts as `φ`. -/
theorem of_mem_span_of_mem_sumIterates (φ : G →+ G) (S : AddSubgroup G) (n : ℕ) (g : G)
    (hg : g ∈ sumIterates φ S n) :
    AEval'.of φ.toIntLinearMap g
      ∈ Submodule.span ℤ[X] (AEval'.of φ.toIntLinearMap '' (S : Set G)) := by
  obtain ⟨s, hs, rfl⟩ := hg
  rw [map_sum]
  refine Submodule.sum_mem _ fun k _ => ?_
  have e : AEval'.of φ.toIntLinearMap ((⇑φ)^[k] (s k))
      = (X ^ k : ℤ[X]) • AEval'.of φ.toIntLinearMap (s k) := by
    rw [AEval'.X_pow_smul_of]
    congr 1
    change _ = (φ.toIntLinearMap ^ k) (s k)
    rw [pow_apply_eq_iterate]
    rfl
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨s k, hs k, rfl⟩)

/-- Conversely, the `ℤ[X]`-span of a subgroup `S` only contains elements of the sets
`∑_{k=0}^n φ^k S`. -/
theorem exists_mem_sumIterates_of_mem_span (φ : G →+ G) (S : AddSubgroup G) (g : G)
    (hg : AEval'.of φ.toIntLinearMap g
      ∈ Submodule.span ℤ[X] (AEval'.of φ.toIntLinearMap '' (S : Set G))) :
    ∃ n, g ∈ sumIterates φ S n := by
  have hinv : (reachSub φ S).toIntSubmodule
      ∈ (Algebra.lsmul ℤ ℤ G φ.toIntLinearMap).invtSubmodule := by
    intro x hx
    exact map_mem_reachSub φ S x hx
  have hle : Submodule.span ℤ[X] (AEval'.of φ.toIntLinearMap '' (S : Set G))
      ≤ AEval.mapSubmodule ℤ G φ.toIntLinearMap ⟨(reachSub φ S).toIntSubmodule, hinv⟩ := by
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, AEval.mem_mapSubmodule_apply]
    exact le_reachSub φ S hx
  have := hle hg
  rw [AEval.mem_mapSubmodule_apply] at this
  exact this

end

/-- The restriction of `φ` to an invariant subgroup commutes with the inclusion, also
after iterating. -/
theorem coe_iterate_restrict {G : Type} [AddCommGroup G] (φ : G →+ G) (H : AddSubgroup G)
    (hH : ∀ h ∈ H, φ h ∈ H) (k : ℕ) (x : H) :
    (((⇑((φ.comp H.subtype).codRestrict H (fun x => hH x x.2)))^[k] x : H) : G)
      = (⇑φ)^[k] (x : G) := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

theorem result : Claim := by
  intro G _ φ H hH htor hexp
  obtain ⟨S, hSfin, hS⟩ := hexp
  -- every element of `G` lies in some `∑_{k=0}^n φ^k S`
  have h1 : ∀ g : G, ∃ n, g ∈ sumIterates φ S n := by
    intro g
    have hfo : IsOfFinAddOrder g := by
      obtain ⟨n, hn0, hn⟩ := htor g
      exact isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, hn0, hn⟩
    have hfin : ((AddSubgroup.zmultiples g : AddSubgroup G) : Set G).Finite := by
      have : Finite (AddSubgroup.zmultiples g) := finite_zmultiples.2 hfo
      exact Set.toFinite _
    obtain ⟨n, hn⟩ := hS _ hfin
    exact ⟨n, hn (AddSubgroup.mem_zmultiples g)⟩
  -- so `G` is a finitely generated `ℤ[X]`-module, `X` acting as `φ`
  have hfg : (⊤ : Submodule ℤ[X] (AEval' φ.toIntLinearMap)).FG := by
    refine ⟨(hSfin.image (AEval'.of φ.toIntLinearMap)).toFinset, ?_⟩
    rw [Set.Finite.coe_toFinset, eq_top_iff]
    intro m _
    obtain ⟨n, hn⟩ := h1 ((AEval'.of φ.toIntLinearMap).symm m)
    have := of_mem_span_of_mem_sumIterates φ S n _ hn
    rwa [LinearEquiv.apply_symm_apply] at this
  have hfin : Module.Finite ℤ[X] (AEval' φ.toIntLinearMap) := ⟨hfg⟩
  -- `ℤ[X]` is Noetherian, so the submodule `H` is finitely generated
  have hHinv : H.toIntSubmodule ∈ (Algebra.lsmul ℤ ℤ G φ.toIntLinearMap).invtSubmodule := by
    intro x hx
    exact hH x hx
  obtain ⟨T, hT⟩ := IsNoetherian.noetherian
    (AEval.mapSubmodule ℤ G φ.toIntLinearMap ⟨H.toIntSubmodule, hHinv⟩)
  -- the generators, as elements of `G`, and the subgroup `S₀` they generate
  set T₀ : Set G :=
    (AEval'.of φ.toIntLinearMap).symm '' (T : Set (AEval' φ.toIntLinearMap)) with hT₀
  have hT₀fin : T₀.Finite := T.finite_toSet.image _
  have hT₀H : T₀ ⊆ (H : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    have hmem : t ∈ AEval.mapSubmodule ℤ G φ.toIntLinearMap ⟨H.toIntSubmodule, hHinv⟩ := by
      rw [← hT]
      exact Submodule.subset_span ht
    rw [AEval.mem_mapSubmodule_apply] at hmem
    exact hmem
  set S₀ : AddSubgroup G := (Submodule.span ℤ T₀).toAddSubgroup with hS₀
  have hS₀H : S₀ ≤ H := by
    intro x hx
    have hle : Submodule.span ℤ T₀ ≤ H.toIntSubmodule := Submodule.span_le.2 hT₀H
    exact hle hx
  -- `S₀` is finite: a finitely generated torsion abelian group is finite
  have hS₀fin : (S₀ : Set G).Finite := by
    have i1 : Module.Finite ℤ (Submodule.span ℤ T₀) := Module.Finite.span_of_finite ℤ hT₀fin
    have i2 : Module.IsTorsion ℤ (Submodule.span ℤ T₀) := by
      intro x
      obtain ⟨n, hn0, hn⟩ := htor (x : G)
      refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn0.ne')⟩, ?_⟩
      apply Subtype.ext
      change ((n : ℤ) • (x : G)) = 0
      rw [natCast_zsmul]
      exact hn
    have i3 : Finite (Submodule.span ℤ T₀) := Module.finite_of_fg_torsion _ i2
    rw [← Set.finite_coe_iff]
    exact i3
  -- every element of `H` lies in some `∑_{k=0}^n φ^k S₀`
  have h2 : ∀ h ∈ H, ∃ n, h ∈ sumIterates φ S₀ n := by
    intro h hh
    apply exists_mem_sumIterates_of_mem_span
    have hmem : AEval'.of φ.toIntLinearMap h
        ∈ AEval.mapSubmodule ℤ G φ.toIntLinearMap ⟨H.toIntSubmodule, hHinv⟩ := by
      rw [AEval.mem_mapSubmodule_apply, LinearEquiv.symm_apply_apply]
      exact hh
    rw [← hT] at hmem
    refine Submodule.span_mono ?_ hmem
    intro t ht
    exact ⟨(AEval'.of φ.toIntLinearMap).symm t, Submodule.subset_span ⟨t, ht, rfl⟩,
      LinearEquiv.apply_symm_apply _ t⟩
  -- `S₀`, seen inside `H`, is a positive generator for the restriction
  refine ⟨S₀.addSubgroupOf H, ?_, ?_⟩
  · have e : (S₀.addSubgroupOf H : Set H) = (H.subtype) ⁻¹' (S₀ : Set G) := rfl
    rw [e]
    exact hS₀fin.preimage (Subtype.val_injective.injOn)
  · intro F hF
    have h3 : ∀ f : H, ∃ n, (f : G) ∈ sumIterates φ S₀ n := fun f => h2 f f.2
    choose N hN using h3
    refine ⟨hF.toFinset.sup N, ?_⟩
    intro f hf
    have hle : N f ≤ hF.toFinset.sup N := Finset.le_sup (hF.mem_toFinset.2 hf)
    obtain ⟨s, hs, hsum⟩ := sumIterates_mono φ S₀ hle (hN f)
    refine ⟨fun k => ⟨s k, hS₀H (hs k)⟩, fun k => ?_, ?_⟩
    · exact AddSubgroup.mem_addSubgroupOf.2 (hs k)
    · apply Subtype.ext
      rw [hsum]
      have e := map_sum H.subtype
        (fun k => (⇑((φ.comp H.subtype).codRestrict H (fun x => hH x x.2)))^[k]
          (⟨s k, hS₀H (hs k)⟩ : H))
        (Finset.range (hF.toFinset.sup N + 1))
      refine Eq.trans ?_ e.symm
      refine Finset.sum_congr rfl fun k _ => ?_
      exact (coe_iterate_restrict φ H hH k ⟨s k, hS₀H (hs k)⟩).symm
