import Mathlib

/-- `∑_{k=0}^n φ^k S`: the sum of the subgroups `S, φ S, ..., φ^n S` of an abelian
group, written out elementwise. It is the set of all `∑_{k=0}^n φ^k (s_k)` with every
`s_k` in `S`. -/
def sumIterates {G : Type} [AddCommGroup G] (φ : G →+ G) (S : AddSubgroup G) (n : ℕ) :
    Set G :=
  {g | ∃ s : ℕ → G, (∀ k, s k ∈ S) ∧ g = ∑ k ∈ Finset.range (n + 1), (⇑φ)^[k] (s k)}

/-- Definition 2.1 of M. Achigar, "Algebraic expansivity on abelian groups",
arXiv:2604.24556v1: an endomorphism `φ` of an abelian group `G` is *positively
expansive* if there is a finite subgroup `S ≤ G` (a positive generator) such that for
every finite subgroup `F ≤ G` there is `n ∈ ℕ` with `F ⊆ ∑_{k=0}^n φ^k S`. -/
def PositivelyExpansive {G : Type} [AddCommGroup G] (φ : G →+ G) : Prop :=
  ∃ S : AddSubgroup G, (S : Set G).Finite ∧
    ∀ F : AddSubgroup G, (F : Set G).Finite → ∃ n : ℕ, (F : Set G) ⊆ sumIterates φ S n

/-- The conjecture at the end of M. Achigar, "Algebraic expansivity on abelian groups",
arXiv:2604.24556v1:

"Let `φ : G → G` be an expansive endomorphism of a torsion group `G`. If `H ≤ G` is a
subgroup such that `φ H ⊆ H`, then the restriction `φ|_H : H → H` is also positively
expansive."

All groups in the paper are abelian. For an endomorphism the paper defines only
positive expansivity, so the hypothesis is read as "`φ` is positively expansive"
(see `source.md`). "Torsion" means every element has finite order. The restriction
`φ|_H` is the endomorphism `x ↦ φ x` of `H` (`φ` after the inclusion of `H`, with
values taken in `H`). -/
def Claim : Prop :=
  ∀ (G : Type) [AddCommGroup G] (φ : G →+ G) (H : AddSubgroup G)
    (hH : ∀ h ∈ H, φ h ∈ H),
    (∀ g : G, ∃ n : ℕ, 0 < n ∧ n • g = 0) →
    PositivelyExpansive φ →
    PositivelyExpansive ((φ.comp H.subtype).codRestrict H (fun x => hH x x.2))
