import Mathlib

/-!
Kettinger and Moles, "Elasticity of Orders from the S-relative Davenport Constant",
arXiv:2605.17595 (v2), the second conjecture after Corollary 2.15 (label "d in subgroups"):

  Let G be a finite abelian group and H1 < H2 <= G. For some g in G, we denote
  alpha = g + H1 and beta = g + H2; in particular, note that alpha is a proper subset of
  beta. Then d_beta(G) = d_{beta \ alpha}(G).

Here d_S(G), the small S-relative Davenport constant (Definition 2.4 of the paper), is the
largest n such that some sequence of n elements of G with sum in S has no zero-sum
subsequence, and 0 if there is no such sequence.

`Claim` says this fails already for the cyclic group of order 4, with H1 = {0, 2}, H2 = G
and g = 1: there beta = G and beta \ alpha = {0, 2}, and the two constants are 3 and 2.
-/

/-- A sequence over `G`, up to the order of its terms, is a multiset. It is zero-sum free
when no nonempty subsequence has sum zero. -/
def ZeroSumFree {G : Type} [AddCommGroup G] (T : Multiset G) : Prop :=
  ∀ U : Multiset G, U ≤ T → U ≠ 0 → U.sum ≠ 0

/-- The small `S`-relative Davenport constant `d_S(G)`: the largest length of a zero-sum
free sequence over `G` whose sum lies in `S` (and `0` if there is none; for a finite group
the lengths are bounded, so the supremum is a maximum). -/
noncomputable def smallDav {G : Type} [AddCommGroup G] (S : Set G) : ℕ :=
  sSup {n : ℕ | ∃ T : Multiset G, T.card = n ∧ T.sum ∈ S ∧ ZeroSumFree T}

/-- The coset `g + H`. -/
def coset {G : Type} [AddCommGroup G] (g : G) (H : AddSubgroup G) : Set G :=
  {x : G | x - g ∈ H}

/-- The conjecture as stated in the paper, for every `g`. -/
def PaperConjecture : Prop :=
  ∀ (G : Type) [AddCommGroup G] [Finite G] (H₁ H₂ : AddSubgroup G), H₁ < H₂ →
    ∀ g : G, smallDav (coset g H₂) = smallDav (coset g H₂ \ coset g H₁)

/-- The counterexample in `ZMod 4`, with the two values, and the failure of the conjecture. -/
def Claim : Prop :=
  AddSubgroup.zmultiples (2 : ZMod 4) < ⊤
    ∧ smallDav (coset (1 : ZMod 4) ⊤) = 3
    ∧ smallDav (coset (1 : ZMod 4) ⊤ \ coset 1 (AddSubgroup.zmultiples 2)) = 2
    ∧ ¬ PaperConjecture
