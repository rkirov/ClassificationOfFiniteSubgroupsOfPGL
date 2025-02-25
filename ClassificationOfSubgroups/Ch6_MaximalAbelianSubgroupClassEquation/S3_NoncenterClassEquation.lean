import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_MaximalAbelianSubgroup
import Mathlib.GroupTheory.ClassEquation

set_option linter.style.longLine true
set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0


universe u


open Matrix MatrixGroups Subgroup MulAut MaximalAbelianSubgroup Pointwise


/- The non-central part of a subgroup -/
def Subgroup.noncenter {G : Type*} [Group G] (H : Subgroup G) : Set G :=
  {x : G | x ∈ H.carrier \ center G}

/- let M∗ be the set of all Aᵢ* and let Cᵢ* be the conjugacy class of Aᵢ* .-/
def noncenter_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F)) :=
  { noncenter (K : Subgroup SL(2,F)) | K ∈ MaximalAbelianSubgroups G }

#check noncenter_MaximalAbelianSubgroups


/-
Definition. The set $\mathcal{C}(A) = Cl(A) = \{x A x^{-1} \; | \; x ∈ G \}$
is called the conjugacy class of $A \in \mathcal{M}$.
-/
def ConjClassOfSet {G : Type*} [Group G] (A : Subgroup G) :=
  { conj x • A | x : G }

def noncenter_ConjClassOfSet {G : Type*} [Group G] (A : Subgroup G)  :=
  { conj x • noncenter A | x : G }

/-
Define the equivalence relation $\sim$ on $\mathcal{M}^*$ by
$A_i \sim A_j$ if and only if $A_i = x A_j x^{-1}$ for some $x \in G$.
 -/
instance {F : Type*} [Field F] {G : Subgroup SL(2,F)} :
  Setoid (noncenter_MaximalAbelianSubgroups G) where
  r Aᵢ Aⱼ := ∃ (x : SL(2,F)), conj x • Aᵢ.val = Aⱼ.val
  iseqv := {
    refl A := ⟨1, by simp⟩
    symm := by
      rintro ⟨Aᵢ, hAᵢ⟩  ⟨Aⱼ, hAⱼ⟩ ⟨x, hx⟩
      use x⁻¹
      simp at hx ⊢
      rw [inv_smul_eq_iff]
      exact hx.symm
    trans := by
      rintro ⟨Aᵢ, hAᵢ⟩ ⟨Aⱼ, hAⱼ⟩ ⟨Aₖ, hAₖ⟩ ⟨x, hx⟩ ⟨y, hy⟩
      use y * x
      rw [← hy, ← hx, smul_smul, MonoidHom.map_mul]
  }

#leansearch "conjugate subgroups."

/- Define $C (A)^* = \bicup_{x \in G} x A  x^{-1}$ -/
def noncenter_C {F : Type*} [Field F] (A G : Subgroup SL(2,F)) [Finite G] :=
  ⋃ x ∈ G, conj x • noncenter A

/- We have the relation $|C_i^*| = |A_i^*| |\mathcal{C}_i^*|$ -/
lemma card_noncenter_C_eq_card_A_mul_card_noncenter_ConjClass {F : Type*} [Field F]
  (G A : Subgroup SL(2,F)) [Finite G] :
  Nat.card (noncenter_C A G) =
    Nat.card (noncenter A) * Nat.card (noncenter_ConjClassOfSet A) := by sorry

/- $G \setminus Z(\textrm{SL}_2(F)) = \bigcup_{A \in \mathcal{M}} (C A)^*$ -/
lemma subgroup_sdiff_center_eq_union_noncenter_C {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] : G.carrier \ center (SL(2,F)) =
    ⋃ A ∈ MaximalAbelianSubgroups G, noncenter_C A G := by sorry

/- $|\mathcal{C}_i| = |C_i|$ -/
lemma card_noncenter_ConjClassOfSet_eq_card_ConjClassOfSet {G : Type*} [Group G] (A : Subgroup G) :
  Nat.card (ConjClassOfSet A) = Nat.card (noncenter_ConjClassOfSet A) := by sorry

/- $|\mathcal{C}_i| = [G : N_G(A_i)]$ -/
lemma card_ConjClassOfSet_eq_index_normalizer {F : Type*} [Field F] (A G : Subgroup SL(2,F)) :
  Nat.card (ConjClassOfSet A) = index (normalizer (A.subgroupOf G)) := by sorry

instance {L : Type*} [Group L] {G : Subgroup L} [Finite G] : Fintype (MaximalAbelianSubgroups G) := by sorry

-- |M| ≤ 2^|G|

-- |S ∩ Cᵢ| ≤ 1 for all Cᵢ ∈ noncentral_ConjClasses
-- #leansearch "subset of."

-- theorem card_noncenter_fin_subgroup_eq_sum_card_noncenter_mul_index_normalizer {F : Type*} [Field F] (G : Subgroup SL(2,F)) (S : Set (Subgroup SL(2,F))) (hS : S ⊆ MaximalAbelianSubgroups G)
--   (hS' : ∀ Cᵢ ∈ ConjClassOfSet G, Nat.card (Cᵢ.carrier ∩ S))[Fintype S] :
--   Nat.card (G.carrier \ (center SL(2,F)).carrier : Set SL(2,F)) = ∑ A ∈ S, Nat.card (noncenter A) * index (normalizer (A.subgroupOf G)) := by sorry

/- Lemma 2.5 N_G(A) = N_G(A*)-/
lemma normalizer_noncentral_eq {F : Type*} [Field F] (A G : Subgroup SL(2,F)) [Finite G] (hA : A ∈ MaximalAbelianSubgroups G) : normalizer A = setNormalizer (noncenter A) := by
  sorry

/- Lemma Let `Q` be a `p`-Sylow subgroup of `G` then $N_G(Q \sqcup Z) = N_G(Q)$-/
lemma normalizer_Sylow_join_center_eq_normalizer_Sylow {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)] [CharP F p] (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G) : normalizer (map G.subtype Q.toSubgroup ⊔ center SL(2,F)) = normalizer (map G.subtype Q.toSubgroup) := by
  sorry



#min_imports
