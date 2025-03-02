import ClassificationOfSubgroups.Ch5_PropertiesOfSLOverAlgClosedField.S2_SpecialSubgroups
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_MaximalAbelianSubgroup
import Mathlib.GroupTheory.ClassEquation

set_option linter.style.longLine true
set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0


universe u


open Matrix MatrixGroups Subgroup MulAut MaximalAbelianSubgroup Pointwise SpecialSubgroups


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
instance noncenter_MaximalAbelianSubgroups_lift {F : Type*} [Field F] (G : Subgroup SL(2,F)) :
  Setoid (noncenter_MaximalAbelianSubgroups G) where
  r A B := ∃ (x : SL(2,F)), conj x • A.val = B.val
  iseqv := {
    refl A := ⟨1, by simp⟩
    symm := by
      rintro ⟨A, hA⟩  ⟨B, hB⟩ ⟨x, hx⟩
      use x⁻¹
      simp at hx ⊢
      rw [inv_smul_eq_iff]
      exact hx.symm
    trans := by
      rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ ⟨x, hx⟩ ⟨y, hy⟩
      use y * x
      rw [← hy, ← hx, smul_smul, MonoidHom.map_mul]
  }

/-
We define the equivalence relation on the set of Maximal Abelian Subgroups of `G`, a finite
group of `SL(2,F)`
-/
instance MaximalAbelianSubgroups_lift {F : Type*} [Field F] (G : Subgroup SL(2,F)) :
  Setoid (MaximalAbelianSubgroups G) where
  r A B := ∃ (x : SL(2,F)), conj x • A.val = B.val
  iseqv := {
    refl A := ⟨1, by simp⟩
    symm := by
      rintro ⟨A, hA⟩  ⟨B, hB⟩ ⟨x, hx⟩
      use x⁻¹
      simp at hx ⊢
      rw [inv_smul_eq_iff]
      exact hx.symm
    trans := by
      rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ ⟨x, hx⟩ ⟨y, hy⟩
      use y * x
      rw [← hy, ← hx, smul_smul, MonoidHom.map_mul]
  }

noncomputable def card_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : MaximalAbelianSubgroups G → ℕ :=
  fun A => Nat.card ((A.val.carrier \ (center SL(2,F)).carrier) :)


/-
The function which computes the cardinality of the noncentral part of a maximal abelian subgroup,
respects the equivalence relation on the setoid of maximal abelian subgroups of `G`.
-/
lemma card_eq_of_related_noncenter_subgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (center_le_G : center SL(2,F) ≤ G)[ hG : Finite G] :
  ∀ (A B : (MaximalAbelianSubgroups G)),
    A ≈ B → card_noncenter_MaximalAbelianSubgroupsOf G A =
      card_noncenter_MaximalAbelianSubgroupsOf G B:= by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ ArB
  simp only [noncenter_MaximalAbelianSubgroups_lift, ← Quotient.eq_iff_equiv, Quotient.eq] at ArB
  obtain ⟨x, rfl⟩ := ArB
  simp only [card_noncenter_MaximalAbelianSubgroupsOf, center_toSubmonoid,
    Submonoid.center_toSubsemigroup, pointwise_smul_toSubmonoid, Set.Nat.card_coe_set_eq]
  let center_finite : Finite (center SL(2, F)) := by
    rw [center_SL2_eq_Z]
    infer_instance
  have center_le_A : (Subsemigroup.center SL(2, F)).carrier ⊆ A.carrier :=
    @MaximalAbelianSubgroup.center_le SL(2,F) _ G A hA center_le_G
  let center_coe_finite : Finite (Subsemigroup.center SL(2, F)).carrier := center_finite
  have center_le_conj_A :
    (Subsemigroup.center SL(2, F)).carrier ⊆ (conj x • A.toSubmonoid).carrier := by
    intro z hz
    rw [Submonoid.mem_carrier, Submonoid.mem_pointwise_smul_iff_inv_smul_mem]
    have hz' := hz
    rw [Subsemigroup.mem_carrier, Subsemigroup.mem_center_iff] at hz'
    simp only [MulAut.smul_def, conj_inv_apply, mem_toSubmonoid]
    rw [hz' x⁻¹]
    group
    exact center_le_A hz
  rw [Set.ncard_diff center_le_A, Set.ncard_diff center_le_conj_A]
  have key : (conj x • A.toSubmonoid).carrier.ncard = A.carrier.ncard := by
    symm
    refine Set.ncard_congr (fun a ha ↦ x * a * x⁻¹) ?closure ?injective ?surjective
    case closure =>
      intro a ha
      simp only [Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
        Submonoid.mem_pointwise_smul_iff_inv_smul_mem,
        smul_mul', MulAut.smul_def, conj_inv_apply, inv_mul_cancel, one_mul, smul_inv',
        mem_toSubmonoid]
      group
      exact ha
    case injective =>
      intro a b ha hb hab
      simp only [mul_left_inj, mul_right_inj] at hab
      exact hab
    case surjective =>
      rintro b ⟨y, hy, rfl⟩
      use y, hy
      congr
  rw [key]

/-
We lift the function which computes the cardinality of the noncentral part of a maximal subgroup
-/
noncomputable def lift_card {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (center_le_G : center SL(2,F) ≤ G) [Finite G] :=
  @Quotient.lift _ _ (s := MaximalAbelianSubgroups_lift G)
    (f := card_noncenter_MaximalAbelianSubgroupsOf G)
    (card_eq_of_related_noncenter_subgroups G center_le_G)

def toConjClassOfSet {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : MaximalAbelianSubgroups G → Set (Set SL(2,F)) :=
  fun A => noncenter_ConjClassOfSet A

lemma toConjClassOfSet_eq_of_related_noncenter_subgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (center_le_G : center SL(2,F) ≤ G) [Finite G] :
  (∀ (A B : MaximalAbelianSubgroups G), A ≈ B → toConjClassOfSet G A = toConjClassOfSet G B) := by
  intro A B ArB
  obtain ⟨x, hx⟩ := ArB
  simp [toConjClassOfSet, noncenter_ConjClassOfSet]
  ext s
  constructor
  · rintro ⟨y, rfl⟩
    simp [← hx]
    use y * x⁻¹
    rw [@MonoidHom.map_mul]
    rw [@MulAction.mul_smul]
    rw [@smul_left_cancel_iff]
    rw [map_inv]
    rw [@inv_smul_eq_iff]
    sorry
  -- simp [← hx]
  · rintro ⟨y, rfl⟩
    simp [← hx]
    use y * x
    rw [@MonoidHom.map_mul]
    rw [@MulAction.mul_smul]
    rw [@smul_left_cancel_iff]
    sorry

def ConjClassOfSet_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (center_le_G : center SL(2,F) ≤ G) [Finite G] :=
  @Quotient.lift _ _ (s := MaximalAbelianSubgroups_lift G) (f := toConjClassOfSet G) (toConjClassOfSet_eq_of_related_noncenter_subgroups G center_le_G)

-- Show that image of ConjClassOfSet_lift is G \ Z

-- Setoid naturally partitions the set.

#check Quotient.lift


-- def lift_card {F : Type*} [Field F] (G : Subgroup SL(2,F)) :=
--   @Quotient.lift _ _ (s := noncenter_MaximalAbelianSubgroups_lift G) (f := Nat.card) (related_noncenter_subgroups_card_eq G)

#check ConjClasses
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
