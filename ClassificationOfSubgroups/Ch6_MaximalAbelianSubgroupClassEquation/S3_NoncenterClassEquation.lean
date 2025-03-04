import ClassificationOfSubgroups.Ch5_PropertiesOfSLOverAlgClosedField.S2_SpecialSubgroups
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_MaximalAbelianSubgroup
import Mathlib.GroupTheory.ClassEquation
import Mathlib

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
  { noncenter (K : Subgroup SL(2,F)) | K ∈ MaximalAbelianSubgroupsOf G }

#check noncenter_MaximalAbelianSubgroups


/-
Definition. The set $\mathcal{C}(A) = Cl(A) = \{x A x^{-1} \; | \; x ∈ G \}$
is called the conjugacy class of $A \in \mathcal{M}$.
-/
def ConjClassOfSet {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G)  :=
  { conj x • A.val | x ∈ G }



def noncenter_ConjClassOfSet {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G)  :=
  { conj x • noncenter A.val | x ∈ G }


noncomputable def card_noncenter_ConjClassOfSet {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) : MaximalAbelianSubgroupsOf G → ℕ :=
  fun A => Nat.card (noncenter_ConjClassOfSet G A)

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
instance lift_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F)) :
  Setoid (MaximalAbelianSubgroupsOf G) where
  r A B := ∃ x ∈ G, conj x • A.val = B.val
  iseqv := {
    refl A := ⟨1, Subgroup.one_mem _ , by simp⟩
    symm := by
      rintro ⟨A, hA⟩  ⟨B, hB⟩ ⟨x, hx⟩
      use x⁻¹
      simp at hx ⊢
      rw [inv_smul_eq_iff]
      exact ⟨hx.left, hx.right.symm⟩
    trans := by
      rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ ⟨x, hx⟩ ⟨y, hy⟩
      use y * x
      split_ands
      apply Subgroup.mul_mem G hy.left hx.left
      rw [← hy.right, ← hx.right, smul_smul, MonoidHom.map_mul]
  }

noncomputable def card_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : MaximalAbelianSubgroupsOf G → ℕ :=
  fun A => Nat.card ((A.val.carrier \ (center SL(2,F)).carrier) :)

/-
The function which computes the cardinality of the noncentral part of a maximal abelian subgroup,
respects the equivalence relation on the setoid of maximal abelian subgroups of `G`.
-/
lemma card_eq_of_related_noncenter_subgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (center_le_G : center SL(2,F) ≤ G)[ hG : Finite G] :
  ∀ (A B : (MaximalAbelianSubgroupsOf G)),
    A ≈ B → card_noncenter_MaximalAbelianSubgroupsOf G A =
      card_noncenter_MaximalAbelianSubgroupsOf G B := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨x, x_in_G, rfl⟩
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
noncomputable def lift_card_noncenter {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (center_le_G : center SL(2,F) ≤ G) [Finite G] :=
  @Quotient.lift _ _ (s := lift_MaximalAbelianSubgroupsOf G)
    (f := card_noncenter_MaximalAbelianSubgroupsOf G)
    (card_eq_of_related_noncenter_subgroups G center_le_G)


def toConjClassOfSet {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : MaximalAbelianSubgroupsOf G → Set (Set SL(2,F)) :=
  fun A => noncenter_ConjClassOfSet G A

lemma conj_noncenter_eq_noncenter_conj {F : Type*} [Field F] {G :Subgroup SL(2,F)}
  (A : MaximalAbelianSubgroupsOf G) (x : SL(2,F)) :
  (conj x • A.val).noncenter = conj x • A.val.noncenter := by
  ext y
  constructor
  · rintro ⟨⟨a, a_in_A, rfl⟩, conj_a_not_in_center⟩
    simp at conj_a_not_in_center ⊢
    simp only [Set.mem_smul_set_iff_inv_smul_mem, smul_mul', MulAut.smul_def, conj_inv_apply,
      inv_mul_cancel, one_mul, smul_inv']
    group
    have a_not_in_center : a ∉ center SL(2,F) := by
      intro a_in_center
      rw [mem_center_iff] at a_in_center
      have contr : x * a * x⁻¹ ∈ center SL(2,F) := by
        rw [mem_center_iff]
        rw [a_in_center x]
        group
        exact a_in_center
      contradiction
    exact ⟨a_in_A, a_not_in_center⟩
  · rintro ⟨a, ⟨a_in_A, a_not_in_center⟩, rfl⟩
    simp
    rw [noncenter, Set.mem_setOf, Set.mem_diff]
    split_ands
    · simp only [pointwise_smul_toSubmonoid, Subsemigroup.mem_carrier,
      Submonoid.mem_toSubsemigroup, Submonoid.mem_pointwise_smul_iff_inv_smul_mem, smul_mul',
      MulAut.smul_def, conj_inv_apply, inv_mul_cancel, one_mul, smul_inv', mem_toSubmonoid]
      group
      exact a_in_A
    · intro conj_in_center
      rw [SetLike.mem_coe, mem_center_iff] at conj_in_center
      have a_in_center : a ∈ center SL(2,F) := by
        rw [mem_center_iff]
        intro g
        specialize conj_in_center (x * g * x⁻¹)
        group at conj_in_center
        rw [mul_left_inj, mul_assoc, mul_assoc, mul_right_inj] at conj_in_center
        exact conj_in_center
      contradiction

lemma toConjClassOfSet_eq_of_related_noncenter_subgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :
  (∀ (A B : MaximalAbelianSubgroupsOf G), A ≈ B → toConjClassOfSet G A = toConjClassOfSet G B) := by
  intro A B ArB
  obtain ⟨x, x_in_G, hx⟩ := ArB
  simp [toConjClassOfSet, noncenter_ConjClassOfSet]
  ext s
  constructor
  · rintro ⟨y, y_in_G, rfl⟩
    simp only [← hx, Set.mem_setOf_eq]
    use y * x⁻¹
    rw [MonoidHom.map_mul, MulAction.mul_smul, smul_left_cancel_iff, map_inv, inv_smul_eq_iff]
    exact ⟨Subgroup.mul_mem G y_in_G (inv_mem x_in_G), conj_noncenter_eq_noncenter_conj A x⟩
  · rintro ⟨y, y_in_G, rfl⟩
    simp only [← hx, Set.mem_setOf_eq]
    use y * x
    rw [MonoidHom.map_mul, MulAction.mul_smul, smul_left_cancel_iff]
    exact ⟨Subgroup.mul_mem G y_in_G x_in_G, (conj_noncenter_eq_noncenter_conj A x).symm⟩


def ConjClassOfSet_lift {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :=
  @Quotient.lift _ _ (s := lift_MaximalAbelianSubgroupsOf G) (f := toConjClassOfSet G)
    (toConjClassOfSet_eq_of_related_noncenter_subgroups G)





open Function

lemma Injective_subroup_to_subset {L : Type*} [Group L] (G : Subgroup L) [Finite G] :
  Injective
    (fun (H : {K | (K : Subgroup L) ≤ G}) =>
      (⟨H.val.carrier, H.property⟩ : {K | K ⊆ G.carrier})) := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ hAB
  simp at hAB ⊢
  refine toSubmonoid_inj.mp ?_
  ext x
  exact Eq.to_iff (congrFun hAB x)


def subsets_MaximalAbelianSubgroups {L : Type*} [Group L] (G : Subgroup L) :=
  { (K : Set L) | K ∈ MaximalAbelianSubgroupsOf G }

instance finite_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Set.Finite (MaximalAbelianSubgroupsOf G) := by
  apply Set.Finite.subset (s := {K | (K : Subgroup SL(2,F)) ≤ G})
  · apply @Finite.of_injective _ _ ?set_finite _ (Injective_subroup_to_subset G)
    exact Set.Finite.finite_subsets hG
  · intro M hM
    exact hM.right

instance finite_MaximalAbelianSubgroups' {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Finite (MaximalAbelianSubgroupsOf G) :=
    Set.finite_coe_iff.mpr <| finite_MaximalAbelianSubgroups G

instance finite_MaximalAbelianSubgroups_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Finite (Quotient (lift_MaximalAbelianSubgroupsOf G)) := Quotient.finite _

noncomputable instance fintype_MaximalAbelianSubgroups_lift {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [hG : Finite G] :
  Fintype (Quotient (lift_MaximalAbelianSubgroupsOf G)) := by
  apply fintypeOfNotInfinite
  rw [not_infinite_iff_finite]
  exact finite_MaximalAbelianSubgroups_lift G

lemma mem_subsets_MaximalAbelianSubgroups {F : Type*} [Field F] {G : Subgroup SL(2,F)}
  (A : MaximalAbelianSubgroupsOf G) : A.val.carrier ∈ subsets_MaximalAbelianSubgroups G := by
  simp only [subsets_MaximalAbelianSubgroups, Set.mem_setOf_eq];
  use A.val
  simp only [Subtype.coe_prop, true_and]
  congr

noncomputable def finset_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :=
  (@Set.Finite.toFinset _ (s := MaximalAbelianSubgroupsOf G) )
  (h := finite_MaximalAbelianSubgroups G)

/-
Now we do the same but for MaximalAbelianSubgroups being a Set (Set SL(2,F))
-/
lemma Surjective_MaxAbSub_to_subsets_MaxAbSub {F : Type*} [Field F] (G : Subgroup SL(2,F)) :
  Surjective
    (fun (A : MaximalAbelianSubgroupsOf G) =>
      (⟨A.val.carrier, mem_subsets_MaximalAbelianSubgroups A⟩ :
        subsets_MaximalAbelianSubgroups G)) := by
    rintro ⟨A, ⟨M, hM₁, hM₂⟩⟩
    use ⟨M, hM₁⟩
    exact SetCoe.ext hM₂

lemma finite_subsets_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [ hG : Finite G] : Set.Finite (subsets_MaximalAbelianSubgroups G) := by
  let inst₀ : Set.Finite (MaximalAbelianSubgroupsOf G) := finite_MaximalAbelianSubgroups G
  let inst₁:  Finite ↑(MaximalAbelianSubgroupsOf G) := inst₀
  exact @Finite.of_surjective
    (α := (MaximalAbelianSubgroupsOf G)) _ _ _ (Surjective_MaxAbSub_to_subsets_MaxAbSub G)

noncomputable def finset_subsets_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [hG : Finite G] := @Set.Finite.toFinset _
    (s := subsets_MaximalAbelianSubgroups G) (h := finite_subsets_MaximalAbelianSubgroups G)



/-
Define the equivalence relation $\sim$ on $\mathcal{M}^*$ by
$A_i \sim A_j$ if and only if $A_i = x A_j x^{-1}$ for some $x \in G$.
 -/
instance finset_subsets_MaximalAbelianSubgroups_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] :  Setoid (finset_subsets_MaximalAbelianSubgroups G) where
  r A B := ∃ (x : SL(2,F)), conj x • A.val = B.val
  iseqv := {
    refl A := ⟨1, by simp⟩
    symm := by
      rintro A B ⟨x, hx⟩
      use x⁻¹
      simp at hx ⊢
      rw [inv_smul_eq_iff]
      exact hx.symm
    trans := by
      rintro A B C ⟨x, hx⟩ ⟨y, hy⟩
      use y * x
      rw [← hy, ← hx, smul_smul, MonoidHom.map_mul]
  }

open Setoid


def isPartition_MaximalAbelianSubgroups_lift {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :=
  isPartition_classes (finset_subsets_MaximalAbelianSubgroups_lift G)


noncomputable def finpartition_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] := @Setoid.IsPartition.finpartition SL(2,F)
    (c := finset_subsets_MaximalAbelianSubgroups G)
    --(hc := isPartition_classes (finset_subsets_MaximalAbelianSubgroups_lift G))

/-
Define $C(A) = \bigcup_{x \in G} xA x^{-1}$
-/
def C {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G]
  (A : MaximalAbelianSubgroupsOf G) := ⋃ x ∈ G, conj x • A.val.carrier

/-
Define $C (A)^* = \bicup_{x \in G} x A  x^{-1}$
-/
def noncenter_C {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G]
  (A : MaximalAbelianSubgroupsOf G) :=  ⋃ x ∈ G, conj x • noncenter A.val

/-
We compute the cardinality of the noncenter conjugacy class
-/
noncomputable def card_noncenter_C {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :
 (MaximalAbelianSubgroupsOf G) → ℕ := fun A => Nat.card (noncenter_C G A)

lemma card_noncenter_C_eq_noncenter_MaximalAbelianSubgroup_mul_noncenter_ConjClassOfSet
  {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] (A : MaximalAbelianSubgroupsOf G) :
  card_noncenter_C G A =
    card_noncenter_MaximalAbelianSubgroupsOf G A * card_noncenter_ConjClassOfSet G A  := sorry


lemma card_noncenter_C_eq_of_related {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :
  ∀ (a b : MaximalAbelianSubgroupsOf G), a ≈ b → card_noncenter_C G a = card_noncenter_C G b := by
  rintro A B ⟨y, y_in_G, conj_y_A_eq_B⟩
  simp [card_noncenter_C, noncenter_C]
  simp_rw [← conj_y_A_eq_B]
  congr
  ext a; constructor
  · rintro ⟨C, ⟨c, hc⟩, a_in_C⟩
    simp only [Set.Subset.antisymm_iff, Set.iUnion_subset_iff] at hc
    obtain ⟨conj_A_subs_C, C_subs_conj_A⟩ := hc
    have a_in_union := C_subs_conj_A a_in_C
    rw [Set.mem_iUnion] at a_in_union
    obtain ⟨c_in_G, a_in_conj_noncenter⟩ := a_in_union
    rw [Set.mem_iUnion₂]
    use c * y⁻¹, Subgroup.mul_mem G c_in_G (inv_mem y_in_G)
    simp [conj_noncenter_eq_noncenter_conj, Set.mem_smul_set]
    simp [Set.mem_smul_set] at a_in_conj_noncenter
    group at a_in_conj_noncenter ⊢
    exact a_in_conj_noncenter
  · rintro hc
    simp [Set.mem_iUnion] at hc ⊢
    obtain ⟨c, c_in_G, hc⟩ := hc
    use c * y, Subgroup.mul_mem G c_in_G y_in_G
    simp_rw [conj_noncenter_eq_noncenter_conj] at hc
    rw [_root_.map_mul, MulAction.mul_smul]
    exact hc

noncomputable def lift_card_noncenter_C {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :=
  @Quotient.lift _ _ (s := lift_MaximalAbelianSubgroupsOf G)
  (f := card_noncenter_C G) (card_noncenter_C_eq_of_related G)

/-
We have the relation $|C_i^*| = |A_i^*| |\mathcal{C}_i^*|$
-/
lemma card_noncenter_C_eq_card_A_mul_card_noncenter_ConjClass {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G]  (A : MaximalAbelianSubgroupsOf G) :
  Nat.card (noncenter_C G A) =
    Nat.card (noncenter A.val) * card_noncenter_ConjClassOfSet G A := by sorry

/- $G \setminus Z(\textrm{SL}_2(F)) = \bigcup_{A \in \mathcal{M}} (C A)^*$ -/
lemma subgroup_sdiff_center_eq_union_noncenter_C {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] : G.carrier \ center (SL(2,F)) =
    ⋃ A : MaximalAbelianSubgroupsOf G, noncenter_C G A := by sorry

/- $|\mathcal{C}_i| = |C_i|$ -/
lemma card_noncenter_ConjClassOfSet_eq_card_ConjClassOfSet {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) :
  Nat.card (ConjClassOfSet G A) = card_noncenter_ConjClassOfSet G A := by sorry

/- $|\mathcal{C}_i| = [G : N_G(A_i)]$ -/
lemma card_ConjClassOfSet_eq_index_normalizer {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) :
  Nat.card (ConjClassOfSet G A) = index (normalizer (A.val.subgroupOf G)) := by sorry

noncomputable instance {F : Type*} [Field F] {G : Subgroup SL(2,F)} [Finite G] :
  Fintype (Quotient (lift_MaximalAbelianSubgroupsOf G)) := by infer_instance

theorem card_noncenter_fin_subgroup_eq_sum_card_noncenter_mul_index_normalizer {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G) :
  Nat.card (G.carrier \ (center SL(2,F)).carrier : Set SL(2,F)) =
  ∑ lift_A : Quotient (lift_MaximalAbelianSubgroupsOf G),
    (lift_card_noncenter G center_le_G) lift_A * (lift_card_noncenter_C G) lift_A := by sorry

/- Lemma 2.5 N_G(A) = N_G(A*)-/
lemma normalizer_noncentral_eq {F : Type*} [Field F] (A G : Subgroup SL(2,F)) [Finite G]
  (hA : A ∈ MaximalAbelianSubgroupsOf G) : normalizer A = setNormalizer (noncenter A) := by
  sorry

/- Lemma Let `Q` be a `p`-Sylow subgroup of `G` then $N_G(Q \sqcup Z) = N_G(Q)$-/
lemma normalizer_Sylow_join_center_eq_normalizer_Sylow {F : Type*} [Field F] {p : ℕ}
[Fact (Nat.Prime p)] [CharP F p] (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G) :
  normalizer (map G.subtype Q.toSubgroup ⊔ center SL(2,F)) = normalizer (map G.subtype Q.toSubgroup) := by
  sorry



#min_imports
