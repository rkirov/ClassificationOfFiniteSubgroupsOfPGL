import Mathlib
import ClassificationOfSubgroups.Ch5_PropertiesOfSLOverAlgClosedField.S2_SpecialSubgroups
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_MaximalAbelianSubgroup

set_option maxHeartbeats 0
set_option linter.style.longLine true


variable {R F : Type*} [CommRing R] [Field F]

open Matrix MatrixGroups Subgroup MulAut Pointwise MaximalAbelianSubgroup SpecialSubgroups

/- The non-central part of a subgroup -/
def Subgroup.noncenter {G : Type*} [Group G] (H : Subgroup G) : Set G :=
  {x : G | x ∈ H.carrier \ center G}

/- let M∗ be the set of all Aᵢ* and let Cᵢ* be the conjugacy class of Aᵢ* .-/
def noncenter_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F)) :=
  { noncenter (K : Subgroup SL(2,F)) | K ∈ MaximalAbelianSubgroups G }

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
