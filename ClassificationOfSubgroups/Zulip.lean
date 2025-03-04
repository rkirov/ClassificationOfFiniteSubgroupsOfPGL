import Mathlib

set_option maxHeartbeats 0
set_option linter.style.longLine true


variable {R F : Type*} [CommRing R] [Field F]

open Matrix MatrixGroups Subgroup MulAut Pointwise

def IsMaximalAbelian {L : Type*} [Group L] (G : Subgroup L) : Prop := Maximal (IsCommutative) G

def MaximalAbelianSubgroups { L : Type*} [Group L] (G : Subgroup L) : Set (Subgroup L) :=
  { K : Subgroup L | IsMaximalAbelian (K.subgroupOf G) ∧ K ≤ G}

/- The non-central part of a subgroup -/
def Subgroup.noncenter {G : Type*} [Group G] (H : Subgroup G) : Set G :=
  {x : G | x ∈ H.carrier \ center G}

/- let M∗ be the set of all Aᵢ* and let Cᵢ* be the conjugacy class of Aᵢ* .-/
def noncenter_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F)) :=
  { noncenter (K : Subgroup SL(2,F)) | K ∈ MaximalAbelianSubgroups G }


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
      card_noncenter_MaximalAbelianSubgroupsOf G B:= by sorry

/-
We lift the function which computes the cardinality of the noncentral part of a maximal subgroup
-/
noncomputable def lift_card_noncenter {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (center_le_G : center SL(2,F) ≤ G) [Finite G] :=
  @Quotient.lift _ _ (s := MaximalAbelianSubgroups_lift G)
    (f := card_noncenter_MaximalAbelianSubgroupsOf G)
    (card_eq_of_related_noncenter_subgroups G center_le_G)

open Function

lemma Injective_subroup_to_subset {L : Type*} [Group L] (G : Subgroup L) [Finite G] :
  Injective
    (fun (H : {K | (K : Subgroup L) ≤ G}) =>
      (⟨H.val.carrier, H.property⟩ : {K | K ⊆ G.carrier})) := by
  sorry

instance finite_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Set.Finite (MaximalAbelianSubgroups G) := by
  sorry

instance finite_MaximalAbelianSubgroups' {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Finite (MaximalAbelianSubgroups G) :=
    Set.finite_coe_iff.mpr <| finite_MaximalAbelianSubgroups G

instance finite_MaximalAbelianSubgroups_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Finite (Quotient (MaximalAbelianSubgroups_lift G)) := Quotient.finite _


noncomputable instance fintype_MaximalAbelianSubgroups_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Fintype (Quotient (MaximalAbelianSubgroups_lift G)) := by
  sorry

example {F : Type*} [Field F] (G : Subgroup SL(2,F)) (center_le_G : center SL(2,F) ≤ G)
  [hG : Finite G] : ∑ A_lift : Quotient (MaximalAbelianSubgroups_lift G), (lift_card_noncenter G center_le_G) A_lift = Nat.card (G.carrier \ (center SL(2,F)).carrier :)  := by sorry
