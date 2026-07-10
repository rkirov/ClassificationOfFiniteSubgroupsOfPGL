import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_A_MaximalAbelianSubgroup
import Mathlib.Data.Setoid.Partition
import Mathlib.Data.Set.Card.Arithmetic

set_option linter.style.longLine true
set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0


universe u


open Matrix MatrixGroups Subgroup MulAut MaximalAbelianSubgroup Pointwise SpecialSubgroups


/-- The non-central part of a subgroup as a set. -/
def Subgroup.noncenter {G : Type*} [Group G] (H : Subgroup G) : Set G :=
  H.carrier \ center G


theorem Subgroup.mem_noncenter {G : Type*} [Group G] {H : Subgroup G} {x : G} :
  x ∈ H.noncenter ↔ x ∈ H ∧ x ∉ center G := by
  simp [Subgroup.noncenter, Set.mem_diff, SetLike.mem_coe]

/-
Definition. The set $\mathcal{C}(A) = Cl(A) = \{x A x^{-1} \; | \; x ∈ G \}$
is called the conjugacy class of $A \in \mathcal{M}$.
-/
def ConjClassOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) :=
  { conj x • A.val | x ∈ G }


/- let M∗ be the set of all Aᵢ* and let Cᵢ* be the conjugacy class of Aᵢ* .-/
def noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F)) :=
  { noncenter (K : Subgroup SL(2,F)) | K ∈ MaximalAbelianSubgroupsOf G }

lemma finite_conj_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] (A : noncenter_MaximalAbelianSubgroupsOf G) (c : SL(2,F)) :
    Finite (conj c • A.val :) := by
  refine Set.finite_coe_iff.mpr ?_
  refine Set.Finite.smul_set ?_
  obtain ⟨A', hA', eq_A⟩ := A.prop
  have fin_A' : Finite A' := Set.Finite.subset hG hA'.right
  apply Set.Finite.subset fin_A' (by rw [← eq_A]; exact Set.diff_subset)

def noncenter_ConjClassOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] (A : noncenter_MaximalAbelianSubgroupsOf G) : Set (Finset SL(2,F)) :=
  { conj x • A.val | x ∈ G }


noncomputable instance {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G]
  (A : noncenter_MaximalAbelianSubgroupsOf G) : Fintype (noncenter_ConjClassOf G A) := by
  let decidable_eq : DecidableEq ↑(noncenter_ConjClassOf G A) :=
    Classical.typeDecidableEq ↑(noncenter_ConjClassOf G A)
  let fintype_G : Fintype G := Fintype.ofFinite _
  let finite_conj (c : G) : Finite (conj c.val • A.val :) :=
    finite_conj_noncenter_MaximalAbelianSubgroupsOf G A c
  let fintype_conj (c : G) : Fintype (conj c.val • A.val :) :=
    Fintype.ofFinite _
  apply Fintype.ofSurjective
      (fun (c : G) => ⟨Set.toFinset (conj c.val • A.val), by use c, c.prop; simp⟩)
      ?Surjective
  rintro ⟨B, ⟨c, c_mem_G, hc⟩⟩
  use ⟨c, c_mem_G⟩
  simp [hc]


lemma noncenter_ConjClassOf_disjoint_of_ne {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
  (G : Subgroup SL(2,F)) (center_le_G : center SL(2,F) ≤ G)
  (A B : noncenter_MaximalAbelianSubgroupsOf G) (hAB : A ≠ B) :
    Disjoint A.val B.val := by
  rw [Set.disjoint_right]
  intro b b_mem_B b_mem_A
  obtain ⟨A', hA', hA⟩ := A.prop
  obtain ⟨B', hB', hB⟩ := B.prop
  apply hAB
  suffices A' = B' by
    rw [Subtype.ext_iff, ← hA, this, ← hB]
  have := Imp.swap.mp (center_eq_meet_of_ne_MaximalAbelianSubgroups A' B' G hA' hB') center_le_G
  contrapose! this
  refine ⟨this, ?_⟩
  apply ne_of_not_le
  rw [SetLike.not_le_iff_exists]
  rw [← hB] at b_mem_B
  rw [← hA] at b_mem_A
  unfold noncenter at b_mem_B b_mem_A
  use b
  split_ands
  · apply @Set.diff_subset (SL(2,F)) A'.carrier (center SL(2,F))
    exact b_mem_A
  · apply @Set.diff_subset (SL(2,F)) B'.carrier (center SL(2,F))
    exact b_mem_B
  · exact b_mem_A.right

-- `conj_smul_eq_self_of_mem` is now provided by mathlib as `Subgroup.conj_smul_eq_self_of_mem`.

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
    simp only [MulAut.smul_def, conj_apply]
    rw [noncenter, Set.mem_diff]
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

lemma conj_smul_mem_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : noncenter_MaximalAbelianSubgroupsOf G)
  (c : SL(2,F)) (c_mem_G : c ∈ G) :
    conj c • A.val ∈ noncenter_MaximalAbelianSubgroupsOf G := by
  obtain ⟨A', hA', eq_A⟩ := A.prop
  use conj c • A'
  constructor
  · rwa [← conj_smul_eq_self_of_mem c_mem_G,
      ← mem_iff_conj_smul_mem_MaximalAbelianSubgroupsOf_conj_smul]
  · rw [show A' = (⟨A', hA'⟩ : MaximalAbelianSubgroupsOf G) by rfl,
      conj_noncenter_eq_noncenter_conj]
    simp [eq_A]

lemma noncenter_ConjClassOf_pairwiseDisjoint {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
  (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
  (A : noncenter_MaximalAbelianSubgroupsOf G) :
    (noncenter_ConjClassOf G A).PairwiseDisjoint id := by
  intro X ⟨g, g_mem_G, hX⟩ Y ⟨g', g'_mem_G, hY⟩ hXY
  suffices Disjoint (X : Set SL(2,F)) (Y : Set SL(2,F)) by
    tauto
  rw [← hX, ← hY]
  have := conj_smul_mem_noncenter_MaximalAbelianSubgroupsOf G A g g_mem_G
  rw [show (conj g • A.val)
    = (⟨(conj g • A.val), conj_smul_mem_noncenter_MaximalAbelianSubgroupsOf G A g g_mem_G⟩
      : noncenter_MaximalAbelianSubgroupsOf G) by rfl,
    show (conj g' • A.val)
      = (⟨(conj g' • A.val), conj_smul_mem_noncenter_MaximalAbelianSubgroupsOf G A g' g'_mem_G⟩
        : noncenter_MaximalAbelianSubgroupsOf G) by rfl]
  exact noncenter_ConjClassOf_disjoint_of_ne G center_le_G _ _ (by simp [hX, hY, hXY])


/--
The conjugacy class of a noncentral maximal abelian subgroups defines an equivalence
relation
-/
noncomputable instance lift_noncenter_ConjClassOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] (A : noncenter_MaximalAbelianSubgroupsOf G) :
  Setoid (noncenter_ConjClassOf G A) where
  r X Y := X.val = Y.val
  iseqv := {
    refl X := by simp
    symm := by intro X Y hXY; exact hXY.symm
    trans := by intro X Y Z hXY hYZ; exact hYZ ▸ hXY
  }


noncomputable def card_noncenter_ConjClassOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : noncenter_MaximalAbelianSubgroupsOf G → ℕ :=
  fun A => Nat.card (noncenter_ConjClassOf G A)

section noncenter_MaximalAbelianSubgroupsOf


lemma noncenter_mem_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : A.val.noncenter ∈ noncenter_MaximalAbelianSubgroupsOf G := by
  use A, A.prop

/-
Define the equivalence relation $\sim$ on $\mathcal{M}^*$ by
$A_i \sim A_j$ if and only if $A_i = x A_j x^{-1}$ for some $x \in G$.
 -/
instance lift_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F] (G : Subgroup SL(2,F)) :
  Setoid (noncenter_MaximalAbelianSubgroupsOf G) where
  r A B := ∃ x ∈ G, conj x • A.val = B.val
  iseqv := {
    refl := by rintro A
               exact ⟨1, Subgroup.one_mem G, by simp⟩
    symm := by
      rintro A B ⟨x, x_in_G, hx⟩
      use x⁻¹
      simp only [inv_mem_iff, map_inv] at hx ⊢
      rw [inv_smul_eq_iff]
      exact ⟨x_in_G, hx.symm⟩
    trans := by
      rintro A B C ⟨x, x_in_G,  hx⟩ ⟨y, y_in_G, hy⟩
      use y * x
      rw [← hy, ← hx, smul_smul, MonoidHom.map_mul]
      exact ⟨Subgroup.mul_mem G y_in_G x_in_G, rfl⟩
  }

def Partition_lift_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) := (lift_noncenter_MaximalAbelianSubgroupsOf G).classes



/-
Define $C (A)^* = \bicup_{x \in G} x A^*  x^{-1}$
-/
def union_conjClasses_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :
  noncenter_MaximalAbelianSubgroupsOf G → Set SL(2,F) :=
    fun A => ⋃ x ∈ G, conj x • A.val


lemma union_conjClasses_noncenter_eq_of_related {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] : (∀ (A B : (noncenter_MaximalAbelianSubgroupsOf G)),
    A ≈ B → union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G A =
     union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G B) := by
  intro A B ArB
  obtain ⟨r, r_in_G, hr⟩ := ArB
  simp only [union_conjClasses_noncenter_MaximalAbelianSubgroupsOf]
  ext y
  constructor
  <;> intro hy
  <;> simp only [Set.mem_iUnion, exists_prop] at hy ⊢
  <;> obtain ⟨g, g_in_G, y_in_conj⟩ := hy
  · simp only [← hr]
    use g * r⁻¹
    split_ands
    · exact Subgroup.mul_mem G g_in_G (inv_mem r_in_G)
    · simp only [_root_.map_mul, map_inv, ← mul_smul, inv_mul_cancel_right]
      exact y_in_conj
  · simp only [←  hr] at y_in_conj
    use g * r
    split_ands
    · exact Subgroup.mul_mem G g_in_G r_in_G
    rw [_root_.map_mul, mul_smul]
    exact y_in_conj

def lift_union_conj_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :=
  @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G)
    (f := union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G)
      (union_conjClasses_noncenter_eq_of_related G)

@[simp]
lemma lift_union_conj_noncenter_MaximalAbelianSubgroupsOf_mk {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] (A : noncenter_MaximalAbelianSubgroupsOf G):
  lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G
    (Quot.mk (⇑(lift_noncenter_MaximalAbelianSubgroupsOf G)) A)
    = union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G A := by
  rfl

end noncenter_MaximalAbelianSubgroupsOf

section MaximalAbelianSubgroupsOf
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
      simp only [inv_mem_iff, map_inv] at hx ⊢
      rw [inv_smul_eq_iff]
      exact ⟨hx.left, hx.right.symm⟩
    trans := by
      rintro ⟨A, hA⟩ ⟨B, hB⟩ ⟨C, hC⟩ ⟨x, hx⟩ ⟨y, hy⟩
      use y * x
      split_ands
      · exact Subgroup.mul_mem G hy.left hx.left
      · rw [← hy.right, ← hx.right, smul_smul, MonoidHom.map_mul]
  }

noncomputable def card_noncenter {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : noncenter_MaximalAbelianSubgroupsOf G → ℕ :=
  fun A => Nat.card A.val

/-
The function which computes the cardinality of the noncentral part of a maximal abelian subgroup,
respects the equivalence relation on the setoid of maximal abelian subgroups of `G`.
-/
lemma card_noncenter_eq_of_related {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] :
  ∀ (A B : (noncenter_MaximalAbelianSubgroupsOf G)),
    A ≈ B → card_noncenter G A =
      card_noncenter G B := by
  rintro ⟨A_star, A, A_in_MaxAbSub, hA⟩ ⟨B_star, B, B_in_MaxAbSub, hB⟩ ⟨x, x_in_G, rfl⟩
  simp only [card_noncenter, Nat.card_coe_set_eq]
  let center_finite : Finite (center SL(2, F)) := by
    rw [center_SL2_eq_Z]
    infer_instance
  simp

/-
We lift the function which computes the cardinality of the noncentral part of a maximal subgroup
-/
noncomputable def lift_card_noncenter {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] := @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G)
    (f := card_noncenter G)
    (card_noncenter_eq_of_related G)


def toConjClassOfSet {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :
    noncenter_MaximalAbelianSubgroupsOf G → Set (Finset SL(2,F)) :=
  fun A => noncenter_ConjClassOf G A


lemma toConjClassOfSet_eq_of_related_noncenter_subgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :
  (∀ (A B : noncenter_MaximalAbelianSubgroupsOf G),
    A ≈ B → toConjClassOfSet G A = toConjClassOfSet G B) := by
  intro A B ArB
  obtain ⟨x, x_in_G, hx⟩ := ArB
  simp only [toConjClassOfSet, noncenter_ConjClassOf]
  ext s
  constructor
  · rintro ⟨y, y_in_G, eq_s⟩
    simp only [← eq_s, ← hx, Set.mem_setOf_eq]
    use y * x⁻¹
    rw [MonoidHom.map_mul, mul_smul, smul_left_cancel_iff, map_inv, inv_smul_eq_iff]
    exact ⟨Subgroup.mul_mem G y_in_G (inv_mem x_in_G), rfl⟩
  · rintro ⟨y, y_in_G, eq_s⟩
    simp only [← eq_s, ← hx, Set.mem_setOf_eq]
    use y * x
    rw [MonoidHom.map_mul, mul_smul, smul_left_cancel_iff]
    exact ⟨Subgroup.mul_mem G y_in_G x_in_G, rfl⟩


def lift_ConjClassOfSet {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G] :=
  @Quotient.lift _ _ (s := lift_noncenter_MaximalAbelianSubgroupsOf G) (f := toConjClassOfSet G)
    (toConjClassOfSet_eq_of_related_noncenter_subgroups G)


end MaximalAbelianSubgroupsOf

section Finite

open Function

lemma Injective_subroup_to_subset {L : Type*} [Group L] (G : Subgroup L) [Finite G] :
  Injective
    (fun (H : {K | (K : Subgroup L) ≤ G}) =>
      (⟨H.val.carrier, H.property⟩ : {K | K ⊆ G.carrier})) := by
  rintro ⟨A, hA⟩ ⟨B, hB⟩ hAB
  simp only [Set.mem_setOf_eq, Subtype.mk.injEq, Set.coe_setOf] at hAB ⊢
  refine toSubmonoid_inj.mp ?_
  ext x
  exact Eq.to_iff (congrFun hAB x)


lemma finite_MaximalAbelianSubgroups {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Set.Finite (MaximalAbelianSubgroupsOf G) := by
  apply Set.Finite.subset (s := {K | (K : Subgroup SL(2,F)) ≤ G})
  · apply @Finite.of_injective _ _ ?set_finite _ (Injective_subroup_to_subset G)
    exact Set.Finite.finite_subsets hG
  · intro M hM
    exact hM.right

instance finite_MaximalAbelianSubgroups' {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Finite (MaximalAbelianSubgroupsOf G) :=
    Set.finite_coe_iff.mpr <| finite_MaximalAbelianSubgroups G

instance finite_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] : Finite (noncenter_MaximalAbelianSubgroupsOf G) := by
  dsimp [noncenter_MaximalAbelianSubgroupsOf]
  refine Finite.of_surjective (
    fun (A : MaximalAbelianSubgroupsOf G) =>
    (
      ⟨noncenter A.val,
      noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G A⟩ :
      noncenter_MaximalAbelianSubgroupsOf G
    )
    ) ?_
  rintro ⟨A_star, A, A_mem_MaximalAbelianSubgroupsOf, hA⟩
  use ⟨A, A_mem_MaximalAbelianSubgroupsOf⟩
  exact Subtype.ext hA

lemma finite_MaximalAbelianSubgroups_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [hG : Finite G] : Finite (Quotient (lift_MaximalAbelianSubgroupsOf G)) := Quotient.finite _

instance finite_lift_noncenter_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] :
  Finite (Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G)) := Quotient.finite _

noncomputable instance fintype_lift_MaximalAbelianSubgroupsOf {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [hG : Finite G] :
  Fintype (Quotient (lift_MaximalAbelianSubgroupsOf G)) := by
  apply fintypeOfNotInfinite
  rw [not_infinite_iff_finite]
  exact finite_MaximalAbelianSubgroups_lift G

noncomputable instance fintype_lift_noncenter_MaximalAbelianSubgroups {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [hG : Finite G] :
  Fintype (Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G)) := by
  apply fintypeOfNotInfinite
  rw [not_infinite_iff_finite]
  exact finite_lift_noncenter_MaximalAbelianSubgroupsOf G


end Finite

/-
Somehow need to lift this statement

⋃ A_star : lift_noncenter_MaximalAbelianSubgroupsOf G,
      lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star

or

⋃ A_star : lift_noncenter_MaximalAbelianSubgroupsOf G,
      lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star.exists_rep.choose


-/

lemma union_noncenter_C_eq_G_diff_center {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  (G : Subgroup SL(2,F)) [hG : Finite G] :
  G.carrier \ center SL(2,F) =
    ⋃ A_star : noncenter_MaximalAbelianSubgroupsOf G,
      union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G A_star := by
    ext x
    constructor
    · rintro hx
      rw [Set.mem_iUnion]
      use ⟨
        centralizer {x} ⊓ G \ center SL(2,F), by
        dsimp [noncenter_MaximalAbelianSubgroupsOf]
        use centralizer {x} ⊓ G
        constructor
        · exact centralizer_inf_mem_maximalAbelianSubgroupsOf_of_noncentral G x hx
        · rw [Set.inter_diff_distrib_left]
          have center_le_centralizer : center SL(2,F) ≤ centralizer {x} := center_le_centralizer {x}
          rw [Set.inter_eq_self_of_subset_right center_le_centralizer]
          rfl⟩
      dsimp [union_conjClasses_noncenter_MaximalAbelianSubgroupsOf]
      rw [Set.mem_iUnion₂]
      use 1
      simp only [_root_.map_one, one_smul, Set.mem_inter_iff, SetLike.mem_coe, Set.mem_diff,
        exists_and_left, exists_prop]
      split_ands
      · exact mem_centralizer_singleton_iff.mpr rfl
      · apply hx.left
      · exact Subgroup.one_mem G
      · apply hx.right
    · intro hx
      rw [@Set.mem_iUnion] at hx
      obtain ⟨A_star, hA⟩ := hx
      dsimp [union_conjClasses_noncenter_MaximalAbelianSubgroupsOf] at hA
      simp [noncenter_MaximalAbelianSubgroupsOf] at A_star
      rw [Set.mem_iUnion₂] at hA
      obtain ⟨c, hc⟩ := hA
      simp only [exists_prop] at hc
      obtain ⟨c_mem_G, x_mem_conj_c⟩ := hc
      obtain ⟨A, A_MaximalAbelian, hA⟩ := A_star.prop
      simp only [← hA, noncenter, Set.mem_smul_set_iff_inv_smul_mem, MulAut.smul_def, inv_apply,
        conj_symm_apply, Set.mem_diff, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
        mem_toSubmonoid, SetLike.mem_coe] at x_mem_conj_c
      have A_subs_G := A_MaximalAbelian.right
      obtain ⟨x_mem_G, x_not_mem_center⟩ := x_mem_conj_c
      rw [← @conj_inv_apply, ← MulAut.smul_def, ← mem_carrier,
        ← Set.mem_smul_set_iff_inv_smul_mem] at x_mem_G x_not_mem_center
      simp only [Set.mem_diff, Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup,
        mem_toSubmonoid, SetLike.mem_coe]
      split_ands
      · apply conj_smul_le_of_le A_subs_G ⟨c, c_mem_G⟩
        apply x_mem_G
      · have conj_center_eq_center : conj c • (center SL(2, F)) = (center SL(2,F)) := by
          exact Normal.conj_smul_eq_self c (center SL(2, F))
        have : conj c • (center SL(2,F)).carrier = (conj c • (center SL(2, F))).carrier := by rfl
        rw [(by rfl : conj c • (center SL(2,F)).carrier = (conj c • (center SL(2, F))).carrier),
          conj_center_eq_center] at x_not_mem_center
        exact x_not_mem_center


/-
Theorem 2.4 i a)
The union of elements of the `Quotient` on the `Setoid`,
`lift_noncenter_MaximalAbelianSubgroups G` is equal to `G \ Z`
-/
lemma union_lift_union_conj_noncenter_MaximalAbelianSubgroupsOf_eq_G_diff_center {F : Type*}
  [Field F] [IsAlgClosed F] [DecidableEq F] (G : Subgroup SL(2,F)) [hG : Finite G] :
  G.carrier \ center SL(2,F) =
    ⋃ A_star : Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G),
      lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G A_star := by
    rw [union_noncenter_C_eq_G_diff_center]
    ext x
    constructor
    · intro hx
      rw [Set.mem_iUnion] at hx ⊢
      obtain ⟨noncenter_M, hM⟩ := hx
      use Quotient.mk (lift_noncenter_MaximalAbelianSubgroupsOf G) noncenter_M
      exact hM
    · intro hx
      rw [Set.mem_iUnion] at hx ⊢
      obtain ⟨lift_noncenter_M, hM⟩ := hx
      obtain ⟨noncenter_M, hM'⟩ := Quot.exists_rep lift_noncenter_M
      use noncenter_M
      rw [← hM'] at hM
      exact hM



/-
Theorem 2.4 i b)
Distinct elements in the `Quotient` of the `Setoid`,
`lift_noncenter_MaximalAbelianSubgroups G` map to disjoint subsets
when sent through `lift_noncenter_C`.
-/


section Subsets

def subsets_MaximalAbelianSubgroups {L : Type*} [Group L] (G : Subgroup L) :=
  { (K : Set L) | K ∈ MaximalAbelianSubgroupsOf G }

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

open Function

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
      simp only [map_inv] at hx ⊢
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



end Subsets


/-
Define $C(A) = \bigcup_{x \in G} xA x^{-1}$
-/
def C {F : Type*} [Field F] (G : Subgroup SL(2,F)) [Finite G]
  (A : MaximalAbelianSubgroupsOf G) := ⋃ x ∈ G, conj x • A.val.carrier


def noncenter_MaximalAbelianSubgroupOf_IsPartition {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) := Setoid.isPartition_classes <| lift_noncenter_MaximalAbelianSubgroupsOf G


/--
We have the relation $|C(A^*)| = |A^*| |\mathcal{C}(A^*)|$
-/
lemma card_noncenter_C_eq_noncenter_MaximalAbelianSubgroup_mul_noncenter_ConjClassOfSet
  {F : Type*} [hF : Field F] [DecidableEq F] [IsAlgClosed F] (G : Subgroup SL(2,F)) [hG : Finite G]
  (center_le_G : center SL(2,F) ≤ G) (A : noncenter_MaximalAbelianSubgroupsOf G) :
    Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G A)
      = Nat.card A * card_noncenter_ConjClassOf G A := by
  dsimp [union_conjClasses_noncenter_MaximalAbelianSubgroupsOf]
  have noncenter_ConjClassOf_pairwiseDisjoint :=
    noncenter_ConjClassOf_pairwiseDisjoint G center_le_G A
  let fintype : Fintype (noncenter_ConjClassOf G A) := inferInstance
  rw [show noncenter_ConjClassOf G A =
    Set.toFinset (noncenter_ConjClassOf G A) by
    apply (Set.coe_toFinset (noncenter_ConjClassOf G A)).symm]
    at noncenter_ConjClassOf_pairwiseDisjoint
  have card_disjiUnion := Finset.card_disjiUnion
    (noncenter_ConjClassOf G A).toFinset _ noncenter_ConjClassOf_pairwiseDisjoint
  have eq : (noncenter_ConjClassOf G A).toFinset.disjiUnion
    id noncenter_ConjClassOf_pairwiseDisjoint
    = (⋃ x ∈ G, conj x • A.val) := by
    ext x
    simp only [noncenter_ConjClassOf, Finset.coe_disjiUnion, Set.coe_toFinset, Set.mem_setOf_eq,
      id_eq, Set.iUnion_exists, Set.biUnion_and', Set.mem_iUnion, SetLike.mem_coe, exists_prop]
    constructor
    · rintro ⟨g, g_mem_G, ⟨conj_A, h_conj_A, x_mem_conj_A⟩⟩
      use g, g_mem_G
      simp_all
    · rintro ⟨g, g_mem_G, x_mem_conj_A⟩
      let : Finite (conj g • A.val :) := finite_conj_noncenter_MaximalAbelianSubgroupsOf G A g
      let : Fintype (conj g • A.val :) := Fintype.ofFinite _
      use g, g_mem_G, (conj g • A.val).toFinset
      simp_all
  rw [← eq, show Set.ncard (SetLike.coe ((noncenter_ConjClassOf G A).toFinset.disjiUnion
    id noncenter_ConjClassOf_pairwiseDisjoint))
    = ((noncenter_ConjClassOf G A).toFinset.disjiUnion id
      noncenter_ConjClassOf_pairwiseDisjoint).card by exact Set.ncard_coe_finset _,
      card_disjiUnion]
  simp only [id_eq]
  have sum_congr : ∑ x ∈ (noncenter_ConjClassOf G A).toFinset, x.card
    = ∑ x ∈ (noncenter_ConjClassOf G A).toFinset, A.val.ncard := by
    refine Finset.sum_equiv (Equiv.refl _) (by simp) ?_
    intro A' hA'
    simp only [Set.mem_toFinset] at hA'
    rw [← Set.ncard_coe_finset A']
    obtain ⟨c, -, eq_B⟩ := hA'
    simp [← eq_B]
  rw [sum_congr, Finset.sum_const, mul_comm]
  congr
  simp [card_noncenter_ConjClassOf]



/--
The subset `G \ Z F` is covered by the union of conjugacy classes of a noncenter maximal
abelian subgroup
-/
lemma sdiff_center_eq_union_noncenter_C {F : Type*} [Field F] [DecidableEq F]
  [IsAlgClosed F] (G : Subgroup SL(2,F))
  [Finite G] : G.carrier \ center (SL(2,F)) =
    ⋃ A : noncenter_MaximalAbelianSubgroupsOf G,
      union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G A := by
    ext x
    constructor
    · intro hx
      unfold union_conjClasses_noncenter_MaximalAbelianSubgroupsOf
      rw [Set.mem_iUnion]
      use ⟨
        (noncenter (centralizer {x} ⊓ G)),
        by
        unfold noncenter_MaximalAbelianSubgroupsOf
        rw [Set.mem_setOf_eq]
        have centralizer_x_inf_G_mem :=
          centralizer_inf_mem_maximalAbelianSubgroupsOf_of_noncentral G x hx
        use (centralizer {x} ⊓ G)⟩
      rw [Set.mem_iUnion]
      use 1
      simp only [one_mem, map_one, noncenter, one_smul, Set.iUnion_true, Set.mem_diff,
        Subsemigroup.mem_carrier, Submonoid.mem_toSubsemigroup, mem_toSubmonoid, mem_inf,
        SetLike.mem_coe]
      split_ands
      · exact mem_centralizer_singleton_iff.mpr rfl
      · exact mem_carrier.mp hx.left
      · exact hx.right
    · intro hx
      rw [Set.mem_iUnion] at hx
      obtain ⟨noncenter_A, U, hU, x_mem_U⟩ := hx
      have h_noncenter_A := noncenter_A.prop
      obtain ⟨A, hA, hA'⟩ := h_noncenter_A
      simp only [Set.mem_range] at hU
      obtain ⟨c, eq_U⟩ := hU
      rw [← eq_U, Set.mem_iUnion] at x_mem_U
      obtain ⟨c_mem_G, hc⟩ := x_mem_U
      rw [← hA'] at hc
      constructor
      · suffices x ∈ conj c • G by
          rwa [conj_smul_eq_self_of_mem c_mem_G] at this
        rw [mem_pointwise_smul_iff_inv_smul_mem]
        apply hA.right
        apply (@Set.diff_subset SL(2,F) A (center SL(2,F)))
        rw [Set.mem_smul_set_iff_inv_smul_mem] at hc
        assumption
      · rw [Set.mem_smul_set_iff_inv_smul_mem] at hc
        unfold noncenter at hc
        obtain ⟨-, c_not_mem_center⟩ := hc
        intro contr
        have : conj c • center SL(2,F) = center SL(2,F) := by
          apply Normal.conj_smul_eq_self c (center SL(2, F))
        rw [← this, coe_pointwise_smul, Set.mem_smul_set_iff_inv_smul_mem] at contr
        contradiction


noncomputable def ConjClassOf_to_noncenter_ConjClassOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) [hG : Finite G] : (ConjClassOf G A) → (noncenter_ConjClassOf G (
      ⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G A⟩)) :=
  let finite (B : ConjClassOf G A) : Finite B.val.noncenter := by
    refine Set.finite_coe_iff.mpr ?_
    unfold noncenter
    apply Set.Finite.subset ?_ (@Set.diff_subset _ B.val.carrier (center SL(2, F)))
    obtain ⟨g, g_mem_G, eq_C⟩ := B.prop
    rw [← eq_C]
    suffices Finite A.val by
      exact Set.Finite.of_surjOn _ (fun ⦃a⦄ ha ↦ ha) this
    exact Set.Finite.subset hG (by simp [A.prop.right])
  let fintype (B : ConjClassOf G A) : Fintype B.val.noncenter := Fintype.ofFinite _
  fun B => ⟨
    B.val.noncenter.toFinset,
    by
    obtain ⟨c, c_mem_G, conj_B_eq⟩ := B.prop
    use c, c_mem_G
    simp [← conj_noncenter_eq_noncenter_conj, ← conj_B_eq]
  ⟩

open Function


lemma conj_subgroup_eq_conj_center_union_conj_noncenter {G : Type*} [Group G] (H : Subgroup G)
  (c : G) : (conj c • H : Set G)
    = (conj c • H.noncenter : Set G) ∪ (conj c • (center G ⊓ H) : Set G) := by
  unfold noncenter
  rw [← Set.image_smul, ← Set.image_smul, ← Set.image_smul, ← Set.image_union,
  Set.union_comm]
  congr
  rw [← Set.diff_self_inter, Set.inter_comm, show H.carrier = (H : Set G) by rfl]
  simp only [coe_inf]
  rw [Set.union_diff_cancel (Set.inter_subset_right)]


lemma mem_coe_conj_iff_conj_coe {G : Type*} [Group G] (H : Subgroup G) (c x : G) :
    x ∈ conj c • H ↔ x ∈ (conj c • H : Set G) := by rfl


-- For Mathlib
lemma instNormalLeCenter {G : Type*} [Group G] (H : Subgroup G)
  (hH : H ≤ center G) : Normal H := by
  rw [← normalizer_eq_top_iff, eq_top_iff]
  intro x hx
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    simp [(@mem_center_iff G _ h).mp (hH hh), hh]
  · intro hh
    rw [show x * h * x⁻¹ = conj x • h by rfl] at hh
    have h_mem_center := hH hh
    rw [← mem_inv_pointwise_smul_iff, ← map_inv,
      Normal.conj_smul_eq_self] at h_mem_center
    rw [← show x * h * x⁻¹ = conj x • h by rfl] at hh
    simpa [(@mem_center_iff G _ h).mp h_mem_center] using hh

-- For Mathlib
instance instNormalCenterInf {G : Type*} [Group G] {H : Subgroup G} :
    Normal (center G ⊓ H) := instNormalLeCenter (center G ⊓ H) inf_le_left



-- For Mathlib
lemma subset_of_union_eq_of_disjoint {G : Type*} (A B C : Set G) (hA : Disjoint A C)
  (h : A ∪ C = B ∪ C) : A ⊆ B := by
  intro a a_mem_A
  have a_mem_B_union_C : a ∈ B ∪ C := by
    rw [← h]
    exact Set.mem_union_left C a_mem_A
  suffices a ∉ C by
    rw [Set.mem_union] at a_mem_B_union_C
    grind
  have A_inter_C_eq_empty : A ∩ C = ∅ := Disjoint.inter_eq hA
  intro a_mem_C
  have contr : a ∈ (∅ : Set G) := by rw [← A_inter_C_eq_empty]; grind
  contradiction


-- For Mathlib
lemma eq_iff_union_eq_of_disjoint {G : Type*} (A B C: Set G) (hA : Disjoint A C)
  (hB : Disjoint B C) : A ∪ C = B ∪ C ↔ A = B := by
  constructor
  · intro h
    apply subset_antisymm
    · exact subset_of_union_eq_of_disjoint A B C hA h
    · exact subset_of_union_eq_of_disjoint B A C hB (id (Eq.symm h))
  · intro h
    rw [h]

theorem Disjoint_conj_noncenter_center {G : Type*} [inst : Group G]
  {c : G} (H : Subgroup G) (key : conj c • (center G ⊓ H) = center G ⊓ H)  :
  Disjoint (conj c • H.noncenter) ↑(center G ⊓ H) := by
  rw [disjoint_comm, disjoint_iff, eq_bot_iff, ← key]
  intro x ⟨x_mem_center, x_mem_conj⟩
  simp only [noncenter] at x_mem_conj
  push_cast at x_mem_center
  rw [Set.mem_smul_set_iff_inv_smul_mem] at x_mem_conj x_mem_center
  rw [Set.mem_diff] at x_mem_conj
  suffices (conj c)⁻¹ • x ∈ center G by
    absurd x_mem_conj.right
    exact this
  apply Set.inter_subset_left
  apply x_mem_center


-- it is not clear whether I should be defining `Subgroup.noncenter`
-- or trying an alternative formalization
lemma conj_eq_conj_iff {G : Type*} [Group G] {c c' : G} (H : Subgroup G) :
    conj c • H.noncenter = conj c' • H.noncenter ↔ conj c • H = conj c' • H := by
  -- have :=  conj_subgroup_eq_conj_center_union_conj_noncenter H c
  suffices conj c • H.noncenter = conj c' • H.noncenter ↔ (conj c • H : Set G) = conj c' • H by
    simp only [this]
    constructor <;> intro h <;> ext x
    · rw [mem_coe_conj_iff_conj_coe, mem_coe_conj_iff_conj_coe, h]
    · rw [← mem_coe_conj_iff_conj_coe, ← mem_coe_conj_iff_conj_coe, h]
  rw [conj_subgroup_eq_conj_center_union_conj_noncenter]
  have key₁ : conj c • (center G ⊓ H) = center G ⊓ H := Subgroup.Normal.conj_smul_eq_self c _
  norm_cast
  rw [key₁]
  push_cast
  rw [conj_subgroup_eq_conj_center_union_conj_noncenter]
  have key₂ : conj c' • (center G ⊓ H) = center G ⊓ H := Subgroup.Normal.conj_smul_eq_self c' _
  norm_cast
  rw [key₂]
  symm
  rw [eq_iff_union_eq_of_disjoint _ _]
  · exact Disjoint_conj_noncenter_center H key₁
  · exact Disjoint_conj_noncenter_center H key₂


lemma Bijective_ConjClassOf_to_noncenter_ConjClassOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  [Finite G] (A : MaximalAbelianSubgroupsOf G) :
    Bijective (ConjClassOf_to_noncenter_ConjClassOf G A) := by
  refine ⟨?Injective, ?Surjective⟩
  · intro conj_A conj_B hAB
    obtain ⟨c, c_mem_G, conj_A_eq⟩ := conj_A.prop
    obtain ⟨c', c'_mem_G, conj_B_eq⟩ := conj_B.prop
    simp only [ConjClassOf_to_noncenter_ConjClassOf, Subtype.mk.injEq,
      ← conj_A_eq, conj_noncenter_eq_noncenter_conj, ← conj_B_eq, Set.toFinset_inj] at hAB
    rw [conj_eq_conj_iff] at hAB
    apply Subtype.ext
    rw [← conj_A_eq, ← conj_B_eq, hAB]
  · intro ⟨A_noncenter, c, c_mem_G, conj_A_noncenter_eq⟩
    use ⟨conj c • A, by simp only [ConjClassOf, Set.mem_setOf_eq]; use c⟩
    simp [ConjClassOf_to_noncenter_ConjClassOf, conj_noncenter_eq_noncenter_conj A c,
      conj_A_noncenter_eq]



/-
Theorem 2.4 ii)
$|\mathcal{C}_i| = |\mathcal{C}_i^*|$
-/
lemma card_noncenter_ConjClassOfSet_eq_card_ConjClassOfSet {F : Type*} [Field F]
  (G : Subgroup SL(2,F)) [Finite G] (A : MaximalAbelianSubgroupsOf G) :
    Nat.card (ConjClassOf G A) =
    Nat.card (noncenter_ConjClassOf G (
      ⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G A⟩
    )) := by
  exact Nat.card_eq_of_bijective _ (Bijective_ConjClassOf_to_noncenter_ConjClassOf G A)


noncomputable def conjClassOf_to_G {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : ConjClassOf G A → G :=
  fun ⟨_, h⟩ => ⟨h.choose, h.choose_spec.left⟩

def G_to_ConjClassOf {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : G → ConjClassOf G A :=
  fun ⟨c, hc⟩ => ⟨conj c • A.val, by use c⟩



def G_to_ConjClassOf_lift  {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : G ⧸ (normalizer (A.val.subgroupOf G : Set ↥G)) → ConjClassOf G A :=
  Quot.lift (G_to_ConjClassOf G A)
  (by
  intro ⟨c, c_mem_G⟩ ⟨c', c'_mem_G⟩ h
  symm at h
  rw [← Quotient.eq_iff_equiv, Quotient.eq, QuotientGroup.leftRel_apply, mem_normalizer_iff] at h
  simp only [G_to_ConjClassOf, Subtype.mk.injEq]
  rw [smul_eq_iff_eq_inv_smul, ← MonoidHom.map_inv, smul_smul, ← map_mul]
  ext x; constructor
  · intro hx
    specialize h ⟨x, A.prop.right hx⟩
    simp [mem_subgroupOf] at h
    simp [mem_pointwise_smul_iff_inv_smul_mem]
    group at h ⊢
    apply h.mp hx
  · intro hx
    simp only [map_mul, map_inv, mem_pointwise_smul_iff_inv_smul_mem, _root_.mul_inv_rev, inv_inv,
      MulAut.smul_def, MulAut.mul_apply, conj_apply, inv_apply, conj_symm_apply] at hx
    group at hx
    have x_mem_G := A.prop.right hx
    rw [show c' ^ (-1 : ℤ) * c * x * c ^ (-1 : ℤ) * c' = (conj (c⁻¹ * c'))⁻¹ • x by simp; group,
      ← mem_pointwise_smul_iff_inv_smul_mem] at x_mem_G
    suffices conj (c⁻¹ * c') • G = G by
      rw [this] at x_mem_G
      specialize h ⟨x, x_mem_G⟩
      simp [mem_subgroupOf] at h
      group at h hx
      apply h.mpr hx
    exact conj_smul_eq_self_of_mem (G.mul_mem (G.inv_mem c_mem_G) c'_mem_G))

@[simp]
lemma G_to_ConjClassOf_lift_apply {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) (x : G) :
  G_to_ConjClassOf_lift G A ((Quot.mk (⇑(QuotientGroup.leftRel (normalizer (A.val.subgroupOf G : Set ↥G)))) x))
    = (G_to_ConjClassOf G A x) := rfl


lemma Bijective_G_to_ConjClassOf_lift {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) : Bijective (G_to_ConjClassOf_lift G A) := by
  refine ⟨?Injective, ?Surjective⟩
  · intro x y hxy
    induction x using Quot.ind with
    | mk x =>
      induction y using Quot.ind with
      | mk y =>
      simp only [G_to_ConjClassOf_lift_apply, G_to_ConjClassOf, Subtype.mk.injEq] at hxy
      rw [Quot.sound]
      rw [QuotientGroup.leftRel_apply, mem_normalizer_iff]
      intro h
      rw [smul_eq_iff_eq_inv_smul, ← MonoidHom.map_inv, smul_smul, ← map_mul] at hxy
      rw [mem_subgroupOf, mem_subgroupOf, _root_.mul_inv_rev, inv_inv]
      simp only [Subgroup.coe_mul]
      rw [show ((x⁻¹ : G) : SL(2,F)) * y * h * (y⁻¹ * x)
        = conj ((x⁻¹ : SL(2,F)) * y) • (h : SL(2,F)) by simp; group, hxy]
      rw [smul_mem_pointwise_smul_iff, ← hxy]
  · dsimp [G_to_ConjClassOf_lift]
    apply (Quot.surjective_lift _).mpr
    intro ⟨conj_A, c, c_mem_G, conj_A_eq⟩
    use ⟨c, c_mem_G⟩
    simp [G_to_ConjClassOf, ← conj_A_eq]

/--
Theorem 2.4 iii)
$|\mathcal{C}_i| = [G : N_G(A_i)]$
-/
lemma card_ConjClassOf_eq_index_normalizer {F : Type*} [Field F] (G : Subgroup SL(2,F))
  (A : MaximalAbelianSubgroupsOf G) :
    Nat.card (ConjClassOf G A) = index (normalizer (A.val.subgroupOf G : Set ↥G)) := by
  rw [index]
  symm
  exact Nat.card_eq_of_bijective (G_to_ConjClassOf_lift G A) (Bijective_G_to_ConjClassOf_lift G A)


noncomputable instance {F : Type*} [Field F] {G : Subgroup SL(2,F)} [Finite G] :
  Fintype (Quotient (lift_MaximalAbelianSubgroupsOf G)) := by infer_instance


/--
The "big unions" `C(A)^*` attached to two inequivalent noncentral maximal abelian subgroups
are disjoint: if a conjugate of `A` and a conjugate of `B` shared an element, those two
conjugates would themselves be equal noncentral maximal abelian subgroups (by
`noncenter_ConjClassOf_disjoint_of_ne`), forcing `A ≈ B`.
-/
lemma union_conjClasses_noncenter_pairwise_disjoint_of_not_equiv {F : Type*} [Field F]
  [DecidableEq F] [IsAlgClosed F] (G : Subgroup SL(2,F)) [Finite G]
  (center_le_G : center SL(2,F) ≤ G)
  (A B : noncenter_MaximalAbelianSubgroupsOf G) (hAB : ¬ A ≈ B) :
    Disjoint (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G A)
      (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G B) := by
  rw [Set.disjoint_left]
  intro z hzA hzB
  dsimp [union_conjClasses_noncenter_MaximalAbelianSubgroupsOf] at hzA hzB
  rw [Set.mem_iUnion₂] at hzA hzB
  obtain ⟨g₁, hg₁, hzA⟩ := hzA
  obtain ⟨g₂, hg₂, hzB⟩ := hzB
  apply hAB
  have hB1mem : conj g₁ • A.val ∈ noncenter_MaximalAbelianSubgroupsOf G :=
    conj_smul_mem_noncenter_MaximalAbelianSubgroupsOf G A g₁ hg₁
  have hB2mem : conj g₂ • B.val ∈ noncenter_MaximalAbelianSubgroupsOf G :=
    conj_smul_mem_noncenter_MaximalAbelianSubgroupsOf G B g₂ hg₂
  have hB12 : (⟨conj g₁ • A.val, hB1mem⟩ : noncenter_MaximalAbelianSubgroupsOf G)
      = ⟨conj g₂ • B.val, hB2mem⟩ := by
    by_contra hne
    exact (Set.disjoint_left.mp
      (noncenter_ConjClassOf_disjoint_of_ne G center_le_G _ _ hne) hzA) hzB
  have heq : conj g₁ • A.val = conj g₂ • B.val := Subtype.ext_iff.mp hB12
  refine ⟨g₂⁻¹ * g₁, G.mul_mem (G.inv_mem hg₂) hg₁, ?_⟩
  rw [_root_.map_mul, mul_smul, heq, ← mul_smul, ← _root_.map_mul, inv_mul_cancel, map_one,
    one_smul]

/-
Theorem 2.4 iv)
$|G \setminus Z| = \sum_{[A] \in \mathfrak{M} / \sim } |[A*]| |[C(A)*]|$

Note: the sum is stated directly in terms of `Nat.card (lift_union_conj_noncenter_...)`,
which (by `card_noncenter_C_eq_noncenter_MaximalAbelianSubgroup_mul_noncenter_ConjClassOfSet`)
already equals `|A_i^*| ⬝ |C_i^*|`; this matches Butler's formula without an extra factor.
We also add the `[DecidableEq F] [IsAlgClosed F]` hypotheses that every supporting lemma in this
file (the partition of `G \ Z` into noncentral maximal abelian subgroups) already requires.
-/
theorem card_noncenter_fin_subgroup_eq_sum_card_noncenter_mul_index_normalizer {F : Type*}
  [Field F] [DecidableEq F] [IsAlgClosed F]
  (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G) :
    Nat.card (G.carrier \ (center SL(2,F)).carrier : Set SL(2,F))
      = ∑ lift_A : Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G),
    Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G lift_A) := by
  simp only [Nat.card_coe_set_eq]
  have hpieces_finite : ∀ A : noncenter_MaximalAbelianSubgroupsOf G,
      (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G A).Finite := by
    intro A
    have hsub : union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G A ⊆
        G.carrier \ (center SL(2,F) : Set SL(2,F)) := by
      rw [union_noncenter_C_eq_G_diff_center G]
      exact Set.subset_iUnion (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G) A
    exact (Set.toFinite (G.carrier : Set SL(2,F))).subset (hsub.trans Set.diff_subset)
  have hlift_pieces_finite : ∀ q : Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G),
      (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G q).Finite := by
    intro q
    induction q using Quotient.inductionOn with
    | h A => exact hpieces_finite A
  have hlift_pairwise : Pairwise (Disjoint on
      lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G) := by
    intro q₁ q₂ hne
    induction q₁ using Quotient.inductionOn with
    | h A =>
      induction q₂ using Quotient.inductionOn with
      | h B =>
        simp only [Function.onFun]
        apply union_conjClasses_noncenter_pairwise_disjoint_of_not_equiv G center_le_G
        intro hAB
        exact hne (Quotient.eq.mpr hAB)
  have key := Set.ncard_iUnion_of_finite hlift_pieces_finite hlift_pairwise
  rw [← union_lift_union_conj_noncenter_MaximalAbelianSubgroupsOf_eq_G_diff_center G,
    finsum_eq_sum_of_fintype] at key
  exact key

-- todo: probably somewhere in mathlib, but I can't find it.
lemma center_conj {G : Type*} [Group G] (x : G) (y: G) :
  x ∈ center G ↔ y * x * y⁻¹ ∈ center G := by
  simp only [mem_center_iff]
  constructor <;> intro h z
  · have := h (y⁻¹ * z * y)
    calc z * (y * x * y⁻¹)
        = y * (y⁻¹ * z * y * x) * y⁻¹ := by group
      _ = y * (x * (y⁻¹ * z * y)) * y⁻¹ := by rw [this]
      _ = y * x * y⁻¹ * z := by group
  · have := h (y * z * y⁻¹)
    calc z * x
        = y⁻¹ * (y * z * y⁻¹ * (y * x * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * x * y⁻¹) * (y * z * y⁻¹)) * y := by rw [this]
      _ = x * z := by group

/-- Lemma 2.5 N_G(A) = N_G(A*)
Oddly it doesn't need any assumption about A being maximal or abelian.
-/
lemma normalizer_noncentral_eq {F : Type*} [Field F] (A G : Subgroup SL(2,F)) [Finite G]:
  normalizer (A.subgroupOf G : Set ↥G) = normalizer (noncenter (A.subgroupOf G)) := by
  ext x
  simp only [mem_normalizer_iff]
  constructor
  · intro h a
    rw [Subgroup.mem_noncenter, Subgroup.mem_noncenter, h a, center_conj a x]
  · intro h n
    by_cases hn : n ∈ center (↥G)
    · have hx : x * n * x⁻¹ = n := by
        rw [mem_center_iff] at hn
        rw [hn x]; group
      rw [hx]
    · have hcn : x * n * x⁻¹ ∉ center (↥G) := fun hc => hn ((center_conj n x).mpr hc)
      have key := h n
      rw [Subgroup.mem_noncenter, Subgroup.mem_noncenter] at key
      constructor
      · intro hnK; exact (key.mp ⟨hnK, hn⟩).1
      · intro hcK; exact (key.mpr ⟨hcK, hcn⟩).1

/- Lemma Let `Q` be a `p`-Sylow subgroup of `G` then $N_G(Q \sqcup Z) = N_G(Q)$-/
lemma normalizer_Sylow_join_center_eq_normalizer_Sylow {F : Type*} [Field F] {p : ℕ}
[Fact (Nat.Prime p)] [CharP F p] (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G) :
  normalizer (map G.subtype Q.toSubgroup ⊔ center SL(2,F) : Set SL(2,F)) =
    normalizer (map G.subtype Q.toSubgroup : Set SL(2,F)) := by
  have hp : Nat.Prime p := Fact.out
  set H := map G.subtype Q.toSubgroup with hHdef
  have hIsPH : IsPGroup p H := Q.isPGroup'.map G.subtype
  -- Note: `⊔` in the statement is elaborated at the level of `Set SL(2,F)`, i.e. it is
  -- ordinary set union of the underlying carriers, not the subgroup join.
  have hnegone_center : (-1 : SL(2,F)) ∈ center SL(2,F) := by
    rw [center_SL2_eq_Z F]; exact neg_one_mem_Z
  have hcentral : ∀ y : SL(2,F), y * (-1 : SL(2,F)) * y⁻¹ = -1 := by
    intro y
    rw [mem_center_iff.mp hnegone_center y, mul_inv_cancel_right]
  by_cases hp2 : p = 2
  · -- In characteristic 2, `-I = I`, so the center of `SL(2,F)` is absorbed into `H`.
    have h2 : (2 : F) = 0 := by
      have hcast : ((p : ℕ) : F) = 0 := CharP.cast_eq_zero F p
      rw [hp2] at hcast
      exact_mod_cast hcast
    have hnegone_eq_one : (-1 : SL(2,F)) = 1 :=
      (SpecialLinearGroup.neg_one_eq_one_of_two_eq_zero h2).symm
    have hSetEq : (H ⊔ center SL(2,F) : Set SL(2,F)) = (H : Set SL(2,F)) := by
      ext x
      simp only [Set.sup_eq_union, Set.mem_union, SetLike.mem_coe]
      constructor
      · rintro (hx | hx)
        · exact hx
        · rw [center_SL2_eq_Z F, mem_Z_iff] at hx
          rcases hx with rfl | rfl
          · exact H.one_mem
          · rw [hnegone_eq_one]; exact H.one_mem
      · intro hx; exact Or.inl hx
    rw [hSetEq]
  · -- `p` is odd, so `-1 ∉ H` and adjoining the center only ever adds the single point `-1`.
    have hNeZero : NeZero (2 : F) := by
      constructor
      intro h2
      apply hp2
      have hcast2 : ((2 : ℕ) : F) = (0 : F) := by exact_mod_cast h2
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp hcast2
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd
    have hnegone_not_mem_H : (-1 : SL(2,F)) ∉ H := by
      intro hmem
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hIsPH) (⟨-1, hmem⟩ : H)
      rw [orderOf_mk, orderOf_neg_one_eq_two] at hk
      rcases Nat.eq_zero_or_pos k with hk0 | hk0
      · rw [hk0, pow_zero] at hk
        exact absurd hk (by norm_num)
      · have hpk : p ∣ p ^ k := dvd_pow_self p hk0.ne'
        rw [← hk] at hpk
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hpk)
    ext y
    rw [mem_set_normalizer_iff, mem_normalizer_iff]
    have hconj_eq_iff : ∀ a b : SL(2,F), y * a * y⁻¹ = y * b * y⁻¹ ↔ a = b := by
      intro a b
      constructor
      · intro h; exact mul_left_cancel (mul_right_cancel h)
      · intro h; rw [h]
    have hyn_eq_negone_iff : ∀ n : SL(2,F), y * n * y⁻¹ = -1 ↔ n = -1 := by
      intro n; rw [← hcentral y, hconj_eq_iff, hcentral y]
    have hyn_eq_one_iff : ∀ n : SL(2,F), y * n * y⁻¹ = 1 ↔ n = 1 := by
      intro n
      have h1' : y * (1 : SL(2,F)) * y⁻¹ = 1 := by group
      rw [← h1', hconj_eq_iff, h1']
    constructor
    · intro hy n
      have key := hy n
      simp only [Set.sup_eq_union, Set.mem_union, SetLike.mem_coe, center_SL2_eq_Z F,
        mem_Z_iff] at key
      constructor
      · intro hn
        rcases key.mp (Or.inl hn) with h1 | h1 | h1
        · exact h1
        · rw [h1]; exact H.one_mem
        · exfalso
          apply hnegone_not_mem_H
          rw [← (hyn_eq_negone_iff n).mp h1]
          exact hn
      · intro hc
        rcases key.mpr (Or.inl hc) with h1 | h1 | h1
        · exact h1
        · rw [h1]; exact H.one_mem
        · exfalso
          apply hnegone_not_mem_H
          rw [h1] at hc
          rw [hcentral y] at hc
          exact hc
    · intro hy n
      simp only [Set.sup_eq_union, Set.mem_union, SetLike.mem_coe, center_SL2_eq_Z F, mem_Z_iff]
      constructor
      · rintro (hn | rfl | rfl)
        · exact Or.inl ((hy n).mp hn)
        · exact Or.inr (Or.inl (by group))
        · exact Or.inr (Or.inr (hcentral y))
      · rintro (hc | h1 | h1)
        · exact Or.inl ((hy n).mpr hc)
        · exact Or.inr (Or.inl ((hyn_eq_one_iff n).mp h1))
        · exact Or.inr (Or.inr ((hyn_eq_negone_iff n).mp h1))



#min_imports
