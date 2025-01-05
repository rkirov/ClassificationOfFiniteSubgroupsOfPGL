import Mathlib
import ClassificationOfSubgroups.Ch1_PropertiesOfSpecialLinearGroup


set_option linter.style.longLine true
set_option autoImplicit false

-- /home/alex-brodbelt/Desktop/Projects/Lean/Dissertation/ClassificationOfSubgroups/ClassificationOfSubgroups/Ch1_PropertiesOfSpecialLinearGroup.lean
-- namespace test

-- variable {G : Type*} [Group G] ( H : Subgroup G) (hHMax : Maximal (Subgroup.IsCommutative) H)

-- example : H.IsCommutative := hHMax.prop

-- example : ∀ J, H < J → ¬J.IsCommutative := by
--   intro J hJ
--   contrapose! hJ
--   exact Maximal.not_gt hHMax hJ

-- example : ∀ (J : Subgroup G),(J.IsCommutative ∧ (∀ K, J < K → ¬K.IsCommutative)) →
--     Maximal (Subgroup.IsCommutative) J := by
--   intro J hJ
--   rw [Maximal]
--   use hJ.left
--   replace hJ := hJ.right
--   intro K hK hJK
--   specialize hJ K
--   if h: J = K then
--     rw [h]
--   else
--     exact (hJ (lt_of_le_of_ne hJK h) hK).elim

-- end test

namespace ElementaryAbelian

def IsElementaryAbelian (p : ℕ) [Fact (Nat.Prime p)] (G : Type*) [CommGroup G] : Prop  :=
  ∀ g : G, g ^ p = 1

/- If `G` is elementary abelian then G is a `p`-Group -/
theorem IsPSubgroup_of_IsElementaryAbelian {G : Type*} [CommGroup G] { p : ℕ } [Fact (Nat.Prime p)]
 (hG : IsElementaryAbelian p G) : IsPGroup p G := fun g => ⟨1, by rw [pow_one, hG]⟩

end ElementaryAbelian

namespace MaximalAbelian

open Subgroup

def IsMaximalAbelian (G : Type*) [Group G] (H : Subgroup G) : Prop := Maximal (IsCommutative) H

def MaximalAbelianSubgroups' { G : Type*} [Group G](H : Subgroup G) : Set (Subgroup H) :=
  { K : Subgroup H | @IsMaximalAbelian H _ K}

def MaximalAbelianSubgroups { L : Type*} [Group L] (G : Subgroup L) : Set (Subgroup L) :=
  { K : Subgroup L | IsMaximalAbelian G (K.subgroupOf G) ∧ K ≤ G}

end MaximalAbelian

namespace SpecialLinearGroup

universe u

variable (F : Type u) [Field F]

open Matrix MatrixGroups Subgroup MaximalAbelian

instance : Group SL(2,F) := by infer_instance

/- Let G be an arbitrary finite subgroup of SL(2, F) containing Z(SL(2, F)) -/
variable {G : Type*} (G : Subgroup (SL(2,F))) [Finite G] (hG : center (SL(2, F)) ≤ G)

namespace IsPGroup

/- Lemma 2.1. If G is a finite group of order pm where p is prime and m > 0,
then p divides |Z(G)|.-/
lemma p_dvd_card_center {H : Type*} {p : ℕ} (hp:  Nat.Prime p) [Group H] [Finite H] [Nontrivial H]
  (hH : IsPGroup p H) : p ∣ Nat.card (center H) := by
  let inst : Fact (Nat.Prime p) := by exact { out := hp }
  have card_H_eq_pow_prime : ∃ n > 0, Nat.card H = p ^ n := by rwa [← hH.nontrivial_iff_card]
  suffices ∃ k > 0, Nat.card (center H) = p ^ k by
    obtain ⟨k, kpos, hk⟩ := this
    use p^(k-1)
    rw [hk, ← Nat.pow_add_one', Nat.sub_add_cancel]
    linarith
  obtain ⟨n, npos, hn⟩ := card_H_eq_pow_prime
  exact IsPGroup.card_center_eq_prime_pow hn npos

end IsPGroup

/- Lemma 2.2: Every finite subgroup of a multiplicative group of a field is cyclic. -/
lemma lemma_2_2 (H : Subgroup Fˣ) [Finite H]: IsCyclic H := subgroup_units_cyclic H

open SpecialSubgroups

lemma mem_centralizer_self {G : Type*} [Group G] (x : G) : x ∈ centralizer {x} := by
  rintro y ⟨rfl⟩
  rfl

lemma IsCommutative_iff {G : Type*} [Group G] (H : Subgroup G) :
  IsCommutative H ↔ ∀ x y : H, x * y = y * x := by
  constructor
  · intro h x y
    have := @mul_comm_of_mem_isCommutative G _ H h x y (by simp) (by simp)
    exact SetLike.coe_eq_coe.mp this
  · intro h
    rw [← @le_centralizer_iff_isCommutative]
    intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    simp at hx
    specialize h ⟨x, hx⟩ ⟨y, hy⟩
    simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq] at h
    exact h

-- lemma Subgroup.coe_mul
lemma inf_IsCommutative_of_IsCommutative_left {G : Type*} [ Group G] (H K : Subgroup G)
  (hH : IsCommutative H) : IsCommutative (H ⊓ K) := by
  rw [IsCommutative_iff]
  intro x y
  have H_meet_K_le_H : H ⊓ K ≤ H := inf_le_left
  have x_in_H : (x : G) ∈ H := H_meet_K_le_H <| SetLike.coe_mem _
  have y_in_H : (y : G) ∈ H := H_meet_K_le_H <| SetLike.coe_mem _
  have := @mul_comm_of_mem_isCommutative G _ H hH x y x_in_H y_in_H
  exact SetLike.coe_eq_coe.mp this

lemma IsCommutative_of_IsCommutative_subgroupOf {G : Type*} [ Group G ] (H K : Subgroup G)
  (hH : IsCommutative (H.subgroupOf K)) : IsCommutative (H ⊓ K) := by
  rw [IsCommutative_iff] at hH ⊢
  intro x y
  have x_in_K : (x : G) ∈ K := x.property.right
  have y_in_K : (y : G) ∈ K := y.property.right
  have x_in_H_subgroupOf_K : ⟨x, x_in_K⟩ ∈ (H.subgroupOf K) := by
    simp [mem_subgroupOf]
    exact x.property.left
  have y_in_H_subgroupOf_K : ⟨y, y_in_K⟩ ∈ (H.subgroupOf K) := by
    simp [mem_subgroupOf]
    exact y.property.left
  specialize hH ⟨⟨x, x_in_K⟩, x_in_H_subgroupOf_K⟩ ⟨⟨y, y_in_K⟩, y_in_H_subgroupOf_K⟩
  simp [SetLike.coe_eq_coe] at hH
  exact SetLike.coe_eq_coe.mp hH



#check subgroupOf_isCommutative


lemma ne_union_left_of_ne {X : Type*} (A B : Set X)(not_B_le_A : ¬ B ≤ A) : A ⊂ A ∪ B := by
  rw [Set.ssubset_def]
  split_ands
  exact Set.subset_union_left
  intro h
  rw [Set.union_subset_iff] at h
  simp_rw [subset_refl, true_and] at h
  contradiction


omit [Finite G] in
/- Theorem 2.3 (i) If x ∈ G\Z then we have CG (x) ∈ M. -/
theorem centralizer_meet_G_of_noncentral_in_MaximalAbelianSubgroups [IsAlgClosed F] [DecidableEq F]
  (x : SL(2,F))
  (hx : x ∈ (G.carrier \ (center SL(2,F)))) :
  centralizer {x} ⊓ G ∈ MaximalAbelianSubgroups G := by
  obtain ⟨x_in_G, x_not_in_Z⟩ := hx
  simp at x_not_in_Z
  have IsCommutative_centralizer_S := IsCommutative_centralizer_of_not_mem_center F x x_not_in_Z
  dsimp [MaximalAbelianSubgroups]
  split_ands
  · rw [inf_subgroupOf_right]
    apply subgroupOf_isCommutative
  · rintro J hJ hx j j_in_J
    rw [inf_subgroupOf_right, mem_subgroupOf, @mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    have x_in_J : ⟨x, x_in_G⟩ ∈ J := by
      apply hx
      apply mem_subgroupOf.mpr
      simp
      split_ands
      · exact mem_centralizer_self x
      · exact x_in_G
    have := @mul_comm_of_mem_isCommutative G _ J hJ (⟨x, x_in_G⟩ : ↥G) j x_in_J j_in_J
    exact SetLike.coe_eq_coe.mpr this
  exact inf_le_right

namespace MaximalAbelianSubgroup

theorem subset_centralizer_meet {G : Type*} [Group G] (M H : Subgroup G)
  (hM : M ∈ MaximalAbelianSubgroups H) (x : G) (x_in_M : x ∈ M) :
  (M : Set G) ⊆ centralizer {x} ⊓ H := by
  intro y y_in_M
  simp [MaximalAbelianSubgroups, IsMaximalAbelian, maximal_iff] at hM
  obtain ⟨⟨hM, -⟩, M_le_H⟩ := hM
  have M_meet_H_IsCommutative :
    IsCommutative (M ⊓ H) := IsCommutative_of_IsCommutative_subgroupOf M H hM
  have M_le_M_meet_H : M ≤ M ⊓ H := Lattice.le_inf M M H (fun ⦃x⦄ a ↦ a) M_le_H
  have x_in_M_meet_H : x ∈ M ⊓ H := M_le_M_meet_H x_in_M
  have y_in_M_meet_H : y ∈ M ⊓ H := M_le_M_meet_H y_in_M
  have :=
    @mul_comm_of_mem_isCommutative G _ (M ⊓ H) M_meet_H_IsCommutative x y x_in_M_meet_H y_in_M_meet_H
  simp
  split_ands
  · rw [mem_centralizer_iff]
    simp
    exact this
  · exact M_le_H y_in_M



lemma not_le_of_ne {G : Type*} [Group G] (A B H : Subgroup G)
  (hA : A ∈ MaximalAbelianSubgroups H) (hB : B ∈ MaximalAbelianSubgroups H) (A_ne_B : A ≠ B):
  ¬ B ≤ A  := by
  intro h
  obtain ⟨⟨hA, -⟩, A_le_H⟩ := hA
  obtain ⟨⟨-, B_maximal⟩, B_le_H⟩ := hB
  have : B.subgroupOf H ≤ A.subgroupOf H := by
    rw [← @map_subtype_le_map_subtype]
    simp
    exact inf_le_of_left_le h
  specialize B_maximal hA this
  have contr : A.subgroupOf H = B.subgroupOf H := by
    rw [← sup_le_inf]
    apply le_trans (b := A.subgroupOf H)
    apply sup_le (le_refl _) this
    apply le_inf (le_refl _) B_maximal
  simp at contr
  have A_meet_G_eq_A : A ⊓ H = A := inf_of_le_left A_le_H
  have B_meet_G_eq_B : B ⊓ H = B := inf_of_le_left B_le_H
  rw [A_meet_G_eq_A, B_meet_G_eq_B] at contr
  contradiction

omit [Finite G] in
lemma le_cen_of_mem {G : Type*} [Group G] (A H : Subgroup G) (hA : A ∈ MaximalAbelianSubgroups H)
  (x : G) (x_in_A : x ∈ A) : A ≤ centralizer {x} := by
  intro a a_in_A
  obtain ⟨⟨A_IsCommutative', -⟩, A_le_G⟩ := hA
  have hA : IsCommutative (A ⊓ H) := IsCommutative_of_IsCommutative_subgroupOf A H A_IsCommutative'
  have A_meet_G_eq_A : A ⊓ H = A := inf_of_le_left A_le_G
  have := @mul_comm_of_mem_isCommutative G _ A (A_meet_G_eq_A ▸ hA) x a x_in_A a_in_A
  simp [mem_centralizer_iff]
  exact this


lemma lt_cen_meet_G {G : Type*} [Group G] (A B H : Subgroup G) (hA : A ∈ MaximalAbelianSubgroups H)
  (hB : B ∈ MaximalAbelianSubgroups H) (A_ne_B: A ≠ B) (x : G) (x_in_A : x ∈ A) (x_in_B : x ∈ B):
  A < centralizer {x} ⊓ H := by
  suffices (A : Set G) < centralizer {x} ⊓ H by exact this
  apply lt_of_lt_of_le (b := (A : Set G) ∪ B)
  · have not_B_le_A : ¬ B ≤ A := not_le_of_ne A B H hA hB A_ne_B
    rw [Set.lt_iff_ssubset, Set.ssubset_iff_subset_ne]
    split_ands
    · exact Set.subset_union_left
    · symm
      apply ne_of_not_le
      intro h
      simp at h
      contradiction
  · simp
    split_ands
    · exact @le_cen_of_mem G _ A H hA x x_in_A
    · exact @le_cen_of_mem G _ B H hB x x_in_B
    · exact hA.right
    · exact hB.right

open Pointwise

def center_mul  {G : Type* } [Group G] (H : Subgroup G) : Subgroup G where
  carrier := (center G : Set G) * (H : Set G)
  mul_mem' := by
    intro x y ⟨z₁, hz₁, a₁, ha₁, h₁⟩ ⟨z₂, hz₂, a₂, ha₂, h₂⟩
    simp at h₁ h₂
    rw [← h₁, ← h₂, mul_assoc, ← mul_assoc a₁, Eq.symm (hz₂.comm a₁)]
    use z₁ * z₂
    split_ands
    · exact mul_mem hz₁ hz₂
    use a₁ * a₂
    split_ands
    · exact mul_mem ha₁ ha₂
    group
  one_mem' := by
    use 1
    split_ands
    · exact one_mem (center G)
    use 1
    split_ands
    · apply one_mem
    simp_rw [mul_one]
  inv_mem' := by
    intro x ⟨z, hz, a, ha, h⟩
    simp [Set.mem_mul]
    use z⁻¹
    split_ands
    · exact (Subgroup.inv_mem_iff (center G)).mpr hz
    use a⁻¹
    split_ands
    · exact (Subgroup.inv_mem_iff H).mpr ha
    simp at h
    rw [@eq_inv_iff_mul_eq_one, ← h, mul_assoc, ← mul_assoc a⁻¹, Eq.symm (hz.comm a⁻¹)]
    group

lemma center_mul_eq_mul_center {G : Type* } [Group G] (H : Subgroup G) :
  (H : Set G) * (center G) = (center G) * H := by
  exact set_mul_normal_comm (↑H) (center G)

-- lemma center_mul_IsComm {G : Type* } [Group G] (H : Subgroup G) :
--   IsCommutative (center G ⊔ H) := by
--   rw [@IsCommutative_iff]


lemma sup_center_carrier_eq_mul {G : Type* } [Group G] (H : Subgroup G) :
  (((H ⊔ center G) : Subgroup G) : Set G) = (H : Set G) * center G := by
  exact mul_normal H (center G)
  -- ext x
  -- constructor
  -- · intro hx
  --   rw [@SetLike.mem_coe] at hx
  --   rw [@sup_eq_closure_mul] at hx
  --   rw [mem_closure] at hx
  --   have H_mul_cen_subs : (H : Set G) * (center G) ⊆ (center_mul H) := by simp [center_mul, center_mul_eq_mul_center]
  --   specialize hx (center_mul H) H_mul_cen_subs
  --   simp [center_mul] at hx
  --   rw [center_mul_eq_mul_center]
  --   exact hx
  -- · intro hx
  --   rw [@mul_normal]
  --   exact hx
lemma center_mul_subset_center_mul {G : Type*} [Group G] (A : Subgroup G) :
  ((center G) :  Set G) * A ⊆ (center_mul A) := by simp [center_mul]

lemma IsComm_of_center_join_IsComm {G : Type* } [Group G] (H : Subgroup G)
  (hH : IsCommutative H) : IsCommutative (center G ⊔ H) :=  by
  rw [IsCommutative_iff]
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [@sup_eq_closure_mul, mem_closure] at hx hy
  specialize hx (center_mul H) (center_mul_subset_center_mul H)
  specialize hy (center_mul H) (center_mul_subset_center_mul H)
  rcases hx with ⟨z₁, hz₁, h₁, hh₁, h₁'⟩
  rcases hy with ⟨z₂, hz₂, h₂, hh₂, h₂'⟩
  simp at hz₁ hz₂ h₁' h₂' ⊢
  rw [← h₁', ← h₂', mul_assoc, ← mul_assoc h₁, Eq.symm (hz₂.comm h₁),
   mul_assoc z₂, mul_assoc z₂, ← mul_assoc h₂, Eq.symm (hz₁.comm h₂),
   @mul_comm_of_mem_isCommutative G _ H hH h₁ h₂ hh₁ hh₂, ← mul_assoc,
   Eq.symm (hz₂.comm z₁)]
  group


lemma center_le (G : Type*) [Group G] (A H : Subgroup G) (hA : A ∈ MaximalAbelianSubgroups H)
  (hH : center G ≤ H) : center G ≤ A := by
  by_contra h
  rw [@SetLike.not_le_iff_exists] at h
  -- We will yield that K is less than or equal to A
  have contr := hA.left.right
  let K := (center G ⊔ A).subgroupOf H
  have A_IsComm : IsCommutative A :=
    inf_of_le_left hA.right ▸ IsCommutative_of_IsCommutative_subgroupOf A H hA.left.left
  have A_join_cen_IsComm : IsCommutative (center G ⊔ A) := IsComm_of_center_join_IsComm _ A_IsComm
  have K_IsComm : IsCommutative K := subgroupOf_isCommutative (center G ⊔ A)
  have A_le_cen_join_A : A.subgroupOf H ≤ (center G ⊔ A).subgroupOf H := by
    simp [← map_subtype_le_map_subtype, hA.right]
  specialize contr K_IsComm A_le_cen_join_A
  obtain ⟨z, hz, z_not_in_A⟩ := h
  have z_in_H : z ∈ H := by apply hH hz
  have : ¬ K ≤ A.subgroupOf H := by
    simp [K, @SetLike.not_le_iff_exists]
    use z, z_in_H
    split_ands
    · simp [@mem_subgroupOf]; exact mem_sup_left hz
    · simp [@mem_subgroupOf]; exact z_not_in_A
  contradiction

end MaximalAbelianSubgroup


open MaximalAbelianSubgroup

/- Theorem 2.3 (ii) For any two distinct subgroups A and B of M, we have A ∩ B = Z. -/
omit [Finite G] in
theorem theorem_2_6_ii [IsAlgClosed F] [DecidableEq F] (A B : Subgroup SL(2,F))
  (hA : A ∈ MaximalAbelianSubgroups G) (hB : B ∈ MaximalAbelianSubgroups G) (A_ne_B: A ≠ B)
  (hG : center SL(2,F) ≤ G) : A ⊓ B = center SL(2,F) := by
  ext x
  constructor
  · rintro ⟨x_in_A, x_in_B⟩
    simp at x_in_A x_in_B
    by_cases hx : x ∈ G.carrier \ (center SL(2,F))
    · have cen_meet_G_in_MaximalAbelianSubgroups :=
        centralizer_meet_G_of_noncentral_in_MaximalAbelianSubgroups F G x hx
      obtain ⟨⟨cen_meet_G_IsCommutative, _h⟩, -⟩ :=
        cen_meet_G_in_MaximalAbelianSubgroups
      simp at cen_meet_G_IsCommutative
      have cen_meet_G_le_A : centralizer {x} ⊓ G ≤ A := by
        suffices (centralizer {x}).subgroupOf G ≤ A.subgroupOf G by
          simp [← @map_subtype_le_map_subtype] at this
          exact this
        -- apply maximality of A
        apply hA.left.right
        exact cen_meet_G_IsCommutative
        simp [← @map_subtype_le_map_subtype]
        rw [inf_of_le_left hA.right]
        exact @le_cen_of_mem SL(2,F) _ A G hA x x_in_A
        -- obtain a contradiction
      have not_cen_meet_G_le_A :=
        not_le_of_lt <| @lt_cen_meet_G SL(2,F) _ A B G hA hB A_ne_B x x_in_A x_in_B
      contradiction
    · simp at hx
      specialize hx (hA.right x_in_A)
      exact hx
  · intro hx
    have cen_le_A := @center_le SL(2,F) _ A G hA hG
    have cen_le_B := @center_le SL(2,F) _ B G hB hG
    exact le_inf cen_le_A cen_le_B hx


/- Theorem 2.3 (iii) An element A of M is either a cyclic group whose order is relatively prime
to p, or of the form Q × Z where Q is an elementary abelian Sylow p-subgroup
of G. -/
-- theorem theorem_2_6_iii_a
--   (A : Subgroup G)
--   (hA : A ∈ MaximalAbelianSubgroups G)
--   (h : ¬ (IsCyclic A ∧ Nat.Coprime (Nat.card A) p)) :
--   ∃ p : ℕ, Nat.Prime p → ∃ Q : Sylow p G, ElementaryAbelian.IsElementaryAbelian  p  Q.toSubgroup → Nonempty (A ≃* (Q.toSubgroup.prod (center SL(2,F)))) := by sorry

/- Theorem 2.3 (iv a) If A ∈ M and |A| is relatively prime to p, then we have [NG (A) : A] ≤ 2. -/
theorem theorem_2_3_iv_a (A : Subgroup SL(2,F)) (hA : A ∈ MaximalAbelianSubgroups G) (hA' : Nat.Coprime (Nat.card A) p) : A.normalizer.index ≤ 2 := by sorry

/- Theorem 2.3 (iv b) Furthermore, if [NG (A) : A] = 2, then there is an element y of NG (A)\A such that, yxy⁻¹ = x⁻¹  for all x ∈ A. -/
theorem theorem_2_3_iv_b (A : Subgroup SL(2,F)) (hA : A ∈ MaximalAbelianSubgroups G) (hA' : Nat.Coprime (Nat.card A) p) (hNA : A.normalizer.index = 2)
  (x : A) : ∃ y ∈ A.normalizer.carrier \ A, y * x * y⁻¹ = x⁻¹ := by sorry

/- Theorem 2.3 (v a) Let Q be a Sylow p-subgroup of G. If Q = { I_G }, then there is a cyclic subgroup K of G such that N_G (Q) = Q K.  -/
-- def theorem_2_6_v_a { p : ℕ }
--   (hp : Nat.Prime p)
--   (Q : Sylow p G)
--   (h : Q.toSubgroup ≠ ⊥) :
--   ∃ K : Subgroup G, IsCyclic K → ∃ φ : Q.toSubgroup.normalizer →* Q.toSubgroup.prod K := by sorry

/- Theorem 2.3 (v b)If |K| > |Z|, then K ∈ M. -/
theorem theorem_2_6_v_b { p : ℕ }
  (hp : Nat.Prime p)
  (Q : Sylow p G)
  (h : Q.toSubgroup ≠ ⊥)
  (K : Subgroup SL(2,F))
  (hK : IsCyclic K)
  (NG_iso_prod_QK : Q.toSubgroup.normalizer ≃* Q.toSubgroup.prod K)
  (h: Nat.card K > Nat.card (center SL(2,F))) :
  K ∈ MaximalAbelianSubgroups G := by sorry

/- Conjugacy of Maximal Abelian subgroups -/
/-
Definition. The set Ci = Clᵢ = {x Aᵢx⁻¹ : x ∈ G} is called the conjugacy class of
A ∈ M.
-/

/- Let Aᵢ* be the non-central part of Aᵢ ∈ M -/

/- let M∗ be the set of all Aᵢ* and let Cᵢ* be the conjugacy class of Aᵢ* .-/

/-
Clᵢ = {x Aᵢx⁻¹ : x ∈ G}

For some Ai ∈ M and A∗i ∈ M∗ let,
Ci = ⋃ x ∈ G, x * Aᵢ * x⁻¹, and Cᵢ* = ⋃ x ∈ G, x Aᵢ* x⁻¹

It’s evident that Cᵢ* = Cᵢ \ Z(SL(2,F)) and that there is a Cᵢ corresponding to each
Cᵢ . Clearly we have the relation, |Cᵢ*| = |Aᵢ*||Clᵢ*|
-/




end SpecialLinearGroup
