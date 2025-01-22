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

open Subgroup



structure ElementaryAbelian (p : ℕ) (G : Type*) [Group G] extends Subgroup G where
  is_comm : IsCommutative toSubgroup
  orderOf_eq : ∀ h : toSubgroup, h ≠ 1 → orderOf h = p


def IsElementaryAbelian {G : Type*} [Group G] (p : ℕ) (H : Subgroup G) : Prop :=
  IsCommutative H ∧ ∀ h : H, h ≠ 1 → orderOf h = p

lemma dvd_card_IsElementaryAbelian {G : Type*} [Group G] (p : ℕ) (H : Subgroup G)
  [Finite H] (hH : IsElementaryAbelian p H) (bot_lt_H: ⊥ < H) : p ∣ (Nat.card H) := by
  simp [@SetLike.lt_iff_le_and_exists] at bot_lt_H
  obtain ⟨h, h_in_H, h_ne_one⟩ := bot_lt_H
  have order_eq_p : @orderOf H _ ⟨h, h_in_H⟩ = p := by
    apply hH.right ⟨h, h_in_H⟩
    simp [h_ne_one]
  rw [← order_eq_p]
  let inst : Fintype (H :) := Fintype.ofFinite ↥H
  have order_dvd_card := @orderOf_dvd_card H _ _ ⟨h, h_in_H⟩
  simp at order_dvd_card ⊢
  exact order_dvd_card


lemma primeFac_IsElementaryAbelian_eq {G : Type*} [Group G] (p : ℕ)
  (hp : Nat.Prime p) (H : Subgroup G) [Finite H] (hH : IsElementaryAbelian p H) (bot_lt_H : ⊥ < H):
  Nat.primeFactors (Nat.card H) = {p} := by
  rw [@Finset.Subset.antisymm_iff]
  constructor
  -- Suppose the set of prime factors is not contained in {p}
  · by_contra! h
    rw [@Finset.not_subset] at h
    obtain ⟨q, hq, q_ne_p⟩ := h
    simp [← ne_eq] at q_ne_p
    rw [Nat.mem_primeFactors] at hq
    obtain ⟨hq, q_dvd_card, -⟩ := hq
    let Fintype_H : Fintype H := Fintype.ofFinite ↥H
    simp at q_dvd_card
    obtain ⟨x, order_eq_q⟩ := @exists_prime_orderOf_dvd_card H _ _ q ({out := hq}) q_dvd_card
    have q_ne_one : q ≠ 1 := Nat.Prime.ne_one hq
    have x_ne_one : x ≠ 1 := by
      intro h
      rw [← orderOf_eq_one_iff, order_eq_q] at h
      contradiction
    have order_eq_p : orderOf x = p := hH.right x x_ne_one
    absurd q_ne_p (order_eq_q ▸ order_eq_p)
    trivial
  · simp
    exact ⟨hp, dvd_card_IsElementaryAbelian p H hH bot_lt_H, Nat.ne_zero_iff_zero_lt.mpr Nat.card_pos⟩

lemma IsPGroup_of_IsElementaryAbelian {G : Type*} [Group G] (p : ℕ) (hp : Nat.Prime p)
  (H : Subgroup G) [Finite H] (hH : IsElementaryAbelian p H) (bot_lt_H : ⊥ < H):
  IsPGroup p H := by
  let inst : Fact (Nat.Prime p) := { out := hp }
  rw [IsPGroup.iff_card]
  have : Nat.primeFactors (Nat.card (H :)) = {p} :=
    @primeFac_IsElementaryAbelian_eq G _ p hp H _ hH bot_lt_H
  have card_primeFac_eq_one : (Nat.card ↥H).primeFactors.card = 1 := this ▸ rfl
  have card_eq_isPrimePow :=
    (@isPrimePow_iff_card_primeFactors_eq_one (Nat.card (H :))).mpr card_primeFac_eq_one
  rw [isPrimePow_nat_iff] at card_eq_isPrimePow
  obtain ⟨p', k, hp', zero_lt_k, card_eq⟩ := card_eq_isPrimePow
  have p'_dvd_card : p' ∣ Nat.card H :=
    card_eq.symm ▸ Dvd.dvd.pow (dvd_refl p') (ne_of_gt zero_lt_k)
  have p_eq_p' : p' ∈ (Nat.card ↥H).primeFactors := by
    rw [@Nat.mem_primeFactors]
    exact ⟨hp', p'_dvd_card, Nat.ne_zero_iff_zero_lt.mpr Nat.card_pos⟩
  simp [this] at p_eq_p'
  use k, p_eq_p'▸ card_eq.symm


namespace MaximalAbelian

def IsMaximalAbelian (G : Type*) [Group G] (H : Subgroup G) : Prop := Maximal (IsCommutative) H

def MaximalAbelianSubgroups { L : Type*} [Group L] (G : Subgroup L) : Set (Subgroup L) :=
  { K : Subgroup L | IsMaximalAbelian G (K.subgroupOf G) ∧ K ≤ G}

end MaximalAbelian

universe u

variable (F : Type u) [Field F]

open Matrix MatrixGroups Subgroup MaximalAbelian MulAut

instance : Group SL(2,F) := by infer_instance

/- Let G be an arbitrary finite subgroup of SL(2, F) containing Z(SL(2, F)) -/
variable {G : Type*} (G : Subgroup (SL(2,F))) [Finite G] (center_le_G : center (SL(2, F)) ≤ G)


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
lemma IsCyclic_of_finite_subgroup_units (H : Subgroup Fˣ) [Finite H] : IsCyclic H :=
  subgroup_units_cyclic H

open SpecialSubgroups


def f (D₀ : Subgroup SL(2,F)) (hD₀ : D₀ ≤ D F) : D₀ →* F :=
  (Units.coeHom F).comp ((D_iso_units F).toMonoidHom.comp (inclusion hD₀))
  -- toFun := fun d₀ ↦ d₀.1 0 0
  -- map_one' := by simp
  -- map_mul' := by
  --   rintro ⟨x, x_in_D₀⟩ ⟨y, y_in_D₀⟩
  --   rcases hD₀ x_in_D₀ with ⟨δ₁, rfl⟩
  --   rcases hD₀ y_in_D₀ with ⟨δ₁, rfl⟩
  --   simp [SpecialMatrices.d]

-- #check (MulEquiv.subgroupMap (conj x) H).symm.toMonoidHom

lemma Injective_f (D₀ : Subgroup SL(2,F)) (hD₀ : D₀ ≤ D F) [Finite D₀] :
  Function.Injective (f F D₀ hD₀) := by
  rintro ⟨x, x_in_D₀⟩ ⟨y, y_in_D₀⟩ δ₁_eq_δ₂'
  rcases hD₀ x_in_D₀ with ⟨δ₁, rfl⟩
  rcases hD₀ y_in_D₀ with ⟨δ₂, rfl⟩
  simp [SpecialMatrices.d, f,] at δ₁_eq_δ₂'
  congr
  exact Units.eq_iff.mp δ₁_eq_δ₂'

lemma finite_subgroup_D_IsCyclic (D₀ : Subgroup SL(2,F)) (hD₀ : D₀ ≤ D F) [Finite D₀] :
  IsCyclic D₀ := isCyclic_of_subgroup_isDomain (f F D₀ hD₀) (Injective_f F D₀ hD₀)

open SpecialSubgroups

lemma mem_centralizer_self {G : Type*} [Group G] (x : G) : x ∈ centralizer {x} := by
  rintro y ⟨rfl⟩
  rfl

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
theorem centralizer_meet_G_in_MaximalAbelianSubgroups_of_noncentral [IsAlgClosed F] [DecidableEq F]
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

theorem le_centralizer_meet {G : Type*} [Group G] (M H : Subgroup G)
  (hM : M ∈ MaximalAbelianSubgroups H) (x : G) (x_in_M : x ∈ M) :
  M ≤ centralizer {x} ⊓ H := by
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
    rw [← map_subtype_le_map_subtype]
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

lemma sup_center_carrier_eq_mul {G : Type* } [Group G] (H : Subgroup G) :
  (((H ⊔ center G) : Subgroup G) : Set G) = (H : Set G) * center G := by
  exact mul_normal H (center G)

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


lemma center_le (G : Type*) [Group G] (H A : Subgroup G) (hA : A ∈ MaximalAbelianSubgroups H)
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
    simp [K, SetLike.not_le_iff_exists]
    use z, z_in_H
    split_ands
    · simp [@mem_subgroupOf]; exact mem_sup_left hz
    · simp [@mem_subgroupOf]; exact z_not_in_A
  contradiction


omit [Finite G] in
lemma singleton_of_cen_eq_G (G : Type*) [Group G] (H : Subgroup G) (hH : H = center G) :
  MaximalAbelianSubgroups H = {center G} := by
  ext A
  have cen_le_G : center G ≤ H := by exact le_of_eq_of_le (id (Eq.symm hH)) fun ⦃x⦄ a ↦ a
  constructor
  · intro hA
    have cen_le_A := @center_le G _ H A hA cen_le_G
    have A_le_cen := hH ▸ hA.right
    -- exact could not finish it off
    have A_eq_cen : A = center G := le_antisymm A_le_cen cen_le_A
    simp [A_eq_cen]
  · rintro ⟨rfl⟩
    simp [MaximalAbelianSubgroups, IsMaximalAbelian]
    split_ands
    · exact subgroupOf_isCommutative (center G)
    · intro A _A_IsComm _cen_le_A
      simp_rw [← hH]
      simp only [subgroupOf_self, le_top]
    exact cen_le_G

lemma eq_center_of_card_le_two (A G : Subgroup SL(2,F)) (center_le_G : center SL(2,F) ≤ G) (hA : A ∈ MaximalAbelianSubgroups G): A = center SL(2,F) := by
  have cen_le_A := center_le SL(2,F) G A hA center_le_G
  have card_cen_eq_two : Nat.card (center SL(2,F)) = 2 := by sorry
  refine le_antisymm ?A_le_cen ?cen_le_A
  case A_le_cen =>
    have one_mem_A : 1 ∈ A := by exact Subgroup.one_mem A
    have neg_one_mem_A : -1 ∈ A := by
      apply cen_le_A (@center_SL2_F_eq_Z F _ _ ▸ neg_one_mem_Z F)
    sorry
  case cen_le_A => exact cen_le_A


end MaximalAbelianSubgroup


open MaximalAbelianSubgroup

/- Theorem 2.3 (ii) For any two distinct subgroups A and B of M, we have A ∩ B = Z. -/
omit [Finite G] in
theorem center_eq_meet_of_ne_MaximalAbelianSubgroups [IsAlgClosed F] [DecidableEq F]
  (A B : Subgroup SL(2,F)) (hA : A ∈ MaximalAbelianSubgroups G) (hB : B ∈ MaximalAbelianSubgroups G)
  (A_ne_B: A ≠ B)(hG : center SL(2,F) ≤ G) : A ⊓ B = center SL(2,F) := by
  ext x
  constructor
  · rintro ⟨x_in_A, x_in_B⟩
    simp at x_in_A x_in_B
    by_cases hx : x ∈ G.carrier \ (center SL(2,F))
    · have cen_meet_G_in_MaximalAbelianSubgroups :=
        centralizer_meet_G_in_MaximalAbelianSubgroups_of_noncentral F G x hx
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
    have cen_le_A := @center_le SL(2,F) _ G A hA hG
    have cen_le_B := @center_le SL(2,F) _ G B hB hG
    exact le_inf cen_le_A cen_le_B hx

-- lemma NeZero_neg_CharP [CharP F p]: ∀ (x : F), NeZero x ↔ p • (1 : F) ≠ x := by sorry

/- Theorem 2.3 (iii) An element A of M is either a cyclic group whose order is relatively prime
to p, or of the form Q × Z where Q is an elementary abelian Sylow p-subgroup
of G. -/
omit [Finite G] in
theorem IsCyclic_and_card_Coprime_CharP_of_center_eq {p : ℕ} (hp : Nat.Prime p) [C : CharP F p]
 (A : Subgroup SL(2,F)) (hA : A ∈ MaximalAbelianSubgroups G) (hG : G = center SL(2,F)) :
  IsCyclic A ∧ Nat.Coprime (Nat.card A) p := by
  rw [@singleton_of_cen_eq_G SL(2,F) _ G hG] at hA
  simp at hA
  rw [center_SL2_F_eq_Z] at hA
  rw [hA]
  split_ands
  · exact Z_IsCyclic F
  · by_cases h : p ≠ 2
    · have two_ne_zero : (2 : F) ≠ 0 := by
        intro h'
        have : ((2 : ℕ ) : F) = (2 : F) := by rfl
        rw [← this, @CharP.cast_eq_zero_iff F _ p C 2,
         Nat.prime_dvd_prime_iff_eq hp Nat.prime_two] at h'
        contradiction
      have NeZero_two : NeZero (2 : F) := { out := two_ne_zero }
      rw [card_Z_eq_two_of_two_ne_zero]
      rw [@Nat.coprime_two_left]
      exact Nat.Prime.odd_of_ne_two hp h
    · simp at h
      let C' : CharP F 2 := by exact CharP.congr p h
      have two_eq_zero : (2 : F) = 0 := by refine CharTwo.two_eq_zero
      rw [card_Z_eq_one_of_two_eq_zero F two_eq_zero]
      exact Nat.gcd_one_left p

open ElementaryAbelian
--  (h : ¬ (IsCyclic A ∧ Nat.Coprime (Nat.card A) p))
--   ∃ p : ℕ, Nat.Prime p → ∃ Q : Sylow p G, ElementaryAbelian.IsElementaryAbelian  p  Q.toSubgroup → Nonempty (A ≃* (Q.toSubgroup.prod (center SL(2,F)))) := by sorry

lemma center_not_mem [IsAlgClosed F] [DecidableEq F] (G : Subgroup SL(2,F)) (hG : center SL(2,F) ≠ G) : center SL(2,F) ∉ MaximalAbelianSubgroups G := by
  intro h
  by_cases h' : center SL(2,F) ≤ G
  · obtain ⟨x, x_in_G, x_not_in_cen⟩ := SetLike.exists_of_lt (lt_of_le_of_ne h' hG)
    have centra_ne_cen : centralizer {x} ⊓ G ≠ center SL(2,F) := by
      apply ne_of_gt
      rw [SetLike.lt_iff_le_and_exists]
      split_ands
      · exact le_inf (Subgroup.center_le_centralizer ({x} : Set SL(2,F))) h'
      · exact ⟨x, ⟨mem_centralizer_self x, x_in_G⟩, x_not_in_cen⟩
    have centra_mem_MaxAbSub :=
      centralizer_meet_G_in_MaximalAbelianSubgroups_of_noncentral F G x (Set.mem_diff_of_mem x_in_G x_not_in_cen)
    have cen_le_centra : center SL(2, F) ≤ centralizer {x} ⊓ G :=
      le_inf (center_le_centralizer {x}) h'
    have cen_le_centra' : (center SL(2, F)).subgroupOf G ≤ (centralizer {x} ⊓ G).subgroupOf G := by
      simp [← map_subtype_le_map_subtype]; rw [inf_of_le_left h']; exact center_le_centralizer {x}
    have centra_le_cen := h.left.right centra_mem_MaxAbSub.left.left cen_le_centra'
    simp [← map_subtype_le_map_subtype] at centra_le_cen
    absurd centra_ne_cen (le_antisymm centra_le_cen cen_le_centra)
    trivial
  · absurd h' h.right
    trivial

open SpecialSubgroups


omit [Finite G] in
lemma eq_centralizer_meet_of_center_lt [IsAlgClosed F] [DecidableEq F]
  (A : Subgroup SL(2,F)) (center_lt : center SL(2,F) < A) (hA : A ∈ MaximalAbelianSubgroups G) :
  ∃ x : SL(2,F), x ∈ G.carrier \ center SL(2,F) ∧ A = centralizer {x} ⊓ G := by
  rw [SetLike.lt_iff_le_and_exists] at center_lt
  obtain ⟨-, x, x_in_A, x_not_in_center⟩ := center_lt
  have hx : x ∈ G.carrier \ center SL(2,F) := Set.mem_diff_of_mem (hA.right x_in_A) x_not_in_center
  obtain ⟨⟨centra_meet_G_IsComm, -⟩, -⟩ :=
    centralizer_meet_G_in_MaximalAbelianSubgroups_of_noncentral F G x hx
  -- We show centralizer {x} ⊓ G ≤ A
  have A_le_centralizer_meet_G := (le_centralizer_meet A G hA x x_in_A)
  -- Note: solution provided by exact? does not work. Probably a bug?
  have A_le_centralizer_meet_G' : A.subgroupOf G ≤ (centralizer {x} ⊓ G).subgroupOf G := by
    simp [← map_subtype_le_map_subtype]
    exact le_trans inf_le_left <| le_trans A_le_centralizer_meet_G inf_le_left
  -- by using the maximality of A and using the fact A ≤ centralizer {x} ⊓ G
  have centralizer_meet_G_le_A := hA.left.right centra_meet_G_IsComm A_le_centralizer_meet_G'
  simp [← map_subtype_le_map_subtype] at centralizer_meet_G_le_A
  -- We show A = centralizer {x} ⊓ G
  exact ⟨x, hx, le_antisymm A_le_centralizer_meet_G centralizer_meet_G_le_A⟩


-- def g (x : SL(2,F)) (G A : Subgroup SL(2,F)) (hA : A ∈ MaximalAbelianSubgroups G) : A →* F where
--   toFun := fun a ↦
--   map_one' := by sorry
--   map_mul' := by sorry

#check (D_iso_units F).toMonoidHom
open MulAction Pointwise

-- def foo  {G : Type*} [Group G] (x : G) (H : Subgroup G): (MulAut.conj x • H) →* H := by sorry
theorem Units.coeHom_injective {M : Type*} [Monoid M] : Function.Injective (Units.coeHom M) := by
  intro x y h
  rw [Units.coeHom_apply, Units.coeHom_apply, ← Units.ext_iff] at h
  exact h

open Function Units




-- lemma order_fin_subgroup_units_eq_pow_char_sub_one { p : ℕ} (hp : Prime p) [CharP F p] (G : Subgroup SL(2,F)) (hc : conj c • D F = centralizer {x}) :
-- If a subgroup/group H is Elementary Abelian then the order of H is p ^ n for some n
-- ⟨t₁⟩ ≤ H of order p and is furthermore normal as H is abelian. Therefore, H ⧸ ⟨ t₁⟩  has order Nat.card H / p.
-- We can continue this process, take an element t₂ ≠ 1 of H ⧸ ⟨ t₁ ⟩ this element has order p and thus




lemma order_ne_char (F : Type*) [Field F] {p : ℕ} [hp' : Fact (Nat.Prime p)] [hC : CharP F p] :
  ∀ x : Fˣ, orderOf x ≠ p := by
  intro x
  by_contra H
  have := ExpChar.pow_prime_pow_mul_eq_one_iff p 1 1 (x : F)
  simp only [← H, pow_one, mul_one, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one x, Units.val_one,
    Units.val_eq_one, true_iff] at this
  exact hp'.out.ne_one (@orderOf_one Fˣ _ ▸ (this ▸ H)).symm

lemma dvd_pow_totient_sub_one_of_coprime {m p : ℕ} (hp : Nat.Prime p) (h : Nat.Coprime m p) :
  m ∣ p^Nat.totient m - 1 := by
  rw [← Nat.modEq_zero_iff_dvd]
  suffices p ^ m.totient ≡ 1 [MOD m] by
    rw [← add_zero (p ^ Nat.totient m), ← Nat.sub_self 1] at this
    nth_rewrite 3 [← zero_add 1] at this
    rw [← Nat.add_sub_assoc (le_refl _), Nat.sub_add_comm (one_le_pow₀ hp.one_le)] at this
    apply Nat.ModEq.add_right_cancel' 1 this
  exact Nat.ModEq.pow_totient h.symm
-- Alex's original approach inspired by a maths stack exchange was
-- the elements of the finite subgroup of the
-- finite subgroup of units of a field has order dividing p ^ k - 1 for some k ∈ ℕ
-- We show that a finite subgroup is contained in a finite field which is a subfield of
-- a possibly non-finite field. First, we take the minimal subfield 𝔽ₚ and adjoin all elements of G.
-- this extension is algebraic as every element is a solution to x^|G| - 1,
-- so the extension is algebraic, hence the field extension 𝔽ₚ(g₁, g₂, …, gₙ) is finite.
-- G ≤ 𝔽ₚ(g₁, g₂, …, gₙ)
-- Here formalized the argument by Mitchell
lemma coprime_card_fin_subgroup_of_inj_hom_group_iso_units {F G : Type*} [Field F] {p : ℕ}
  [hp' : Fact (Nat.Prime p)] [hC : CharP F p] [Group G] (H : Subgroup G) [Finite H]
  (f : H →* Fˣ) (hf : Injective f) :
  Nat.Coprime (Nat.card H) p := by
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hp'.out]
  have order_ne_p := @order_ne_char F _ p _ _
  contrapose! order_ne_p
  let H_fintype : Fintype H := Fintype.ofFinite ↥H
  simp only [Nat.card_eq_fintype_card] at order_ne_p
  obtain ⟨h, hh⟩ := @exists_prime_orderOf_dvd_card H _ _ p _ order_ne_p
  use f h
  rw [orderOf_injective f hf ↑h, ← hh]

instance TZ_Comm : CommGroup (T F ⊔ Z F :) := by
  rw [T_join_Z_eq_TZ F]
  let inst := IsCommutative_TZ F
  exact IsCommutative.commGroup (TZ F)

-- instance : CovariantClass (↥(T F ⊔ Z F)) (↥(T F ⊔ Z F)) (fun x1 x2 ↦ x1 * x2) fun x1 x2 ↦ x1 ≤ x2 := by sorry

-- instance TZ_DistribLattice : DistribLattice (T F ⊔ Z F :) := by
--   apply CommGroup.toDistribLattice
--   apply (TZ_Comm F)
-- lemma

lemma conj_ZT_eq_conj_Z_join_T {F : Type*} [Field F] (c : SL(2,F)):
  conj c • TZ F = conj c • T F ⊔ Z F := by
  rw [← TZ_eq_TZ']
  ext x
  constructor
  · rintro ⟨t, ⟨⟨t, ht, z, hz, rfl⟩, rfl⟩⟩
    simp at ht ⊢
    simp [← center_SL2_F_eq_Z] at hz ⊢
    rw [mul_assoc c, mul_assoc t, ← mem_center_iff.mp hz c⁻¹]
    rw [← SetLike.mem_coe, mul_normal]
    use c * t * c⁻¹
    constructor
    · simp [pointwise_smul_def, ht]
    use z
    constructor
    · exact hz
    group
  · rw [← SetLike.mem_coe, ← center_SL2_F_eq_Z, mul_normal]
    rintro ⟨y, hy, z, hz, rfl⟩
    simp [pointwise_smul_def] at hy ⊢
    obtain ⟨t, ht, rfl⟩ := hy
    use t * z
    constructor
    · simp only [TZ', mem_mk]
      use t
      constructor
      · exact ht
      use z
      constructor
      · exact (@center_SL2_F_eq_Z F _ _) ▸ hz
      rfl
    rw [mul_assoc c, mul_assoc t, ← mem_center_iff.mp hz c⁻¹]
    group

def conj_T_meet_G_eq_T_conj_G {F : Type*} [Field F] (c : SL(2,F)) (G : Subgroup SL(2,F)) (hG : center SL(2,F) ≤ G) :
  (conj c • T F ⊓ G:) ≃* (T F ⊓ conj c⁻¹ • G:) where
  toFun :=
    fun ⟨x, x_in_conj, x_in_G⟩ =>
      ⟨c⁻¹ * x * c,
      by
      rw [mem_inf]
      obtain ⟨t, ht, h⟩ := x_in_conj
      simp at h
      constructor
      · rw [← h]
        group
        exact ht
      · simp [pointwise_smul_def]
        exact x_in_G
      ⟩
  invFun :=
    fun ⟨t, ht, t_in_conj⟩ =>
      ⟨c * t * c⁻¹,
      by
      rw [mem_inf]
      obtain ⟨g, g_in_G, h⟩ := t_in_conj
      simp at h
      constructor
      · simp [pointwise_smul_def]
        exact ht
      · rw [← h]
        group
        exact g_in_G
      ⟩
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

  -- ext x
  -- constructor
  -- · rintro ⟨⟨t, ht, h⟩, x_in_G⟩
  --   simp at h x_in_G
  --   have key : t = c⁻¹ * x * c := by rw [← h]; group





  --   sorry
  -- · sorry


theorem IsCyclic_and_card_coprime_CharP_or_fin_prod_IsElementaryAbelian_le_T_of_center_ne
  [IsAlgClosed F] [DecidableEq F]  {p : ℕ} [Fact (Nat.Prime p)] [hC : CharP F p] [hG : Finite G]
  (A : Subgroup SL(2,F)) (hA : A ∈ MaximalAbelianSubgroups G)
  (center_le_G : center SL(2,F) ≤ G) (center_ne_G : G ≠ center SL(2,F)) :
  (IsCyclic A ∧ Nat.Coprime (Nat.card A) p) ∨
  (∃ Q₀ : Subgroup SL(2,F), Finite Q₀ ∧ Q₀ ≤ G ∧ A = Q₀ ⊔ Z F ∧ IsElementaryAbelian p Q₀) := by
  have center_ne_A : center SL(2,F) ≠ A :=
    Ne.symm (ne_of_mem_of_not_mem hA (center_not_mem F G center_ne_G.symm))
  have center_lt_A : center SL(2,F) < A :=
    lt_of_le_of_ne (center_le SL(2,F) G A hA center_le_G) center_ne_A
  -- Take the element that belongs to A but does not belong to Z
  -- We will use this element to show A = centralizer {x} ⊓ G
  obtain ⟨x, ⟨x_in_G, x_not_in_center⟩, A_eq_centra⟩ :=
    eq_centralizer_meet_of_center_lt F G A center_lt_A hA
  -- Once shown A = centralizer {x} ⊓ G and recalling x is conjugate to d δ or ± t τ
  -- We show the centralizer in each of these cases is conjugate to finite
  -- commutative subgroups of either D or TZ
  simp [center_SL2_F_eq_Z, ← ne_eq] at x_not_in_center
  obtain ⟨x_ne_one, x_ne_neg_one⟩ := x_not_in_center
  let inst : Finite A := A_eq_centra  ▸ Set.Finite.subset hG inf_le_right
  rcases SL2_IsConj_d_or_IsConj_t_or_IsConj_neg_t F x with
    (⟨δ, x_IsConj_d⟩ | ⟨τ, x_IsConj_t⟩ | ⟨τ, x_IsConj_neg_t⟩)
  -- x is conjugate to d δ
  · left
    have δ_ne_one : δ ≠ 1 := by rintro rfl; simp_all
    have δ_ne_neg_one : δ ≠ -1 := by rintro rfl; simp_all
    obtain ⟨c, c_smul_D_eq_centralizer⟩ :=
      conjugate_centralizers_of_IsConj (SpecialMatrices.d δ) x x_IsConj_d
    rw [centralizer_d_eq_D F δ δ_ne_one δ_ne_neg_one] at c_smul_D_eq_centralizer
    -- A = centralizer {x} ⊓ G ≤ centralizer {x}
    -- for some x ∈ G \ center SL(2,F)
    -- centralizer {x} is equal to MulAut conj c • centralizer {d δ}, so
    -- centralizer {x} is isomorphic to centralizer {d δ} equals D
    -- which itself is isomorphic to Fˣ
    -- given A is a finite subgroup of a group isomorphic to F
    -- A is Cyclic
    -- A is a subgroup of conj c • (D F)
    have A_le_conj_D :=
      le_trans (le_of_eq A_eq_centra) <|
      le_trans inf_le_left (le_of_eq c_smul_D_eq_centralizer.symm)
    -- compose the monoid homomorphisms of inclusions and isomorphisms
    -- `Fˣ *←  D F ←* conj • (D F) *← A`
    let f : A →* Fˣ :=
      ((D_iso_units F).toMonoidHom.comp
      (((MulEquiv.subgroupMap (conj c) (D F)).symm.toMonoidHom).comp
      (inclusion A_le_conj_D)))
    have hf : Function.Injective f := by
      dsimp [f]
      apply Injective.comp
      exact MulEquiv.injective (D_iso_units F)
      apply Injective.comp
      -- we construct the monoid homomorphism from the isomorphism
      exact MulEquiv.injective (MulEquiv.subgroupMap (conj c) (D F)).symm
      -- we construct the inclusion monoid homomorphism
      exact inclusion_injective A_le_conj_D
    -- `F *← Fˣ *← A`
    let f' : A →* F := (coeHom F).comp f
    have hf' : Injective f' := by
      dsimp [f']
      apply Injective.comp
      exact Units.coeHom_injective
      exact hf
    split_ands
    -- A is cyclic as it is it is finite and there exists an injective monoid homomorphism into F
    · exact isCyclic_of_subgroup_isDomain f' hf'
    -- cardinality of A is coprime to p, the characteristic of F as Fˣ has no element of order p
    -- after looking at the frobenius endomorphism
    · exact @coprime_card_fin_subgroup_of_inj_hom_group_iso_units F SL(2,F) _ p _ _ _ A _ f hf
  -- x is conjugate to t τ
  · right
    have τ_ne_zero : τ ≠ 0 := by
      rintro rfl
      simp at x_IsConj_t
      symm at x_IsConj_t
      contradiction
    obtain ⟨c, c_smul_TZ_eq_centralizer⟩ :=
      conjugate_centralizers_of_IsConj (SpecialMatrices.t τ) x x_IsConj_t
    rw [centralizer_t_eq_TZ F τ_ne_zero] at c_smul_TZ_eq_centralizer
    have A_eq_conj_TZ_meet_G : A = (conj c • (T F ⊔ Z F)) ⊓ G := by
      rw [A_eq_centra, T_join_Z_eq_TZ, c_smul_TZ_eq_centralizer]
    -- rw [← T_join_Z_eq_TZ F] at A_le_conj_TZ
    -- -- contruct monoid homomorphism from A →* T F ⊔ Z F
    -- let f : A →* (T F ⊔ Z F :) :=
    --   (MulEquiv.subgroupMap (conj c) (T F ⊔ Z F)).symm.toMonoidHom.comp (inclusion A_le_conj_TZ)
    -- image of A under f yields a finite subgroup of T F ⊔ Z T
    -- show that a finite subgroup of T F ⊔ Z T is of the form Q ⊔ Z T
    -- for Q with the desired properties
    have := centralizer_t_eq_TZ F τ_ne_zero
    rw [← T_join_Z_eq_TZ F] at this
    -- A = centralizer {x} ⊓ G
    -- centralizer {x} = conj c • centralizer {t τ}
    -- centralizer {t τ} = Z ⊓ T
    -- image of top element through the homorphism f : A →* T F ⊔ Z F
    -- is a finite subgroup of T F ⊔ Z F
    -- let T₀Z := Subgroup.map f ⊤
    -- have fin_T₀Z : Finite T₀Z := Finite.Set.finite_image ⊤ f
    -- define isomorphism between A and (T F ⊔ Z F) ⊓ G = (T F ⊓ G) ⊔ Z F and
    have Z_eq_Z_meet_G : Z F = Z F ⊓ G :=
      ((@center_SL2_F_eq_Z F _ _).symm) ▸ left_eq_inf.mpr center_le_G
    -- but before we can define the isomorphism we need the key result
    let center_normal : (center SL(2, F)).Normal := normal_of_characteristic (center SL(2, F))
    have key : (T F ⊔ Z F) ⊓ G = (T F ⊓ G) ⊔ Z F := calc
      (T F ⊔ Z F) ⊓ G = (T F ⊓ G) ⊔ (Z F ⊓ G) := by
        ext y
        rw [← SetLike.mem_coe, ← Z_eq_Z_meet_G, ← center_SL2_F_eq_Z, Subgroup.coe_inf,
          Subgroup.mul_normal (H := T F) (N := center SL(2,F)), ← SetLike.mem_coe,
          Subgroup.mul_normal (H := T F ⊓ G) (N := center SL(2,F)), Subgroup.coe_inf]
        constructor
        · rintro ⟨⟨t, t_in_T, z, hz, rfl⟩, y_in_G⟩
          simp at y_in_G ⊢
          use t
          constructor
          · constructor
            · exact t_in_T
            · rw [← mul_one t, ← mul_inv_cancel z, ← mul_assoc]
              exact Subgroup.mul_mem _ y_in_G <| (Subgroup.inv_mem_iff G).mpr (center_le_G hz)
          use z
        · rintro ⟨t, ⟨t_in_T, t_in_G⟩, z, z_in_Z, rfl⟩
          simp
          constructor
          · use t
            constructor
            exact t_in_T
            use z
          exact Subgroup.mul_mem _ t_in_G <| center_le_G z_in_Z
      _ = (T F ⊓ G) ⊔ Z F := by rw [← Z_eq_Z_meet_G]
    -- from the subgroup equality we construct an isomorphism and compose all of them
    -- `((T F ⊓ G) ⊔ Z F:) ≃* ((T F ⊔ Z F) ⊓ G :) ≃* ((conj c • (T F ⊔ Z F)) ⊓ G) ≃* A`
    let f' : A ≃* ((T F ⊓ G) ⊔ Z F:) := sorry
      --(MulEquiv.subgroupCongr key).trans ((MulEquiv.subgroupMap (conj c) (D F)).symm).trans (MulEquiv.subgroupCongr A_eq_conj_TZ_meet_G)
    -- We push T F ⊓ G which is a subgroup of T F ⊓ G ⊔ Z F through
    -- the inverse monoid homomorphism to get the subgroup Q isomorphic to T₀ < T F
    -- which is an Elementary Abelian subgroup.
    --     rw [sup_eq_sup_iff_left]
    --     constructor
    --     · exact le_trans inf_le_left le_sup_right
    --     · refine le_trans ?_ le_sup_right
    --       exact (le_of_eq (inf_of_le_left <| (@center_SL2_F_eq_Z F _ _) ▸ center_le_G).symm)
    -- have : Z F ⊓ G = Z F  := inf_of_le_left <| (@center_SL2_F_eq_Z F _ _) ▸ center_le_G

    sorry
  -- x is conjugate to -t τ
  · sorry



#check Subgroup.mul_mem
#check iSup_inf_eq
#check Fintype.card_units
#check MonoidHom.comp
#check Subgroup.inclusion_injective
#check MulEquiv.comp_left_injective
#check le_of_eq
#check isCyclic_of_subgroup_isDomain
#check Function.Injective

#check Nat.coprime_mul_iff_left

/- Theorem 2.3 (iv a) If A ∈ M and |A| is relatively prime to p, then we have [N G (A) : A] ≤ 2. -/
theorem index_normalizer_le_two {p : ℕ}(A : Subgroup SL(2,F)) (center_le_G : center SL(2,F) ≤ G) (hA : A ∈ MaximalAbelianSubgroups G) (hA' : Nat.Coprime (Nat.card A) p) : (A.subgroupOf G).normalizer.index ≤ 2 := by
  by_cases h : Nat.card A ≤ 2
  · have A_eq_Z : A = Z F := by
      refine le_antisymm ?A_le_Z ?Z_le_A
      case A_le_Z =>
        obtain ⟨⟨A_IsComm, A_Maximal⟩, A_le_G⟩ := hA
        sorry
      case Z_le_A => exact (@center_SL2_F_eq_Z F _ _) ▸ center_le SL(2,F) G A hA center_le_G
    simp [A_eq_Z]
    have : Subgroup.Normal ((Z F).subgroupOf G) := by
      rw [← @normalizer_eq_top]
      sorry
    sorry
  · sorry

#check le_normalizer_of_normal
#check Normal
#check le_centralizer_meet

/- Theorem 2.3 (iv b) Furthermore, if [NG (A) : A] = 2, then there is an element y of NG (A)\A such that, yxy⁻¹ = x⁻¹  for all x ∈ A. -/
theorem of_index_normalizer_eq_two {p : ℕ }(A : Subgroup SL(2,F)) (hA : A ∈ MaximalAbelianSubgroups G) (hA' : Nat.Coprime (Nat.card A) p) (hNA : A.normalizer.index = 2)
  (x : A) : ∃ y ∈ A.normalizer.carrier \ A, y * x * y⁻¹ = x⁻¹ := by sorry

/- Theorem 2.3 (v a) Let Q be a Sylow p-subgroup of G. If Q = { I_G }, then there is a cyclic subgroup K of G such that N_G (Q) = Q K.  -/
-- def theorem_2_6_v_a { p : ℕ }
--   (hp : Nat.Prime p)
  -- (Q : Sylow p G)
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
  K ∈ MaximalAbelianSubgroups G := by
  sorry

#check MulAut
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
