import Mathlib
import ClassificationOfSubgroups.Ch1_PropertiesOfSpecialLinearGroup

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
theorem IsPSubgroup_of_IsElementaryAbelian {G : Type*} [CommGroup G] { p : ℕ } [Fact (Nat.Prime p)] (hG : IsElementaryAbelian p G) : IsPGroup p G := fun g => ⟨1, by rw [pow_one, hG]⟩

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
lemma p_dvd_card_center {H : Type*} {p : ℕ} (hp:  Nat.Prime p) [Group H] [Finite H] [Nontrivial H] (hH : IsPGroup p H) : p ∣ Nat.card (center H) := by
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

lemma IsCommutative_iff {G : Type*} [Group G] (H : Subgroup G) : IsCommutative H ↔ ∀ x y : H, x * y = y * x := by
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
lemma inf_IsCommutative_of_IsCommutative_left {G : Type*} [ Group G] (H K : Subgroup G) (hH : IsCommutative H) : IsCommutative (H ⊓ K) := by
  rw [IsCommutative_iff]
  intro x y
  have H_meet_K_le_H : H ⊓ K ≤ H := inf_le_left
  have x_in_H : (x : G) ∈ H := H_meet_K_le_H <| SetLike.coe_mem _
  have y_in_H : (y : G) ∈ H := H_meet_K_le_H <| SetLike.coe_mem _
  have := @mul_comm_of_mem_isCommutative G _ H hH x y x_in_H y_in_H
  exact SetLike.coe_eq_coe.mp this

lemma subgroupOf_IsCommutative {G : Type*} [ Group G ] (H K : Subgroup G) (hH : IsCommutative H) : IsCommutative (H.subgroupOf K) := by
  -- rw [@IsCommutative_iff]
  rw [← @inf_subgroupOf_right]
  have : IsCommutative (H ⊓ K) := by exact inf_IsCommutative_of_IsCommutative_left H K hH
  exact subgroupOf_isCommutative (H ⊓ K)

/- Theorem 2.3 (i) If x ∈ G\Z then we have CG (x) ∈ M. -/
theorem G_meet_centralizer_of_noncentral_in_MaximalAbelianSubgroups [IsAlgClosed F] [DecidableEq F]
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





/- Theorem 2.3 (ii) For any two distinct subgroups A and B of M, we have A ∩ B = Z. -/
theorem theorem_2_6_ii (A B : Subgroup SL(2,F)) (hA : A ∈ MaximalAbelianSubgroups G)
  (hB : B ∈ MaximalAbelianSubgroups G) (A_neq_B: A ≠ B) (hG : center SL(2,F) ≤ G) :
  A ⊓ B = Z F := by
  ext x
  constructor
  · rintro ⟨x_in_A, x_in_B⟩
    simp at x_in_A x_in_B
    simp
    sorry

  · sorry


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
