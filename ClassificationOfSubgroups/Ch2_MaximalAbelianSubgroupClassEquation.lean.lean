import Mathlib

namespace test

variable {G : Type*} [Group G] ( H : Subgroup G) (hHMax : Maximal (Subgroup.IsCommutative) H)

example : H.IsCommutative := hHMax.prop

example : ∀ J, H < J → ¬J.IsCommutative := by
  intro J hJ
  contrapose! hJ
  exact Maximal.not_gt hHMax hJ

example : ∀ (J : Subgroup G),(J.IsCommutative ∧ (∀ K, J < K → ¬K.IsCommutative)) →
    Maximal (Subgroup.IsCommutative) J := by
  intro J hJ
  rw [Maximal]
  use hJ.left
  replace hJ := hJ.right
  intro K hK hJK
  specialize hJ K
  if h: J = K then
    rw [h]
  else
    exact (hJ (lt_of_le_of_ne hJK h) hK).elim

end test

namespace ElementaryAbelian

def IsElementaryAbelian (p : ℕ) [Fact (Nat.Prime p)] (G : Type*) [CommGroup G] : Prop  :=
  ∀ g : G, g ^ p = 1

/- If `G` is elementary abelian then G is a `p`-Group -/
theorem IsPSubgroup_of_IsElementaryAbelian {G : Type*} [CommGroup G] { p : ℕ } [Fact (Nat.Prime p)] (hG : IsElementaryAbelian p G) : IsPGroup p G := fun g => ⟨1, by rw [pow_one, hG]⟩

end ElementaryAbelian

namespace MaximalAbelian

open Subgroup

def IsMaximalAbelian (G : Type*) [Group G] (H : Subgroup G) : Prop := Maximal (IsCommutative) H

def MaximalAbelianSubgroups { G : Type*} [Group G](H : Subgroup G) : Set (Subgroup H) :=
  { K : Subgroup H | @IsMaximalAbelian H _ K}

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

/- Theorem 2.3 (i) If x ∈ G\Z then we have CG (x) ∈ M. -/
theorem theorem_2_3_i
  (x : SL(2,F))
  (hx : x ∈ (G.carrier \ (Subgroup.center SL(2,F)).carrier)) :
  Subgroup.centralizer {⟨x, by aesop⟩} ∈ MaximalAbelianSubgroups G := by sorry

/- Theorem 2.3 (ii) For any two distinct subgroups A and B of M, we have A ∩ B = Z. -/
-- theorem theorem_2_6_ii
--   (A B : Subgroup G)
--   (hA : A ∈ MaximalAbelianSubgroups G)
--   (hB : B ∈ MaximalAbelianSubgroups G)
--   (A_neq_B: A ≠ B)
--   (hG : center SL(2,F) ≤ G) :
--   ((A) ⊓ (B)) = ((center SL(2,F))) := by sorry

/- Theorem 2.3 (iii) An element A of M is either a cyclic group whose order is relatively prime
to p, or of the form Q × Z where Q is an elementary abelian Sylow p-subgroup
of G. -/
-- theorem theorem_2_6_iii_a
--   (A : Subgroup G)
--   (hA : A ∈ MaximalAbelianSubgroups G)
--   (h : ¬ (IsCyclic A ∧ Nat.Coprime (Nat.card A) p)) :
--   ∃ p : ℕ, Nat.Prime p → ∃ Q : Sylow p G, ElementaryAbelian.IsElementaryAbelian  p  Q.toSubgroup → Nonempty (A ≃* (Q.toSubgroup.prod (center SL(2,F)))) := by sorry

/- Theorem 2.3 (iv a) If A ∈ M and |A| is relatively prime to p, then we have [NG (A) : A] ≤ 2. -/
theorem theorem_2_3_iv_a (A : Subgroup G) (hA : A ∈ MaximalAbelianSubgroups G) (hA' : Nat.Coprime (Nat.card A) p) : A.normalizer.index ≤ 2 := by sorry

/- Theorem 2.3 (iv b) Furthermore, if [NG (A) : A] = 2, then there is an element y of NG (A)\A such that, yxy⁻¹ = x⁻¹  for all x ∈ A. -/
theorem theorem_2_3_iv_b (A : Subgroup G) (hA : A ∈ MaximalAbelianSubgroups G) (hA' : Nat.Coprime (Nat.card A) p) (hNA : A.normalizer.index = 2)
  (x : A) : ∃ y ∈ A.normalizer.carrier \ A, y * x * y⁻¹ = x⁻¹ := by sorry

/- Theorem 2.3 (v a) Let Q be a Sylow p-subgroup of G. If Q 6= {IG }, then there is a cyclic subgroup K of G such that NG (Q) = QK.  -/
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
  (K : Subgroup G)
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
