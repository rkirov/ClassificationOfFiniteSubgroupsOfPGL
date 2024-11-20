import Mathlib

universe u

open Matrix MatrixGroups

variable (F : Type u) [Field F] [IsAlgClosed F]

instance : Group SL(2,F) := by infer_instance

namespace ElementaryAbelian

def IsElementaryAbelian (G : Type*) [CommGroup G] : Prop := ∃ p : ℕ, Nat.Prime p → ∀ g : G, g ^ p = 1

end ElementaryAbelian

namespace MaximalAbelian

def IsMaximalAbelian (G : Type*) [Group G] (H : Subgroup G) : Prop := Maximal (Subgroup.IsCommutative) H

def MaximalAbelianSubgroups { G : Type*} [Group G](H : Subgroup G) : Set (Subgroup H) :=
  { K : Subgroup H | @IsMaximalAbelian H _ K}

end MaximalAbelian

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

namespace SpecialLinearGroup


section one

def T (τ : F): SL(2, F) :=
  ⟨!![1, 0; τ, 1], by norm_num [Matrix.det_fin_two_of]⟩

def D (δ : Fˣ) : SL(2, F) :=
  ⟨!![(δ : F), (0 : F); (0 :F) , (δ⁻¹ : F)], by norm_num [Matrix.det_fin_two_of]⟩

def W : SL(2, F) :=
  ⟨!![0,1;-1,0], by norm_num [Matrix.det_fin_two_of]⟩

/- Each element of L is conjugate to either dω for some ω ∈ F ∗ ,
or to ±tλ for some λ ∈ F .
where tλ = ![![1 , 0], ![λ, 1]] and dω = ![![ω, 0], ![0, ω⁻¹]]
(and w = ![![0, 1] , [-1, 0]])
-/
open Subgroup
/- Lemma 1.3. Z(SL(2,F)) = ⟨ -I ⟩ .-/
def center_of_SL_2_F : center SL(2,F) ≃* rootsOfUnity 2 F  := by apply Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' 2

/-! Requires Jordan Normal Form -/
theorem theorem_1_5 (x : SL(2,F)) : ∃ δ : Fˣ, IsConj x (D δ) ∨ ∃ τ : F, IsConj x (T τ) := by sorry

end one

section two

open MaximalAbelian

/- Let G be an arbitrary finite subgroup of SL(2, F) containing Z(SL(2, F)) -/
variable {G : Type*} (G : Subgroup (SL(2,F))) [Finite G] (hG : Subgroup.center (SL(2, F)) ≤ G)

namespace IsPGroup

/- Lemma 2.1. If G is a finite group of order pm where p is prime and m > 0,
then p divides |Z(G)|.-/
lemma p_dvd_card_center {H : Type*} {p : ℕ} (hp:  Nat.Prime p) [Group H] [Finite H] [Nontrivial H] (hH : IsPGroup p H) : p ∣ Nat.card (Subgroup.center H) := by
  let inst : Fact (Nat.Prime p) := by exact { out := hp }
  have card_H_eq_pow_prime : ∃ n > 0, Nat.card H = p ^ n := by rwa [← hH.nontrivial_iff_card]
  have card_center_eq_pow_prime : ∃ k > 0, Nat.card (Subgroup.center H) = p ^ k := by obtain ⟨n, npos, hn⟩ := card_H_eq_pow_prime ; apply IsPGroup.card_center_eq_prime_pow hn npos
  obtain ⟨k, kpos, hk⟩ := card_center_eq_pow_prime
  use p^(k-1)
  rw [hk, ← Nat.pow_add_one', Nat.sub_add_cancel]
  linarith

end IsPGroup

/- Lemma 2.2: Every finite subgroup of a multiplicative group of a field is cyclic. -/
omit [IsAlgClosed F] in
lemma lemma_2_2 (H : Subgroup Fˣ) [Finite H]: IsCyclic H := subgroup_units_cyclic H


/- Theorem 2.3 (i) If x ∈ G\Z then we have CG (x) ∈ M. -/
theorem theorem_2_3_i (x : SL(2,F)) (hx : x ∈ (G.carrier \ (Subgroup.center SL(2,F)).carrier)) : Subgroup.centralizer {⟨x, by aesop⟩} ∈ MaximalAbelianSubgroups G := by sorry

-- need coercion
-- instance : (Subgroup.center SL(2,F) : Subgroup ↥G) := infer_instance

/- Theorem 2.3 (ii) For any two distinct subgroups A and B of M, we have A ∩ B = Z. -/
-- theorem theorem_2_6_ii (A B : Subgroup G) (hA : A ∈ MaximalAbelianSubgroups G) (hB : B ∈ MaximalAbelianSubgroups G) (A_neq_B: A ≠ B) :
--   ((A) ⊓ (B)) = ((Subgroup.center SL(2,F))):= by sorry

/- Theorem 2.3 (iii) An element A of M is either a cyclic group whose order is relatively prime
to p, or of the form Q × Z where Q is an elementary abelian Sylow p-subgroup
of G. -/
-- theorem theorem_2_6_iii (A : Subgroup G) (hA : A ∈ MaximalAbelianSubgroups G) : (IsCyclic A ∧ Nat.Coprime (Nat.card A) p) ∨ (∃ Q : Sylow p G, IsElementaryAbelian Q → A ≃* Q.toSubgroup.prod (Subgroup.center L)) := by sorry

/- Theorem 2.3 (iv a) If A ∈ M and |A| is relatively prime to p, then we have [NG (A) : A] ≤ 2. -/
theorem theorem_2_3_iv_a (A : Subgroup G) (hA : A ∈ MaximalAbelianSubgroups G) (hA' : Nat.Coprime (Nat.card A) p) : A.normalizer.index ≤ 2 := by sorry

/- Theorem 2.3 (iv b) Furthermore, if [NG (A) : A] = 2, then there is an element y of NG (A)\A such that, yxy⁻¹ = x⁻¹  for all x ∈ A. -/
theorem theorem_2_3_iv_b (A : Subgroup G) (hA : A ∈ MaximalAbelianSubgroups G) (hA' : Nat.Coprime (Nat.card A) p) (hNA : Subgroup.index (Subgroup.normalizer A) = 2)
  (x : A) : ∃ y ∈ A.normalizer.carrier \ A, y * x * y⁻¹ = x⁻¹ := by sorry

/- Theorem 2.3 (v a) Let Q be a Sylow p-subgroup of G. If Q 6= {IG }, then there is a cyclic subgroup K of G such that NG (Q) = QK.  -/
-- theorem theorem_2_6_v_a { p : ℕ } (hp : Nat.Prime p) (Q : Sylow p G) (h : Q.toSubgroup ≠ ⊥) : ∃ K : Subgroup G, IsCyclic K → Q.toSubgroup.normalizer ≃* Q.toSubgroup.prod K:= by sorry

/- Theorem 2.3 (v b)If |K| > |Z|, then K ∈ M. -/
-- theorem theorem_2_6_v_b { p : ℕ } (hp : Nat.Prime p) (Q : Sylow p G) (h : Q.toSubgroup ≠ ⊥) (K :  Subgroup G) (hK : IsCyclic K) (NG_iso_prod_QK : Q.toSubgroup.normalizer ≃* Q.toSubgroup.prod K) (h: Nat.card K > Nat.card (Subgroup.center L)) : K ∈ MaximalAbelianSubgroups G := by sorry

end two

section three

/- Theorem 3.6 -/
theorem dickson_classification_theorem_class_I {p : ℕ} [CharP F p] (hp : Prime p) (hp' : p = 0 ∨ Nat.Coprime (Nat.card G) p)
  (G : Subgroup (SL(2,F))) [Finite G] : SL(2,F) = SL(2,F) := sorry

end three

end SpecialLinearGroup
