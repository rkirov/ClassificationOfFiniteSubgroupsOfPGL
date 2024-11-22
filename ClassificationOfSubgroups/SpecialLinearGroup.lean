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

-- def NonCentral
def MaximalAbelianSubgroups { G : Type*} [Group G](H : Subgroup G) : Set (Subgroup H) :=
  { K : Subgroup H | @IsMaximalAbelian H _ K}

end MaximalAbelian

namespace SpecialLinearGroup

universe u

open Matrix MatrixGroups

variable (F : Type u) [Field F]

instance : Group SL(2,F) := by infer_instance
section one

def T {F : Type*} [Field F] (τ : F): SL(2, F) :=
  ⟨!![1, 0; τ, 1], by norm_num [Matrix.det_fin_two_of]⟩

def D {F : Type*} [Field F] (δ : Fˣ) : SL(2, F) :=
  ⟨!![(δ : F), (0 : F); (0 :F) , (δ⁻¹ : F)], by norm_num [Matrix.det_fin_two_of]⟩

def W {F : Type*} [Field F] : SL(2, F) :=
  ⟨!![0,1;-1,0], by norm_num [Matrix.det_fin_two_of]⟩

@[simp]
lemma inv_D_eq (δ : Fˣ) : (D δ)⁻¹ = D (δ⁻¹) := by simp [Matrix.SpecialLinearGroup.SL2_inv_expl, D]; rfl
  -- ext i j
  -- fin_cases i <;> fin_cases j <;>
  -- simp [D]

@[simp]
lemma inv_T_eq (τ : F) : (T τ)⁻¹ = T (-τ) := by simp [Matrix.SpecialLinearGroup.SL2_inv_expl, T]; rfl

/-
Lemma 1.1. For any ω, ρ ∈ F ∗ and τ, µ ∈ F we have:
(i) D δ * D ρ = D (δ * ρ),
(ii) T τ *  T μ = T (τ + µ),
(iii) D δ * T τ * (D δ)⁻¹ = T (τ * δ⁻²),
(iv) W * D δ * W⁻¹ = (D δ)⁻¹.
-/
-- (i)
lemma lemma_1_1_i (δ ρ : Fˣ) : D δ * D ρ = D (δ * ρ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D, mul_comm]

-- (ii)
lemma lemma_1_1_ii (τ μ : F) : T τ * T μ = T (τ + μ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>  simp [T]

-- (iii)
lemma lemma_1_1_iii (δ : Fˣ) (τ : F) : D δ * T τ * (D δ)⁻¹ = T (τ * δ⁻¹ * δ⁻¹) := by
  simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D, T, mul_comm]

-- (iv)
lemma lemma_1_1_iv (δ : Fˣ) : W * (D δ) * W⁻¹ = (D δ)⁻¹ := by
  rw [inv_D_eq]
  ext i j
  fin_cases i <;> fin_cases j <;>  simp [D, W]

/- Lemma 1.2.1.1-/
def setOfD : Subgroup SL(2,F) where
  carrier := { D δ | δ : Fˣ }
  mul_mem' := by
              intro S Q hS hQ
              simp at *
              obtain ⟨δS, hδS⟩ := hS
              obtain ⟨δQ, hδQ⟩ := hQ
              use δS * δQ
              rw [← hδS, ← hδQ, lemma_1_1_i]
  one_mem' := by
              use 1
              ext i j; fin_cases i <;> fin_cases j <;> simp [D]
  inv_mem' := by
              intro S
              simp
              intro δ hS
              use δ⁻¹
              simp [← hS]

/- Lemma 1.2.1.2 -/
def setOfT : Subgroup SL(2,F) where
  carrier := { T τ | τ : F}
  mul_mem' := by
              intro S Q hS hQ
              simp at *
              obtain ⟨τS, hτS⟩ := hS
              obtain ⟨τQ, hτQ⟩ := hQ
              use τS + τQ
              rw [← hτS, ← hτQ, lemma_1_1_ii]
  one_mem' := by
              use 0
              simp [T]
              ext i j; fin_cases i <;> fin_cases j <;> simp [D]
  inv_mem' := by
              intro S hS
              simp at *
              obtain ⟨τ, hτ⟩ := hS
              use (-τ)
              simp [← hτ]


open Subgroup

/- Lemma 1.3. Z(SL(2,F)) = ⟨ -I ⟩ .-/
def center_of_SL_2_F : center SL(2,F) ≃* rootsOfUnity 2 F  := by apply Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' 2

#check Module.End

-- instance Module.End (Matrix (Fin 2) (Fin 2) F) := by sorry

#check Module.End.exists_isNilpotent_isSemisimple

#check Matrix.SpecialLinearGroup.toLin'_to_linearMap

instance : Monoid SL(2,F) := Matrix.SpecialLinearGroup.monoid

instance : Module F (Matrix (Fin 2) (Fin 2) F) := by exact module
/- Requires Jordan Normal Form -/
/- Lemma 1.5. Each element of SL(2,F) is conjugate to either D δ for some δ ∈ Fˣ, or to  ± T τ for some τ ∈ F .-/
theorem theorem_1_5 [IsAlgClosed F] (S : SL(2,F)) : ∃ δ : Fˣ, IsConj S (D δ) ∨ ∃ τ : F, IsConj S (T τ) := by
  let inst : PerfectField F := IsAlgClosed.perfectField F
  obtain h := @Module.End.exists_isNilpotent_isSemisimple F (Matrix (Fin 2) (Fin 2) F) _ _ _-- (S.coeToGL.toLinear_apply)
  sorry

/- Proposition 1.7. (i) NL (D1 ) = hD, wi, where D1 is any subgroup of D with
order greater than 2.-/


/- Proposition 1.8. Let a and b be conjugate elements in a group G. Then ∃ x ∈ G such that xCG (a)x−1 = CG (b).-/
-- lemma proposition_1_8 { G : Type* } [Group G] (a b : G) (hab : IsConj a b) : ∃ x : G, ConjAct(centralizer { a }) = centralizer { b } := by sorry  :=


/- Corollary 1.9. The centraliser of an element x in L is abelian unless x belongs to the centre of L.-/
lemma corollary_1_9 (S : SL(2,F)) : x ∉ center SL(2,F) → IsCommutative (centralizer { S }) := by sorry

end one


section two

open MaximalAbelian Subgroup

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

example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
    [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq h
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
  (K :  Subgroup G)
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
Cᵢ . Clearly we have the relation, |Cᵢ*| = |Aᵢ*||Clᵢ*| (clearly on pen and paper smh...)
-/
end two

section three

/- Theorem 3.6 -/
theorem dickson_classification_theorem_class_I {p : ℕ} [CharP F p] (hp : Prime p) (hp' : p = 0 ∨ Nat.Coprime (Nat.card G) p)
  (G : Subgroup (SL(2,F))) [Finite G] : SL(2,F) = SL(2,F) := sorry

end three

end SpecialLinearGroup
