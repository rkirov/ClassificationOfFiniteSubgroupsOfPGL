import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Sylow
import ClassificationOfSubgroups.Ch3_PropertiesOfSLOverAlgClosedField.S4_PropertiesOfCentralizers
import ClassificationOfSubgroups.Ch4_MaximalAbelianSubgroupClassEquation.MaximalAbelianSubgroup
import ClassificationOfSubgroups.Ch4_MaximalAbelianSubgroupClassEquation.ElementaryAbelian


set_option linter.style.longLine true
set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0


universe u

variable (F : Type u) [Field F]

open Matrix MatrixGroups Subgroup MulAut MaximalAbelianSubgroup




/- Lemma 2.2: Every finite subgroup of a multiplicative group of a field is cyclic. -/
-- lemma IsCyclic_of_finite_subgroup_units (H : Subgroup Fˣ) [Finite H] : IsCyclic H :=
--   subgroup_units_cyclic H

open SpecialSubgroups








#check IsPGroup.exists_le_sylow
#check comap_inf

#check Sylow

#check le_normalizer_of_normal
#check Normal
#check le_centralizer_meet

/- Theorem 2.3 (iv b) Furthermore, if [NG (A) : A] = 2, then there is an element y of NG (A)\A such that, yxy⁻¹ = x⁻¹  for all x ∈ A. -/
theorem of_index_normalizer_eq_two {p : ℕ }(A G : Subgroup SL(2,F)) (hA : A ∈ MaximalAbelianSubgroups G) (hA' : Nat.Coprime (Nat.card A) p) (hNA : A.normalizer.index = 2)
  (x : A) : ∃ y ∈ A.normalizer.carrier \ A, y * x * y⁻¹ = x⁻¹ := by sorry

/- Theorem 2.3 (v a) Let Q be a Sylow p-subgroup of G. If Q = { I_G }, then there is a cyclic subgroup K of G such that N_G (Q) = Q K.  -/
def theorem_2_6_v_a { p : ℕ }
  (hp : Nat.Prime p)
  (G : Subgroup SL(2,F))
  (Q : Sylow p G)
  (h : Q.toSubgroup ≠ ⊥) :
  ∃ K : Subgroup G, IsCyclic K ∧ normalizer Q.toSubgroup = Q.toSubgroup ⊓ K := by sorry

/- Theorem 2.3 (v b)If |K| > |Z|, then K ∈ M. -/
theorem theorem_2_6_v_b { p : ℕ } [hp' : Fact (Nat.Prime p)] (G : Subgroup SL(2,F)) (Q : Sylow p G) (h : Q.toSubgroup ≠ ⊥) (K : Subgroup G)
  (hK : IsCyclic K) (hNG : normalizer Q.toSubgroup = Q.toSubgroup ⊔ K) (h : Nat.card K > Nat.card (center SL(2,F))) :
  map G.subtype K ∈ MaximalAbelianSubgroups G := by
  sorry

/- Conjugacy of Maximal Abelian subgroups -/
/-
Definition. The set Ci = Clᵢ = {x Aᵢx⁻¹ : x ∈ G} is called the conjugacy class of
A ∈ M.
-/

def Cᵢ  {F : Type*} [Field F] (Aᵢ G : Subgroup SL(2,F)) (hA : Aᵢ  ∈ MaximalAbelianSubgroups G) := (ConjClasses Aᵢ)

def Cᵢ_noncentral (Aᵢ G : Subgroup SL(2,F)) := Cᵢ Aᵢ G

-- The non-central part of a subgroup
def Subgroup.noncenter {G : Type*} [Group G] (H : Subgroup G) := {x : G | x ∈ H.carrier \ center G}

#leansearch "noncentral part of a group?"


#leansearch "conjugacy class?"

/- Let Aᵢ* be the non-central part of Aᵢ ∈ M -/

#check ConjClasses
#check ConjClasses.noncenter

/- let M∗ be the set of all Aᵢ* and let Cᵢ* be the conjugacy class of Aᵢ* .-/

-- def M_ (A : )

-- lemma theorem_2_4 ()

/-
Clᵢ = {x Aᵢx⁻¹ : x ∈ G}

For some Ai ∈ M and A∗i ∈ M∗ let,
Ci = ⋃ x ∈ G, x * Aᵢ * x⁻¹, and Cᵢ* = ⋃ x ∈ G, x Aᵢ* x⁻¹

It’s evident that Cᵢ* = Cᵢ \ Z(SL(2,F)) and that there is a Cᵢ corresponding to each
Cᵢ . Clearly we have the relation, |Cᵢ*| = |Aᵢ*||Clᵢ*|
-/

#leansearch "finite union?"

-- def C_i {F : Type*} [Field F] (A G : Subgroup SL(2,F)) [Finite G] (hA : A ∈ MaximalAbelianSubgroups G) :=  ⋃ x ∈ G,

-- lemma card_noncentral_conjugacy_eq_mul_noncentral_MaxAbSub


#min_imports
