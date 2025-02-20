import Mathlib
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_MaximalAbelianSubgroup

set_option linter.style.longLine true

open Matrix MatrixGroups Subgroup


/- Lemma 3.1 -/
lemma IsPGroup.not_le_normalizer {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] (G : Subgroup SL(2,F)) (H K : Subgroup G) (hK : IsPGroup p K )
  (H_lt_K : H < K) : ¬ H ≤ Subgroup.normalizer K := by sorry

open MaximalAbelianSubgroup


/- Lemma 3.2 -/
lemma Sylow.not_normal_subgroup_of_G {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] (G K : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G)
  (hK : K ∈ MaximalAbelianSubgroups G)
  (hQK : map G.subtype (normalizer Q.toSubgroup) = (map G.subtype Q.toSubgroup) ⊔ K) :
  ¬ Normal Q.toSubgroup := by
  sorry

/- Lemma 3.3 -/
def R (F : Type*) [Field F] (p : ℕ) [Fact (Nat.Prime p)] [CharP F p](k : ℕ+) :=
  { x : F | x^p^(k : ℕ) - x = 0}


instance field_R {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] {k : ℕ+} : Field (R F p k) := by sorry

/- Lemma 3.4 -/
#check Matrix.card_GL_field

abbrev SL := Matrix.SpecialLinearGroup

lemma card_SL_field {𝔽 : Type u_1} [Field 𝔽] [Fintype 𝔽] (n : ℕ) :
  Nat.card (SL (Fin n) 𝔽) = Nat.card (GL (Fin n) 𝔽) / (Fintype.card 𝔽 - 1) := by sorry

/- Lemma 3.5. Correspondence theorem -/
#leansearch "group theory correspondence theorem?"


instance five_prime : Fact (Nat.Prime 5) := { out := by decide }


#leansearch "Schur covering group of S₄?"

-- (v) Ŝ₄ , the representation group of S4 in which the transpositions correspond to
-- the elements of order 4.

/- Theorem 3.6 -/
theorem dickson_classification_theorem_class_I {F : Type*} [Field F] {p : ℕ} [CharP F p]
  (hp : Prime p) (hp' : p = 0 ∨ Nat.Coprime (Nat.card G) p) (G : Subgroup (SL(2,F)))
  [Finite G] :
  IsCyclic G ∨
  ∃ n : ℕ, ∃ φ : G ≃* DihedralGroup n, True
  ∨
  ∃ φ : G ≃* SL(2, GaloisField 3 1), True
  ∨
  ∃ φ : G ≃* SL(2, GaloisField 5 1), True
  ∨
  ∃ φ : G ≃* GL (Fin 2) (GaloisField 3 1), True
  := by sorry


-- def myGroup : Subgroup :=

-- How to embed d (x : GaloisField p (2k)) into SL(2, GaloisField p k)?

-- (x) The group hSL(2, Fq ), dπ i, where SL(2, Fq ) C hSL(2, Fq ), dπ i.

theorem dickson_classification_theorem_class_II {F : Type*} [Field F] {p : ℕ}
  [Fact (Nat.Prime p)] [CharP F p]
  (hp : Prime p) (hp' : p ∣ Nat.card G) (G : Subgroup (SL(2,F)))
  [Finite G] :
  ∃ Q : Subgroup SL(2,F), IsElementaryAbelian p Q ∧ Normal Q ∧ ∃ φ : G ≃* Q, True
  ∨
  (p = 2 ∧ ∃ n : ℕ, ∃ φ : G ≃* DihedralGroup n, Odd n)
  ∨
  ∃ φ : G ≃* SL(2, GaloisField 5 1), True
  ∨
  ∃ k : ℕ+, ∃ φ : G ≃* GaloisField p k, True
  ∨
  ∃ k : ℕ+, ∃ x : GaloisField p (2* k), orderOf x^2 = p^(k : ℕ) ∧
    ∃ φ : G ≃* SL(2, GaloisField p k), True
  := by sorry

-- implicit normality condition on Q

#leansearch "quotient group is a group?"
-- ∧ IsCyclic (Subgroup.map (@QuotientGroup.mk' G _ (Q.subgroupOf G) (by sorry)) ⊤) -- needs to know quotient is a group

-- (IsCyclic (QuotientGroup.Quotient.group Q (nN := by sorry)))

-- (vi) Q is elementary abelian, Q C G and G/Q is a cyclic group whose order is
--relatively prime to p.
