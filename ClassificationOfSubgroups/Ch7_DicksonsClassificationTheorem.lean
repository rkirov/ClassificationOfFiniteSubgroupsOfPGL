import Mathlib
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_MaximalAbelianSubgroup

set_option linter.style.longLine true
set_option maxHeartbeats 0

open Matrix MatrixGroups Subgroup


/- Lemma 3.1 -/
lemma IsPGroup.not_le_normalizer {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] (G : Subgroup SL(2,F)) (H K : Subgroup G) (hK : IsPGroup p K )
  (H_lt_K : H < K) : ¬ H ≤ Subgroup.normalizer K := by sorry

open MaximalAbelianSubgroup


/- Lemma 3.2 -/
lemma Sylow.not_normal_subgroup_of_G {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] (G K : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G)
  (hK : K ∈ MaximalAbelianSubgroupsOf G)
  (hQK : map G.subtype (normalizer Q.toSubgroup) = (map G.subtype Q.toSubgroup) ⊔ K) :
  ¬ Normal Q.toSubgroup := by
  sorry

/- Lemma 3.3 -/
def R (F : Type*) [Field F] (p : ℕ) [Fact (Nat.Prime p)] [CharP F p](k : ℕ+) :=
  { x : F | x^p^(k : ℕ) - x = 0 }


instance field_R {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] {k : ℕ+} : Field (R F p k) := by sorry

/- Lemma 3.4 -/
#check Matrix.card_GL_field

abbrev SL := Matrix.SpecialLinearGroup

lemma card_SL_field {𝔽 : Type u_1} [Field 𝔽] [Fintype 𝔽] (n : ℕ) :
  Nat.card (SL (Fin n) 𝔽) = Nat.card (GL (Fin n) 𝔽) / (Fintype.card 𝔽 - 1) := by sorry

/- Lemma 3.5. Correspondence theorem -/
-- #leansearch "group theory correspondence theorem?"
#check QuotientGroup.comapMk'OrderIso


instance five_prime : Fact (Nat.Prime 5) := { out := by decide }



def Isomorphic (G H : Type*) [Group G] [Group H] :=
  Nonempty (G ≃* H)

-- (v) Ŝ₄ , the representation group of S4 in which the transpositions correspond to
-- the elements of order 4.

/- Theorem 3.6 -/
theorem dicksons_classification_theorem_class_I {F : Type*} [Field F] [IsAlgClosed F]
  {p : ℕ} [CharP F p] (hp : Prime p) (hp' : p = 0 ∨ Nat.Coprime (Nat.card G) p)
  (G : Subgroup (SL(2,F)))  [Finite G] :
  IsCyclic G ∨
  Isomorphic G (DihedralGroup n)
  ∨
  Isomorphic G SL(2, ZMod 3)
  ∨
  Isomorphic G SL(2, ZMod 5)
  ∨
  Isomorphic G (GL (Fin 2) (ZMod 3))
  := by sorry


-- def myGroup : Subgroup :=



/- Embed GF(p^k) into GF(p^m) where k ∣ m -/
noncomputable
def finite_field_inclusion (p : ℕ) [Fact (Nat.Prime p)] (K L : Type*) [Field K] [Field L]
  [Algebra (ZMod p) K] [Algebra (ZMod p) L] [Finite K] (h : Nat.card K ∣ Nat.card L) :
    K →ₐ[ZMod p] L := by
  let k := Nat.log p (Nat.card K)
  let l := Nat.log p (Nat.card L)
  have hk : Nat.card K = p ^ k := sorry
  have hl : Nat.card L = p ^ l := sorry
  let e : K ≃ₐ[ZMod p] GaloisField p k := GaloisField.algEquivGaloisField _ _ hk
  let e' : L ≃ₐ[ZMod p] GaloisField p l := GaloisField.algEquivGaloisField _ _ hl
  let hb := Basis.exists_basis (ZMod p) (GaloisField p k)
  let ι := hb.choose
  let b := Classical.choice hb.choose_spec
  let hbf : Fintype ι := FiniteDimensional.fintypeBasisIndex b
  let hb' := Basis.exists_basis (ZMod p) (GaloisField p l)
  let ι' := hb'.choose
  let b' := Classical.choice hb'.choose_spec
  let hbf' : Fintype ι' := FiniteDimensional.fintypeBasisIndex b'
  have : Fintype.card ι ≤ Fintype.card ι' := sorry
  let f : ι → ι' := sorry
  have hf : Function.Injective f := sorry
  refine {
    toFun x := e'.symm (Basis.constr b (ZMod p) (fun i ↦ b'.equivFun.symm (fun i' ↦ sorry)) (e x))
    map_one' := sorry
    map_mul' := sorry
    map_zero' := sorry
    map_add' := sorry
    commutes' := sorry
  }

def ringHom {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ+}: GaloisField p k →+* GaloisField p (2*k) := by

  sorry
#leansearch "less than or equal to of dvd."

lemma card_GaloisField_dvd_card_GaloisField (p : ℕ) [Fact (Nat.Prime p)] {m n : ℕ+}
  (m_dvd_n : m ∣ n) :  Nat.card (GaloisField p m.val) ∣ Nat.card (GaloisField p n.val) := by
  rw [GaloisField.card p m m.ne_zero, GaloisField.card p n n.ne_zero]
  apply pow_dvd_pow
  suffices m.val ∣ n.val by exact Nat.le_of_dvd n.prop this
  exact PNat.dvd_iff.mp m_dvd_n


instance {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ+} :
  Algebra (ZMod p) (GaloisField p (2 * k.val)) := by sorry


-- (x) The group hSL(2, Fq ), dπ i, where SL(2, Fq ) C hSL(2, Fq ), dπ i.
noncomputable def GaloisField_ringHom (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ+) :=
  (@finite_field_inclusion p _ (GaloisField p k.val) (GaloisField p (2*k.val)) _ _ _ _ _
    (@card_GaloisField_dvd_card_GaloisField p _ k (2*k) ((dvd_mul_left k 2)))).toRingHom

#check GaloisField_ringHom

noncomputable def monoidHom  {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ+} :
  SL(2, GaloisField p k.val) →* SL(2, GaloisField p (2* k.val)) :=
    Matrix.SpecialLinearGroup.map (GaloisField_ringHom p k)


open Polynomial

lemma foo {p n : ℕ} : (X ^ p ^ n - X : (ZMod p)[X]) ∣ (X ^ n ^ (2*k) - X) := by
  sorry



#leansearch "field characteristic of galois field."

#check RingHom.toMonoidHom

#check GaloisField

#check GaloisField.equivZmodP

#check Polynomial.IsSplittingField.splits

noncomputable instance {p n : ℕ} [Fact (Nat.Prime p)] :
  Algebra (ZMod p) (GaloisField p n) := by infer_instance

noncomputable instance {p n : ℕ} [Fact (Nat.Prime p)] :
  CharP (GaloisField p n) p := by infer_instance

theorem dicksons_classification_theorem_class_II {F : Type*} [Field F] [IsAlgClosed F]{p : ℕ}
  [Fact (Nat.Prime p)] [CharP F p] (G : Subgroup (SL(2,F))) [Finite G] (hp : p ∣ Nat.card G)  :
  ∃ Q : Subgroup SL(2,F), IsElementaryAbelian p Q ∧ Normal Q ∧ Isomorphic G Q
  ∨
  (p = 2 ∧ ∃ n : ℕ, Odd n ∧ Isomorphic G (DihedralGroup n))
  ∨
  Isomorphic G SL(2, ZMod 5)
  ∨
  ∃ k : ℕ+, Isomorphic G SL(2, GaloisField p k)
  ∨
  ∃ k : ℕ+, ∃ x : GaloisField p (2* k), orderOf x^2 = p^(k : ℕ) ∧
    ∃ φ : G ≃* SL(2, GaloisField p k), True
  := by sorry

#leansearch "alternating group."

#leansearch "algebraic closure of finite field."

#check ZMod

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

open Matrix LinearMap Subgroup

open scoped MatrixGroups


/-- A projective general linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveGeneralLinearGroup' : Type _ :=
    GL n R ⧸ center (GL n R)

/-- `PGL n R` is the projective special linear group `(GL n R)/ Z(GL(n R))`. -/
abbrev PGL := ProjectiveGeneralLinearGroup'

/-- `PSL(n, R)` is the projective special linear group `SL(n, R)/Z(SL(n, R))`. -/
abbrev PSL := Matrix.ProjectiveSpecialLinearGroup




theorem FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod {p : ℕ} [Fact (Nat.Prime p)] (𝕂 : Type*)
  [Field 𝕂] [CharP 𝕂 p] [Finite 𝕂]
  (G : Subgroup (PGL (Fin 2) (AlgebraicClosure (ZMod p)))) [hG : Finite G] :
  IsCyclic G
  ∨
  ∃ n, Isomorphic G (DihedralGroup n)
  ∨
  Isomorphic G (alternatingGroup (Fin 4))
  ∨
  Isomorphic G (Equiv.Perm (Fin 5))
  ∨
  Isomorphic G (alternatingGroup (Fin 5))
  ∨
  Isomorphic G (PSL (Fin 2) (𝕂))
  ∨
  Isomorphic G (PGL (Fin 2) (𝕂)) := by
  let CharFpbar : CharP (AlgebraicClosure (ZMod p)) p := by infer_instance
  refine Or.elim (em' (p ∣ Nat.card G)) ?caseI ?caseII
  case caseII =>
    intro p_dvd_card_G
    -- rcases dickson_classification_theorem_class_II (AlgebraicClosure (ZMod p)) _ _ p _ _ p_dvd_card_G
    sorry
  case caseI =>
    sorry

-- #leansearch "not or."



-- implicit normality condition on Q

-- ∧ IsCyclic (Subgroup.map (@QuotientGroup.mk' G _ (Q.subgroupOf G) (by sorry)) ⊤) -- needs to know quotient is a group

-- (IsCyclic (QuotientGroup.Quotient.group Q (nN := by sorry)))

-- (vi) Q is elementary abelian, Q C G and G/Q is a cyclic group whose order is
--relatively prime to p.
