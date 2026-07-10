import ClassificationOfSubgroups.Ch4_PGLIsoPSLOverAlgClosedField.ProjectiveGeneralLinearGroup
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_A_MaximalAbelianSubgroup
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

set_option linter.style.longLine true
set_option maxHeartbeats 0

open Matrix Subgroup LinearMap

open scoped MatrixGroups


/- Lemma 3.1 -/
-- The original statement here was false: `H < K` gives `H ≤ K ≤ normalizer K`
-- (`Subgroup.le_normalizer`), directly contradicting `¬ H ≤ normalizer K`.
-- Restated to match Butler's actual Lemma 3.1 (`case2q`, tex ~line 1277): a proper
-- subgroup of a finite `p`-group `K` is strictly contained in its normalizer inside `K`.
lemma IsPGroup.lt_normalizer_subgroupOf {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] (G : Subgroup SL(2,F)) (H K : Subgroup ↥G) [Finite ↥K] (hK : IsPGroup p ↥K)
  (H_lt_K : H < K) :
    H.subgroupOf K < normalizer ((H.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  have hnc : NormalizerCondition ↥K := Group.normalizerCondition_of_isNilpotent (G := ↥K)
    (h := hK.isNilpotent)
  have hne : H.subgroupOf K ≠ ⊤ :=
    fun heq => H_lt_K.ne (le_antisymm H_lt_K.le (Subgroup.subgroupOf_eq_top.mp heq))
  exact hnc _ (lt_top_iff_ne_top.mpr hne)

open MaximalAbelianSubgroup


/- Lemma 3.2 -/
lemma Sylow.not_normal_subgroup_of_G {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] (G K : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G)
  (hK : K ∈ MaximalAbelianSubgroupsOf G)
  (hQK : map G.subtype (normalizer (Q.toSubgroup : Set ↥G)) = (map G.subtype Q.toSubgroup) ⊔ K) :
  ¬ Normal Q.toSubgroup := by
  sorry

/- Lemma 3.3 -/
-- `R` is unused elsewhere in this development, so it is restructured here as a `Subfield F`
-- (rather than a bare `Set F`): the fixed field of the `k`-th iterated Frobenius, i.e. the
-- equalizer of `x ↦ x ^ p ^ k` and `id`. This is definitionally the set
-- `{x : F | x ^ p ^ k - x = 0}` (via `sub_eq_zero`), and packaging it as a `Subfield` gets
-- the `Field` instance for free from `Subfield.toField`.
def R (F : Type*) [Field F] (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] (k : ℕ+) : Subfield F :=
  RingHom.eqLocusField (iterateFrobenius F p (k : ℕ)) (RingHom.id F)

instance field_R {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] {k : ℕ+} : Field (R F p k) := Subfield.toField (R F p k)

/- Lemma 3.4 -/
noncomputable instance Fintype_GL {F : Type*} {n : ℕ} [Field F] [Fintype F] :
    Fintype (GL (Fin n) F) := by
  exact Fintype.ofFinite (GL (Fin n) F)

theorem GL_card {q : ℕ} {F : Type*} [Field F] [Fintype F] (hq : Fintype.card F = q) :
    Fintype.card (GL (Fin 2) F)= (q ^ 2 - 1) * (q ^ 2 - q) := by
  rw [← Nat.card_eq_fintype_card]
  rw [Matrix.card_GL_field]
  simp [hq]

-- Matrix.card_SL_field seems to be missing from mathlib
-- NOTE: as originally stated (no hypothesis on `n`) this is false at `n = 0` whenever
-- `Fintype.card 𝔽 > 2`: `GL (Fin 0) 𝔽` and `SL (Fin 0) 𝔽` both have cardinality `1`, but
-- `1 / (Fintype.card 𝔽 - 1) = 0 ≠ 1` by `ℕ`-division. Restated with `n ≠ 0` (the only
-- caller, `SL_card` below, uses `n = 2`).
lemma card_SL_field {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] (n : ℕ) (hn : n ≠ 0) :
  Nat.card (SL (Fin n) 𝔽) = Nat.card (GL (Fin n) 𝔽) / (Fintype.card 𝔽 - 1) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hsurj : Function.Surjective (GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ) :=
    GeneralLinearGroup.det_surjective
  -- `SL (Fin n) 𝔽` is in bijection with `ker (det : GL (Fin n) 𝔽 →* 𝔽ˣ)`.
  have hequiv : Nat.card (SL (Fin n) 𝔽)
      = Nat.card (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ)) := by
    apply Nat.card_congr
    exact
    { toFun := fun A => ⟨(A : GL (Fin n) 𝔽), by
          rw [MonoidHom.mem_ker]; exact SpecialLinearGroup.coeToGL_det A⟩
      invFun := fun B => ⟨(B.1 : Matrix (Fin n) (Fin n) 𝔽), by
          have h : GeneralLinearGroup.det (B.1 : GL (Fin n) 𝔽) = 1 := B.2
          have h2 := congrArg Units.val h
          simpa [GeneralLinearGroup.val_det_apply] using h2⟩
      left_inv := fun A => by
          apply Subtype.ext; rfl
      right_inv := fun B => by
          apply Subtype.ext; apply Units.ext; rfl }
  have hcard : Nat.card (GL (Fin n) 𝔽) =
      Nat.card (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ))
        * (Fintype.card 𝔽 - 1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ)),
      Nat.card_congr (QuotientGroup.quotientKerEquivRange
        (GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ)).toEquiv,
      MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_units,
      Nat.card_eq_fintype_card, mul_comm]
  have hpos : 0 < Fintype.card 𝔽 - 1 := by
    have := Fintype.one_lt_card (α := 𝔽); omega
  rw [hequiv]
  exact (Nat.div_eq_of_eq_mul_left hpos hcard).symm

noncomputable instance Fintype_SL {F : Type*} {n : ℕ} [Field F] [Fintype F] :
    Fintype (SL (Fin n) F) := by
  exact Fintype.ofFinite (SL(n, F))

theorem SL_card {q : ℕ} {F : Type*} [Field F] [Fintype F]
    (hq : Fintype.card F = q) (hqone: q > 1): Fintype.card SL(2, F) = (q ^ 2 - 1) * q := by
  rw [← Nat.card_eq_fintype_card]
  rw [card_SL_field 2 (by norm_num)]
  simp [hq]
  rw [GL_card hq]
  have : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, pow_two]
    simp
  rw [this]
  ring_nf
  apply Nat.mul_div_left (q * (q ^ 2 - 1)) (by exact Nat.zero_lt_sub_of_lt hqone)

/- Lemma 3.5. Correspondence theorem -/
#check QuotientGroup.comapMk'OrderIso

def Isomorphic (G H : Type*) [Group G] [Group H] :=
  Nonempty (G ≃* H)

/-
When $s = 1$ and $t = 0$
-/
lemma case_I {F : Type*} {p : ℕ} [Field F] [CharP F p ] (G : Subgroup SL(2,F)) [Finite G]
  (Q : Sylow p G) (Q_ne_G : (⊤ : Subgroup G) ≠ Q.toSubgroup)
  (hQ : IsElementaryAbelian p Q.toSubgroup) [Normal Q.toSubgroup] :
  IsCyclic (G ⧸ Q.toSubgroup) ∧ Nat.Coprime p (Nat.card (G ⧸ Q.toSubgroup)) := by sorry

/-
When $s = t = 1$
-/
lemma case_II {F : Type*} {p : ℕ} [Field F] [CharP F p ]
  (G : Subgroup SL(2,F)) [Finite G] (hG : Nat.Coprime p (Nat.card G)) :
  Isomorphic G SL(2, ZMod 3) ∨ ∃ n, Odd n ∧ Isomorphic G (DihedralGroup (4*n)) := by sorry

/-
When $s = t = 0$
-/
lemma case_III {F : Type*} {p : ℕ} [Field F] [CharP F p ]
  (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G) :
  Isomorphic G ((Subgroup.map G.subtype Q.toSubgroup) ⊔ (center SL(2,F)) :) := by sorry

/-
When $s = 0$ and $t = 1$
-/
lemma case_IV {F : Type*} {p : ℕ} [Field F] [CharP F p] (G : Subgroup SL(2,F)) [Finite G] :
 (p = 2 ∧ (∃ n, Odd n ∧ Isomorphic G (DihedralGroup (2*n))))
 ∨
 (p = 3) ∧ Isomorphic G (SL(2, ZMod 3)) := by sorry


-- We first need to define the homomorphism of
-- SL(2, GaloisField p k) into SL(2, GaloisField p (2*k))

open Polynomial

/- Embed GF(p^k) into GF(p^m) where k ∣ m -/
variable {p : ℕ} [hp : Fact (Nat.Prime p)] {n m : ℕ+}


noncomputable
abbrev GaloisField.polynomial (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ+) :
  (ZMod p)[X] := X ^ p ^ n.val - X


lemma GaloisField.polynomial_ne_zero : GaloisField.polynomial p n ≠ 0 := by
  rw [GaloisField.polynomial]
  exact FiniteField.X_pow_card_pow_sub_X_ne_zero (ZMod p) n.ne_zero hp.out.one_lt

lemma GaloisField.splits_of_dvd (hn : n ∣ m) :
    Splits ((GaloisField.polynomial p n).map (algebraMap (ZMod p) (GaloisField p m))) := by
  have hinj : Function.Injective (algebraMap (ZMod p) (GaloisField p m)) :=
    (algebraMap (ZMod p) (GaloisField p m)).injective
  have hsk : Splits ((GaloisField.polynomial p m).map (algebraMap (ZMod p) (GaloisField p m))) := by
    haveI : Fintype (GaloisField p m) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField p m) = p ^ (m : ℕ) := by
      rw [Fintype.card_eq_nat_card]; exact GaloisField.card p m m.pos.ne'
    have h := IsSplittingField.splits (L := GaloisField p m)
      (X ^ Fintype.card (GaloisField p m) - X : (ZMod p)[X])
    rwa [hcard] at h
  have hdvd_m : (X ^ (p ^ m.val - 1) - 1 : (ZMod p)[X]) ∣ GaloisField.polynomial p m := by
    refine ⟨X, ?_⟩
    suffices (X : (ZMod p)[X]) ^ p ^ m.val = X ^ (p ^ m.val - 1 + 1) by
      simpa [GaloisField.polynomial, sub_mul, ← pow_succ]
    rw [tsub_add_cancel_of_le]
    exact Nat.pow_pos (Nat.Prime.pos Fact.out)
  have hsk' : Splits ((X ^ (p ^ m.val - 1) - 1 : (ZMod p)[X]).map
      (algebraMap (ZMod p) (GaloisField p m))) :=
    Splits.of_dvd hsk ((Polynomial.map_ne_zero_iff hinj).mpr polynomial_ne_zero)
      (Polynomial.map_dvd _ hdvd_m)
  obtain ⟨k, rfl⟩ := hn
  have hd : (p ^ n.val - 1) ∣ (p ^ (n.val * k) - 1) := by
    refine Nat.pow_sub_one_dvd_pow_sub_one p ?_
    exact dvd_mul_right _ _
  have hdx : (X : (ZMod p)[X]) ^ (p ^ n.val - 1) - 1 ∣ X ^ (p ^ (n.val * k) - 1) - 1 := by
    obtain ⟨j, hj⟩ := hd
    simp_rw [hj, pow_mul]
    exact sub_one_dvd_pow_sub_one _ j
  have hbig_ne : (X ^ (p ^ (n.val * k) - 1) - 1 : (ZMod p)[X]) ≠ 0 := by
    refine Monic.ne_zero_of_ne (zero_ne_one' (ZMod p)) ?_
    refine monic_X_pow_sub ?_
    simp [hp.out.one_lt]
  have hs' : Splits ((X ^ (p ^ n.val - 1) - 1 : (ZMod p)[X]).map
      (algebraMap (ZMod p) (GaloisField p (n * k)))) :=
    Splits.of_dvd hsk' ((Polynomial.map_ne_zero_iff hinj).mpr hbig_ne) (Polynomial.map_dvd _ hdx)
  have hexp : p ^ n.val - 1 + 1 = p ^ n.val :=
    tsub_add_cancel_of_le (Nat.pow_pos (Nat.Prime.pos Fact.out))
  have hfact : GaloisField.polynomial p n = X * (X ^ (p ^ n.val - 1) - 1) := by
    rw [GaloisField.polynomial, mul_sub, mul_one, ← pow_succ', hexp]
  rw [hfact, Polynomial.map_mul, Polynomial.map_X]
  exact Splits.mul Splits.X hs'



noncomputable
def GaloisField.algHom_of_dvd (hn : n ∣ m) : GaloisField p n →ₐ[ZMod p] GaloisField p m :=
  Polynomial.SplittingField.lift _ (splits_of_dvd hn)


-- (x) The group hSL(2, Fq ), dπ i, where SL(2, Fq ) C hSL(2, Fq ), dπ i.
noncomputable def GaloisField_ringHom (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ+) :=
  (@GaloisField.algHom_of_dvd p _ k (2*k) (dvd_mul_left k 2)).toRingHom


noncomputable def SL2_monoidHom_SL2  {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ+} :
  SL(2, GaloisField p k.val) →* SL(2, GaloisField p (2* k.val)) :=
    Matrix.SpecialLinearGroup.map
      (@GaloisField.algHom_of_dvd p _ k (2*k) (dvd_mul_left k 2)).toRingHom

open SpecialMatrices

noncomputable def SL2_join_d (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ+) (π : (GaloisField p (2* k.val))ˣ ) :=
 (Subgroup.map (@SL2_monoidHom_SL2 p _ k) (⊤ : Subgroup SL(2, GaloisField p k.val)))
  ⊔
  Subgroup.closure { d π }


lemma case_V {F : Type*} {p : ℕ} [Fact (Nat.Prime p)] [Field F] [CharP F p]
  (G : Subgroup SL(2,F)) [Finite G] :
  ∃ k : ℕ+, Isomorphic G SL(2, GaloisField p k.val)
  ∨
  ∃ k : ℕ+, ∃ π : (GaloisField p (2 * k.val))ˣ, Isomorphic G (SL2_join_d p k π)
  ∨
  Isomorphic G SL(2, ZMod 5) := by sorry

inductive Symbols
 | x
 | y

open FreeGroup Symbols PresentedGroup

/-
Relations for the group presentation ⟨x, y | x^n = y^2, y * x * y⁻¹ = x⁻¹ ⟩
-/
def Relations (n : ℕ) : Set (FreeGroup (Symbols)) :=
  {.of x ^ n * (.of y)⁻¹ * (.of y)⁻¹ } ∪
  {.of y * .of x * (.of y)⁻¹ * .of x }

abbrev D (n : ℕ) :=
  PresentedGroup <| Relations n

lemma case_VI {F : Type*} {p : ℕ} [Fact (Nat.Prime p)] [Field F] [CharP F p]
  (G : Subgroup SL(2,F)) [Finite G] :
  ∃ n, Even n ∧ Isomorphic G (D n)
  ∨
  Isomorphic G (GL (Fin 2) (ZMod 5))
  ∨
  Isomorphic G SL(2, ZMod 5) := by sorry


 -- (v) Ŝ₄ , the representation group of S4 in which the transpositions correspond to
-- the elements of order 4.

instance five_prime : Fact (Nat.Prime 5) := { out := by decide }

/- Theorem 3.6 -/
-- ANCHOR: dicksons_classification_theorem_class_I
theorem dicksons_classification_theorem_class_I {F : Type*} [Field F] [IsAlgClosed F]
  {p : ℕ} [CharP F p] (hp : Prime p) (G : Subgroup (SL(2,F)))  [Finite G]
  (hp' : p = 0 ∨ Nat.Coprime (Nat.card G) p) :
  IsCyclic G ∨
  Isomorphic G (DihedralGroup n)
  ∨
  Isomorphic G SL(2, ZMod 3)
  ∨
  Isomorphic G SL(2, ZMod 5)
  ∨
  Isomorphic G (GL (Fin 2) (ZMod 3))
  := by sorry
-- ANCHOR_END: dicksons_classification_theorem_class_I

-- Ŝ₄ is isomorphic to GL₂(F₃)

lemma card_GaloisField_dvd_card_GaloisField (p : ℕ) [Fact (Nat.Prime p)] {m n : ℕ+}
  (m_dvd_n : m ∣ n) :  Nat.card (GaloisField p m.val) ∣ Nat.card (GaloisField p n.val) := by
  rw [GaloisField.card p m m.ne_zero, GaloisField.card p n n.ne_zero]
  apply pow_dvd_pow
  suffices m.val ∣ n.val by exact Nat.le_of_dvd n.prop this
  exact PNat.dvd_iff.mp m_dvd_n

-- ANCHOR: dicksons_classification_theorem_class_II
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
-- ANCHOR_END: dicksons_classification_theorem_class_II



variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

open Matrix LinearMap Subgroup

open scoped MatrixGroups


/-- A projective general linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveGeneralLinearGroup' : Type _ :=
    GL n R ⧸ center (GL n R)



-- ANCHOR: FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod
theorem FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod {p : ℕ}
  [Fact (Nat.Prime p)] (𝕂 : Type*) [Field 𝕂] [CharP 𝕂 p] [Finite 𝕂]
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
    sorry
-- ANCHOR_END: FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod

#min_imports
