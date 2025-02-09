import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace Matrix

universe u v w

open Matrix

open scoped MatrixGroups

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R] (F : Type w) [Field F]

variable (i j : n) (c : R)

namespace SpecialLinearGroup

scoped[MatrixGroups] notation "SL"  => Matrix.SpecialLinearGroup

def transvection (hij : i ≠ j) : SL n R :=
  ⟨Matrix.transvection i j c, (det_transvection_of_ne i j hij (c : R))⟩

end SpecialLinearGroup

namespace TransvectionStruct

def toSL (t : TransvectionStruct n R) : SL n R := ⟨t.toMatrix, by simp⟩

def toGL (t : TransvectionStruct n R) : GL n R := t.toSL

end TransvectionStruct

namespace GeneralLinearGroup

def transvection (hij : i ≠ j) : GL n R :=
  (SpecialLinearGroup.transvection n R i j c hij).toGL

def scalar (r : Rˣ) : GL n R :=
  Units.map (Matrix.scalar n).toMonoidHom r

/-- scalar matrix belongs to GL n R iff r is a unit -/
theorem coe_scalar_matrix (r : Rˣ) : Matrix.scalar n r.val = scalar n R r := rfl

/-- `M` is a scalar matrix if it commutes with every nontrivial transvection (elementary matrix). -/
theorem mem_range_scalar_of_commute_transvectionStruct' {M : GL n R}
    (hM : ∀ t : TransvectionStruct n R, Commute t.toGL M):
    (M : Matrix n n R) ∈ Set.range (Matrix.scalar n) := by
  refine mem_range_scalar_of_commute_transvectionStruct ?_
  simp_rw [← Commute.units_val_iff] at hM
  exact hM

theorem mem_range_unit_scalar_of_mem_range_scalar_and_mem_general_linear_group {M : GL n R} (hM : (M : Matrix n n R) ∈ Set.range (Matrix.scalar n)) :
    ∃ r : Rˣ, scalar n R r = M := by
    obtain ⟨r', hr'⟩ := hM
    have det_scalar : (Matrix.scalar n r').det = r'^(Nat.card n) := by simp
    have det_M_is_unit: IsUnit ((M : Matrix n n R).det) := by simp only [isUnits_det_units]
    rw [← hr', det_scalar] at det_M_is_unit
    by_cases hn : Nat.card n ≠ 0
    · have r'_is_unit : IsUnit r' := by rw [← isUnit_pow_iff hn]; exact det_M_is_unit
      obtain ⟨r, hr⟩ := r'_is_unit
      use r
      have h : scalar n R r = Matrix.scalar n r' := by simp [scalar]; intro _n; exact hr
      rw [ext_iff, Matrix.ext_iff, h, hr']
    · simp only [Nat.card_eq_fintype_card, ne_eq, Decidable.not_not] at hn
      use 1
      rw [scalar]; simp only [RingHom.toMonoidHom_eq_coe, _root_.map_one]
      ext i j
      have n_empty : IsEmpty n := by rw [← Fintype.card_eq_zero_iff, hn]
      rw [← units_eq_one M]


theorem mem_units_range_scalar_iff_commute_transvectionStruct {R : Type v} [CommRing R] (M : GL n R) : (∀ (A : GL n R), Commute A M) ↔ (∃ r : Rˣ, scalar n R r = M) := by
  constructor
  · intro hM
    -- if M commutes with every matrix then it must commute with the transvection matrices
    have h₀ : ∀ (t : TransvectionStruct n R), Commute (t.toGL) M := fun t => hM t.toGL
    -- if M commutes with the transvection matrices then M ∈ Set.range (Matrix.scalar n) where Set.range is Rˣ
    have h₁ : (M : Matrix n n R) ∈ Set.range ⇑(Matrix.scalar n) := mem_range_scalar_of_commute_transvectionStruct' _ _ h₀--mem_range_unit_scalar_of_commute_transvectionStruct n R h₀
    have h₂ : ∃ r : Rˣ, scalar n R r = M := mem_range_unit_scalar_of_mem_range_scalar_and_mem_general_linear_group n R h₁
    obtain ⟨r, rfl⟩ := h₂
    use r
  · intro h A
    obtain ⟨r, rfl⟩ := h
    ext i j
    rw [
      GeneralLinearGroup.coe_mul, GeneralLinearGroup.coe_mul,
      ← coe_scalar_matrix, scalar_commute
      ]
    exact fun r' ↦ Commute.all (↑r) r'

instance : Group (GL n R) := Units.instGroup

namespace Center

open Subgroup GeneralLinearGroup

theorem mem_center_general_linear_group_iff {M : GL n R} : M ∈ Subgroup.center (GL n R) ↔ (∃ r : Rˣ, scalar n R r = M) := by
  rw [mem_center_iff]
  constructor
  · intro h
    rw [← mem_units_range_scalar_iff_commute_transvectionStruct]
    congr
  · intro h A
    have hA : (∀ (A : GL n R), Commute A M) := (mem_units_range_scalar_iff_commute_transvectionStruct n M).mpr h
    exact Commute.eq <| hA A

end Center

instance hasInv : Inv (GeneralLinearGroup n R) :=
  ⟨fun A => ⟨
    ((det A)⁻¹ • adjugate A.1),
    A,
    by
    rw [smul_mul, adjugate_mul]
    exact inv_smul_smul (det A) 1,
    by
    rw [mul_eq_one_comm, smul_mul, adjugate_mul]
    exact inv_smul_smul (det A) 1
    ⟩
  ⟩

-- instance hasInv : Inv (GeneralLinearGroup n R) := by exact Units.instInv

end GeneralLinearGroup

namespace ProjectiveGeneralLinearGroup

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

open Subgroup

/-- A projective general linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveGeneralLinearGroup : Type _ :=
    GL n R ⧸ center (GL n R)


variable (n : ℕ)

/-- `PGL n R` is the projective special linear group `(GL n R)/ Z(GL(n R))`. -/
notation "PGL(" n ", " R ")" => ProjectiveGeneralLinearGroup (Fin n) R

end ProjectiveGeneralLinearGroup


open Matrix LinearMap Subgroup

open scoped MatrixGroups


variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

/-- A projective special linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveSpecialLinearGroup : Type _ :=
    SpecialLinearGroup n R ⧸ center (SpecialLinearGroup n R)

/-- `PSL(n, R)` is the projective special linear group `SL(n, R)/Z(SL(n, R))`. -/
scoped[MatrixGroups] notation "PSL(" n ", " R ")" => Matrix.ProjectiveSpecialLinearGroup (Fin n) R


namespace Isomorphism

open ProjectiveGeneralLinearGroup


variable (n : ℕ) (F : Type u) [Field F] [IsAlgClosed F]

#leansearch "MulEquiv from bijective homomorphism?"

#check MulEquiv.ofBijective

#check MulEquiv.ofBijective_apply

open Subgroup

def MonoidHom_PSL_into_PGL : SpecialLinearGroup (Fin n) R ⧸ center (SpecialLinearGroup (Fin n) R) →* GL (Fin n) R ⧸ center (GL (Fin n) R) where
  toFun S := by
    obtain s := @S.exists_rep.choose
    obtain hs := @S.exists_rep.choose_spec
    let g := s.toGL
    let G := QuotientGroup.mk' (center (GL (Fin n) R)) S.exists_rep.choose.toGL
    --ideally use G
    sorry
  map_one' := sorry
  map_mul' := sorry

def GL_into_PGL {n :Type*} [Fintype n] [DecidableEq n] :
  GeneralLinearGroup n R →* ProjectiveGeneralLinearGroup n R where
  toFun := fun G => QuotientGroup.mk' (center (GeneralLinearGroup n R)) G
  map_one' := sorry
  map_mul' := sorry


def φ (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] : SpecialLinearGroup n R →*  ProjectiveGeneralLinearGroup n R where
  toFun := fun S => QuotientGroup.mk' (center (GeneralLinearGroup n R)) S.toGL
  map_mul' S₁ S₂ := by simp
  map_one' := by simp



#check QuotientGroup.lift

lemma coe  {n : Type*}  [Fintype n] [DecidableEq n] (x : SpecialLinearGroup n R): SpecialLinearGroup.toGL x = (x : Matrix n n R) := rfl

lemma center_SL_le_ker (n : Type*) [Nonempty n] [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] [NeZero (1 : R)]: center (SpecialLinearGroup n R) ≤ (φ n R).ker := by
  intro x x_mem_center
  rw [SpecialLinearGroup.mem_center_iff] at x_mem_center
  obtain ⟨ω, hω, h⟩ := x_mem_center
  simp [MonoidHom.mem_ker, φ]
  rw [GeneralLinearGroup.Center.mem_center_general_linear_group_iff]
  have IsUnit_ω : IsUnit ω := IsUnit.of_pow_eq_one hω Fintype.card_ne_zero
  use IsUnit_ω.unit
  ext
  simp [← GeneralLinearGroup.coe_scalar_matrix, coe, ← h]

instance center_is_normal (n R : Type*) [Nonempty n] [Fintype n] [DecidableEq n] [CommRing R] [NeZero (1 : R)] : Subgroup.Normal (center (SpecialLinearGroup n R)) := normal_of_characteristic (center (SL n R))

instance PGL_is_monoid  (n R : Type*) [Nonempty n] [Fintype n] [DecidableEq n] [CommRing R] [NeZero (1 : R)] : Monoid (ProjectiveGeneralLinearGroup n R) := RightCancelMonoid.toMonoid

def PSL_monoidHom_PGL (n R : Type*) [Nonempty n] [Fintype n] [DecidableEq n] [CommRing R] [NeZero (1 : R)] : ProjectiveSpecialLinearGroup n R →* ProjectiveGeneralLinearGroup n R :=
  @QuotientGroup.lift (SpecialLinearGroup n R) _ (center (SpecialLinearGroup n R)) (center_is_normal n R) (ProjectiveGeneralLinearGroup n R) (PGL_is_monoid n R) (φ n R) (center_SL_le_ker n R)

open Polynomial

lemma exists_SL (n F : Type*) [Fintype n] [DecidableEq n] [Nonempty n] [Field F] [IsAlgClosed F] (G : GeneralLinearGroup n F) : ∃ c : Fˣ, ∃ S : SpecialLinearGroup n F, c • S.toGL = G := by
  let P : F[X] := X^(Nat.card n) - C (det G.val)
  have deg_P_ne_zero : degree P ≠ 0 := by sorry
  obtain ⟨c, hc⟩ := @IsAlgClosed.exists_root F _ _ P deg_P_ne_zero
  have c_ne_zero : c ≠ 0 := by sorry
  have IsUnit_c : IsUnit c := by exact Ne.isUnit c_ne_zero
  have hc' : ∃ c : Fˣ, c^(Nat.card n) = det G.val := by
    use IsUnit_c.unit
    simp [P, sub_eq_zero] at hc
    simp [hc]
  obtain ⟨c, hc⟩ := hc'
  have det_inv_c_G_eq_one : det (c⁻¹ • G).1 = (1 : F) := by
    simp [← hc, inv_smul_eq_iff, Units.smul_def]
  use c, ⟨(c⁻¹ • G), det_inv_c_G_eq_one⟩
  ext
  simp [coe]

def GL_into_SL (n F : Type*) [Fintype n] [DecidableEq n] [Nonempty n] [Field F] [IsAlgClosed F] : GeneralLinearGroup n F →* SpecialLinearGroup n F where
  toFun := fun G => sorry
  map_mul' := sorry
  map_one' := sorry

def GL_into_PSL (n F : Type*) [Fintype n] [DecidableEq n] [Nonempty n] [Field F] [IsAlgClosed F]  : GeneralLinearGroup n F →* ProjectiveSpecialLinearGroup n F :=
  by sorry


#check MulEquiv.ofBijective
-- We define the isomorphism between the projective general linear group and the projective special linear group
def iso (n F : Type*) [Fintype n] [DecidableEq n] [Nonempty n] [Field F] [IsAlgClosed F] : ProjectiveGeneralLinearGroup n F ≃* ProjectiveSpecialLinearGroup n F where
  toFun := sorry
  invFun := PSL_monoidHom_PGL n F
  left_inv := sorry
  right_inv := sorry
  map_mul' := sorry

#leansearch "center of special linear group?"



#check QuotientGroup.map

end Isomorphism

end Matrix
