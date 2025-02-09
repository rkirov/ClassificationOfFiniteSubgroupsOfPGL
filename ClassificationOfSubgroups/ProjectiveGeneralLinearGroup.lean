import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

set_option linter.style.longLine true
set_option autoImplicit false

universe u v w

open Matrix

open scoped MatrixGroups

variable {n : Type u} [DecidableEq n] [Fintype n] {R : Type v} [CommRing R] (F : Type w) [Field F]


scoped[MatrixGroups] notation "SL"  => Matrix.SpecialLinearGroup

def Matrix.transvection.toSL {i j : n} (hij : i ≠ j) (c : R): SL n R :=
  ⟨Matrix.transvection i j c, (det_transvection_of_ne i j hij (c : R))⟩


namespace Matrix.TransvectionStruct

open Matrix

def toSL (t : TransvectionStruct n R) : SL n R := Matrix.transvection.toSL t.hij t.c

def toGL (t : TransvectionStruct n R) : GL n R := Matrix.transvection.toSL t.hij t.c

end Matrix.TransvectionStruct

namespace GeneralLinearGroup

def scalar (n : Type*) [DecidableEq n] [Fintype n] (r : Rˣ) : GL n R :=
  Units.map (Matrix.scalar n).toMonoidHom r

/-- scalar matrix belongs to GL n R iff r is a unit -/
theorem coe_scalar_matrix (r : Rˣ) : Matrix.scalar n r.val = scalar n r := rfl

/-- `M` is a scalar matrix if it commutes with every nontrivial transvection (elementary matrix). -/
theorem mem_range_scalar_of_commute_transvectionStruct' {M : GL n R}
    (hM : ∀ t : TransvectionStruct n R, Commute t.toGL M):
    (M : Matrix n n R) ∈ Set.range (Matrix.scalar n) := by
  refine mem_range_scalar_of_commute_transvectionStruct ?_
  simp_rw [← Commute.units_val_iff] at hM
  exact hM

theorem mem_range_unit_scalar_of_mem_range_scalar_and_mem_general_linear_group {M : GL n R}
  (hM : (M : Matrix n n R) ∈ Set.range (Matrix.scalar n)) :
    ∃ r : Rˣ, scalar n r = M := by
    obtain ⟨r', hr'⟩ := hM
    have det_scalar : (Matrix.scalar n r').det = r'^(Nat.card n) := by simp
    have det_M_is_unit: IsUnit ((M : Matrix n n R).det) := by simp only [isUnits_det_units]
    rw [← hr', det_scalar] at det_M_is_unit
    by_cases hn : Nat.card n ≠ 0
    · have r'_is_unit : IsUnit r' := by rw [← isUnit_pow_iff hn]; exact det_M_is_unit
      obtain ⟨r, hr⟩ := r'_is_unit
      use r
      have h : scalar n r = Matrix.scalar n r' := by simp [scalar]; intro _n; exact hr
      ext
      rw [h, hr']
    · simp only [Nat.card_eq_fintype_card, ne_eq, Decidable.not_not] at hn
      use 1
      rw [scalar]; simp only [RingHom.toMonoidHom_eq_coe, _root_.map_one]
      ext
      have n_empty : IsEmpty n := by rw [← Fintype.card_eq_zero_iff, hn]
      rw [← units_eq_one M]


theorem mem_units_range_scalar_iff_commute_transvectionStruct {R : Type v} [CommRing R]
  (M : GL n R) : (∀ (A : GL n R), Commute A M) ↔ (∃ r : Rˣ, scalar n r = M) := by
  constructor
  · intro hM
    -- If M commutes with every matrix then it must commute with the transvection matrices
    have h₀ : ∀ (t : TransvectionStruct n R), Commute (t.toGL) M := fun t => hM t.toGL
    -- If M commutes with the transvection matrices,
    -- then M ∈ Set.range (Matrix.scalar n) where Set.range is Rˣ
    have h₁ : (M : Matrix n n R) ∈ Set.range ⇑(Matrix.scalar n) :=
      mem_range_scalar_of_commute_transvectionStruct' h₀
    have h₂ : ∃ r : Rˣ, scalar n r = M :=
      mem_range_unit_scalar_of_mem_range_scalar_and_mem_general_linear_group h₁
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

namespace Center

open Subgroup GeneralLinearGroup

theorem mem_center_general_linear_group_iff {M : GL n R} :
  M ∈ Subgroup.center (GL n R) ↔ (∃ r : Rˣ, scalar n r = M) := by
  rw [mem_center_iff]
  constructor
  · intro h
    rw [← mem_units_range_scalar_iff_commute_transvectionStruct]
    congr
  · intro h A
    have hA : (∀ (A : GL n R), Commute A M) :=
      (mem_units_range_scalar_iff_commute_transvectionStruct M).mpr h
    exact Commute.eq <| hA A

end Center

end GeneralLinearGroup

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

open Subgroup

/-- A projective general linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveGeneralLinearGroup : Type _ :=
    GL n R ⧸ center (GL n R)


/-- `PGL n R` is the projective special linear group `(GL n R)/ Z(GL(n R))`. -/
abbrev PGL := ProjectiveGeneralLinearGroup


open Matrix LinearMap Subgroup

open scoped MatrixGroups


variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

/-- A projective special linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveSpecialLinearGroup : Type _ :=
    SpecialLinearGroup n R ⧸ center (SpecialLinearGroup n R)

/-- `PSL(n, R)` is the projective special linear group `SL(n, R)/Z(SL(n, R))`. -/
abbrev PSL := ProjectiveSpecialLinearGroup


namespace Isomorphism

variable (n : ℕ) (F : Type u) [Field F] [IsAlgClosed F]

open Subgroup

def SL_monoidHom_PGL (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  SL n R →*  PGL n R where
  toFun S := QuotientGroup.mk' (center (GeneralLinearGroup n R)) S.toGL
  map_mul' S₁ S₂ := by simp
  map_one' := by simp

lemma coe  {n : Type*}  [Fintype n] [DecidableEq n] (x : SpecialLinearGroup n R):
  SpecialLinearGroup.toGL x = (x : Matrix n n R) := rfl

lemma center_SL_le_ker (n : Type*) [Nonempty n] [Fintype n] [DecidableEq n]
  (R : Type*) [CommRing R] [NeZero (1 : R)]:
  center (SpecialLinearGroup n R) ≤ (SL_monoidHom_PGL n R).ker := by
  intro x x_mem_center
  rw [SpecialLinearGroup.mem_center_iff] at x_mem_center
  obtain ⟨ω, hω, h⟩ := x_mem_center
  simp [MonoidHom.mem_ker, SL_monoidHom_PGL]
  rw [GeneralLinearGroup.Center.mem_center_general_linear_group_iff]
  have IsUnit_ω : IsUnit ω := IsUnit.of_pow_eq_one hω Fintype.card_ne_zero
  use IsUnit_ω.unit
  ext
  simp [← GeneralLinearGroup.coe_scalar_matrix, coe, ← h]

instance center_is_normal (n R : Type*) [Nonempty n] [Fintype n] [DecidableEq n]
  [CommRing R] [NeZero (1 : R)] : Subgroup.Normal (center (SpecialLinearGroup n R)) :=
  normal_of_characteristic (center (SL n R))

instance PGL_is_monoid  (n R : Type*) [Nonempty n] [Fintype n] [DecidableEq n]
  [CommRing R] [NeZero (1 : R)] : Monoid (ProjectiveGeneralLinearGroup n R) :=
  RightCancelMonoid.toMonoid

def PSL_monoidHom_PGL (n R : Type*) [Nonempty n] [Fintype n] [DecidableEq n]
  [CommRing R] [NeZero (1 : R)] :
  PSL n R →* PGL n R :=
  @QuotientGroup.lift (SL n R) _ (center (SL n R)) (center_is_normal n R) (PGL n R)
    (PGL_is_monoid n R) (SL_monoidHom_PGL n R) (center_SL_le_ker n R)

open Polynomial


lemma exists_SL_eq_scaled_GL_of_IsAlgClosed {n F : Type*} [hn₁ : Fintype n] [DecidableEq n]
  [hn₂ : Nonempty n] [Field F] [IsAlgClosed F] (G : GL n F) :
  ∃ c : Fˣ, ∃ S : SL n F,  c • S.toGL = G := by
  let P : F[X] := X^(Nat.card n) - C (det G.val)
  have nat_card_ne_zero : (Nat.card n) ≠ 0 := Nat.card_ne_zero.mpr ⟨hn₂, Fintype.finite hn₁⟩
  have deg_P_ne_zero : degree P ≠ 0 := by
    rw [Polynomial.degree_X_pow_sub_C]
    exact Nat.cast_ne_zero.mpr nat_card_ne_zero
    exact Nat.card_pos
  obtain ⟨c, hc⟩ := @IsAlgClosed.exists_root F _ _ P deg_P_ne_zero
  have c_ne_zero : c ≠ 0 := by
    rintro rfl
    simp [P] at hc
    have det_G_ne_zero : det G.val ≠ 0 := IsUnit.ne_zero <| isUnits_det_units G
    contradiction
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

open Function

lemma Bijective_PSL_monoidHom_PGL {n F : Type*} [hn₁ : Fintype n] [DecidableEq n]
  [hn₂ : Nonempty n] [Field F] [IsAlgClosed F] :  Bijective (PSL_monoidHom_PGL n F) := by
  refine ⟨?injective, ?surjective⟩
  case injective =>

    sorry
    -- rw [@injective_iff_map_eq_one']
    -- intro psl
    -- constructor
    -- · intro h
    --   simp [PSL_monoidHom_PGL] at h
    --   dsimp [PSL, ProjectiveSpecialLinearGroup] at psl
    --   rw [← @MonoidHom.mem_ker] at h
    --   simp [← @QuotientGroup.eq_one_iff] at h
    --   sorry
    -- · sorry
  case surjective =>
    sorry



noncomputable def GL_monoidHom_SL (n F : Type*) [Fintype n] [DecidableEq n] [Nonempty n]
  [Field F] [IsAlgClosed F] :
  GL n F →* SL n F where
  toFun G := by
    obtain c := (exists_SL_eq_scaled_GL_of_IsAlgClosed G).choose
    obtain S := (exists_SL_eq_scaled_GL_of_IsAlgClosed G).choose_spec.choose
    obtain h := (exists_SL_eq_scaled_GL_of_IsAlgClosed G).choose_spec.choose_spec
    use S
    exact SpecialLinearGroup.det_coe S
  map_mul' G₁ G₂ := by
    simp
    sorry
  map_one' := by
    simp
    sorry

def SL_monoidHom_PSL (n R : Type*) [Fintype n] [DecidableEq n] [Nonempty n] [CommRing R] :
  SL n R →* PSL n R := QuotientGroup.mk' (center (SL n R))


def GL_monoidHom_PSL (n F : Type*) [Fintype n] [DecidableEq n] [Nonempty n] [Field F] [IsAlgClosed F]  :
  GeneralLinearGroup n F →* ProjectiveSpecialLinearGroup n F := sorry--SL_monoidHom_PSL.comp GL_monoidHom_SL

instance mul_PSL {n : Type*} [Fintype n] [DecidableEq n] : Mul (PSL n F) := { mul := fun a _ ↦ a }

instance mul_PGL {n : Type*} [Fintype n] [DecidableEq n] : Mul (PGL n F) := { mul := fun a _ ↦ a }

-- We define the isomorphism between the projective general linear group and the projective special linear group
-- def PGL_iso_PSL (n F : Type*) [Fintype n] [DecidableEq n] [Nonempty n] [Field F] [IsAlgClosed F] :
--   PSL n F ≃* PGL n F := @MulEquiv.ofBijective (PSL n F) (PGL n F)

end Isomorphism
