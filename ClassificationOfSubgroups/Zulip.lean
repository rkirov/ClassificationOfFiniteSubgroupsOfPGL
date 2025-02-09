import Mathlib

variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]


open Matrix Subgroup

open scoped MatrixGroups

/-- A projective general linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveGeneralLinearGroup : Type _ :=
    GL n R ⧸ center (GL n R)


/-- `PGL n R` is the projective special linear group `(GL n R)/ Z(GL(n R))`. -/
abbrev PGL := ProjectiveGeneralLinearGroup





variable (n : Type u) [DecidableEq n] [Fintype n] (R : Type v) [CommRing R]

/-- A projective special linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveSpecialLinearGroup : Type _ :=
    SpecialLinearGroup n R ⧸ center (SpecialLinearGroup n R)

/-- `PSL(n, R)` is the projective special linear group `SL(n, R)/Z(SL(n, R))`. -/
abbrev PSL := _root_.ProjectiveSpecialLinearGroup


namespace Isomorphism

variable (n : ℕ) (F : Type u) [Field F] [IsAlgClosed F]



scoped[MatrixGroups] notation "SL"  => Matrix.SpecialLinearGroup

def SL_monoidHom_GL  (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  SL n R →* GL n R := SpecialLinearGroup.toGL

def GL_monoidHom_PGL (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  GL n R →* PGL n R := QuotientGroup.mk' (center (GL n R))

def SL_monoidHom_PGL (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  SL n R →*  PGL n R :=  MonoidHom.comp (GL_monoidHom_PGL n R) (SL_monoidHom_GL n R)

lemma coe  {n : Type*}  [Fintype n] [DecidableEq n] (x : SpecialLinearGroup n R):
  SpecialLinearGroup.toGL x = (x : Matrix n n R) := rfl

theorem mem_center_general_linear_group_iff {n : Type*} [Fintype n] [DecidableEq n] {M : GL n R} :
  M ∈ Subgroup.center (GL n R) ↔ (∃ r : Rˣ, scalar n r = M) := by sorry

lemma center_SL_le_ker (n : Type*) [Nonempty n] [Fintype n] [DecidableEq n]
  (R : Type*) [CommRing R] [NeZero (1 : R)]:
  center (SpecialLinearGroup n R) ≤ (SL_monoidHom_PGL n R).ker := by
  intro x x_mem_center
  rw [SpecialLinearGroup.mem_center_iff] at x_mem_center
  obtain ⟨ω, hω, h⟩ := x_mem_center
  simp [MonoidHom.mem_ker, SL_monoidHom_PGL, GL_monoidHom_PGL, SL_monoidHom_GL]
  rw [mem_center_general_linear_group_iff]
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

open Function

lemma Bijective_PSL_monoidHom_PGL {n F : Type*} [hn₁ : Fintype n] [DecidableEq n]
  [hn₂ : Nonempty n] [Field F] [IsAlgClosed F] :  Bijective (PSL_monoidHom_PGL n F) := by
  refine ⟨?injective, ?surjective⟩
  case injective =>
    rw [← @MonoidHom.ker_eq_bot_iff]
    rw [@eq_bot_iff]
    intro k k_in_ker
    simp [PSL_monoidHom_PGL] at k_in_ker
    rw [← @QuotientGroup.mk_one] at k_in_ker
    -- extract representative or equivalent somehow
    rw [← @MulActionHom.toQuotient_apply] at k_in_ker
    -- show representative is a root of unity
    rw [mem_bot]
    rw [← @QuotientGroup.mk_one]
    sorry
  case surjective =>
    intro pgl
    -- extract representative or equivalent somehow
    -- obtain ⟨c, S, h⟩ := exists_SL_eq_scaled_GL_of_IsAlgClosed G
    sorry
