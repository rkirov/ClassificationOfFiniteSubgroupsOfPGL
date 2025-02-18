import Mathlib

open Matrix LinearMap Subgroup Function

open scoped MatrixGroups

variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R] (F : Type*) [Field F]

scoped[MatrixGroups] notation "SL"  => Matrix.SpecialLinearGroup

/-- A projective general linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveGeneralLinearGroup : Type _ :=
    GL n R ⧸ center (GL n R)

/-- `PGL n R` is the projective special linear group `(GL n R)/ Z(GL(n R))`. -/
abbrev PGL := ProjectiveGeneralLinearGroup

/-- `PSL(n, R)` is the projective special linear group `SL(n, R)/Z(SL(n, R))`. -/
abbrev PSL := Matrix.ProjectiveSpecialLinearGroup

def SL_monoidHom_GL  (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  SL n R →* GL n R := SpecialLinearGroup.toGL

def SL_monoidHom_PSL (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  SL n R →* PSL n R := QuotientGroup.mk' (center (SL n R))

def GL_monoidHom_PGL (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  GL n R →* PGL n R := QuotientGroup.mk' (center (GL n R))

def SL_monoidHom_PGL (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] :
  SL n R →*  PGL n R := (GL_monoidHom_PGL n R).comp (SL_monoidHom_GL n R)

lemma coe  {n : Type*}  [Fintype n] [DecidableEq n] (x : SpecialLinearGroup n R):
  SpecialLinearGroup.toGL x = (x : Matrix n n R) := rfl

lemma scalar_eq_smul_one (n : Type*) [Fintype n] [DecidableEq n] (R : Type*) [CommRing R] (r : R):
  (scalar n) r = r • 1 := by
  simp [smul_one_eq_diagonal]

lemma center_SL_le_ker (n : Type*) [Nonempty n] [Fintype n] [DecidableEq n]
  (R : Type*) [CommRing R] [NeZero (1 : R)] :
  center (SpecialLinearGroup n R) ≤ (SL_monoidHom_PGL n R).ker := by
  sorry

instance center_is_normal (n R : Type*) [Nonempty n] [Fintype n] [DecidableEq n]
  [CommRing R] [NeZero (1 : R)] : Subgroup.Normal (center (SpecialLinearGroup n R)) :=
  normal_of_characteristic (center (SL n R))

instance PGL_is_monoid  (n R : Type*) [Nonempty n] [Fintype n] [DecidableEq n]
  [CommRing R] [NeZero (1 : R)] : Monoid (ProjectiveGeneralLinearGroup n R) :=
  RightCancelMonoid.toMonoid

-- By the universal property the map from PSL n F to PGL n F is well defined
def PSL_monoidHom_PGL (n R : Type*) [Nonempty n] [Fintype n] [DecidableEq n]
  [CommRing R] [NeZero (1 : R)] :
  PSL n R →* PGL n R :=
  @QuotientGroup.lift (SL n R) _ (center (SL n R)) (center_is_normal n R) (PGL n R)
    (PGL_is_monoid n R) (SL_monoidHom_PGL n R) (center_SL_le_ker n R)

theorem SpecialLinearGroup.toGL_inj {n : Type*} [DecidableEq n] [Fintype n] {R : Type*} [CommRing R] : Injective (@SpecialLinearGroup.toGL n _ _ R _) := by
  sorry --ommited

theorem ker_SL_monoidHom_PGL_eq_center (n F : Type*) [hn₁ : Fintype n] [DecidableEq n]
  [Field F] [IsAlgClosed F] : (SL_monoidHom_PGL n R).ker = center (SL n R) := by sorry --ommited


theorem  Injective_PSL_monoidHom_PGL' (n F : Type*) [hn₁ : Fintype n] [DecidableEq n]
  [hn₂ : Nonempty n] [Field F] [IsAlgClosed F] :  Injective (PSL_monoidHom_PGL n F) := by
  dsimp [PSL_monoidHom_PGL]
  --refine Setoid.ker_lift_injective --(f := QuotientGroup.lift ((SL_monoidHom_PGL n F).ker) (SL_monoidHom_PGL n F))
  sorry
