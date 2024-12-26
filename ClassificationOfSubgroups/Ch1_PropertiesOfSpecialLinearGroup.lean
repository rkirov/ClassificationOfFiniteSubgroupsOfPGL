import Mathlib
import ClassificationOfSubgroups.SpecialCases


set_option linter.style.longLine true

universe u



open Matrix MatrixGroups

variable
  (F : Type u) [Field F]
  (n : Type u) [Fintype n]
  (R : Type u) [CommRing R]

instance : Group SL(2,F) := by infer_instance

local notation:1024 "↑ₘ" A:1024 => ((A : GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)

lemma Matrix.fin_two_eq { R: Type*} [CommSemiring R] {M N : Matrix (Fin 2) (Fin 2) R}
  (h₀₀ : M 0 0 = N 0 0)(h₀₁ : M 0 1 = N 0 1)(h₁₀ : M 1 0 = N 1 0)(h₁₁ : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h₀₀
  · exact h₀₁
  · exact h₁₀
  · exact h₁₁

@[ext]
lemma SL2_ext (A B : SL(2,F))
    (h00 : A.1 0 0 = B.1 0 0) (h01 : A.1 0 1 = B.1 0 1) (h10 : A.1 1 0 = B.1 1 0)
    (h11 : A.1 1 1 = B.1 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

namespace SpecialMatrices

def T {F : Type*} [Field F] (τ : F): SL(2,F) :=
  ⟨!![1, 0; τ, 1], by simp⟩

@[simp]
lemma T_0_eq_one : T (0 : F) = 1 := by ext <;> rfl

def D {F : Type*} [Field F] (δ : Fˣ) : SL(2, F) :=
  ⟨!![(δ : F), (0 : F); (0 :F) , (δ⁻¹ : F)], by norm_num⟩

lemma D_eq_diagonal (δ : Fˣ) :
  (D δ : Matrix (Fin 2) (Fin 2) F) = diagonal (fun i ↦ if i.val = 0 then (δ : F) else δ⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D]

@[simp]
lemma D_one_eq_one : D (1 : Fˣ) = 1 := by ext <;> simp [D]

@[simp]
lemma D_neg_one_eq_neg_one : D (-1 : Fˣ) = -1 := by ext <;> simp [D, inv_neg_one]

lemma D_coe_eq : (D (δ : Fˣ) : Matrix (Fin 2) (Fin 2) F) = !![(δ : F), 0; 0, δ⁻¹] := by
  apply Matrix.fin_two_eq
  repeat' simp [D]

lemma D_0_0_is_unit (δ : Fˣ) : IsUnit ((D δ) 0 0) := by simp [D]

def W {F : Type*} [Field F] : SL(2, F) :=
  ⟨!![0,1;-1,0], by norm_num⟩

def DT {F : Type*} [Field F] (δ : Fˣ) (τ : F) : SL(2, F) :=
  ⟨!![δ, 0; τ * δ⁻¹, δ⁻¹], by norm_num⟩

def DW {F : Type*} [Field F] (δ : Fˣ) : SL(2,F) :=
  ⟨!![0, δ; -δ⁻¹, 0], by norm_num⟩

lemma D_mul_T_eq_DT (δ : Fˣ) (τ : F) : D δ * T τ = DT δ τ := by ext <;> simp [D, T, DT, mul_comm]

lemma D_mul_W_eq_DW (δ : Fˣ) : D δ * W = DW δ := by ext <;> simp [D, W, DW]

@[simp]
lemma inv_D_eq (δ : Fˣ) : (D δ)⁻¹ = D (δ⁻¹) := by simp [Matrix.SpecialLinearGroup.SL2_inv_expl, D]; rfl

@[simp]
lemma inv_T_eq (τ : F) : (T τ)⁻¹ = T (-τ) := by simp [Matrix.SpecialLinearGroup.SL2_inv_expl, T]; rfl


end SpecialMatrices


/-
Lemma 1.1. For any ω, ρ ∈ F ∗ and τ, µ ∈ F we have:
(i) D δ * D ρ = D (δ * ρ),
(ii) T τ *  T μ = T (τ + µ),
(iii) D δ * T τ * (D δ)⁻¹ = T (τ * δ⁻²),
(iv) W * D δ * W⁻¹ = (D δ)⁻¹.
-/
open SpecialMatrices
-- (i)
lemma lemma_1_1_i (δ ρ : Fˣ) : D δ * D ρ = D (δ * ρ) := by ext <;> simp [D, mul_comm]

-- (ii)
lemma lemma_1_1_ii (τ μ : F) : T τ * T μ = T (τ + μ) := by ext <;> simp [T]

-- (iii)
lemma lemma_1_1_iii (δ : Fˣ) (τ : F) : D δ * T τ * (D δ)⁻¹ = T (τ * δ⁻¹ * δ⁻¹) := by simp; ext <;> simp [T, D, mul_comm]

-- (iv)
lemma lemma_1_1_iv (δ : Fˣ) : W * (D δ) * W⁻¹ = (D δ)⁻¹ := by simp; ext <;> simp [D, W]

/- Lemma 1.2.1.1-/
def subgroupGeneratedByD (F : Type*) [Field F] : Subgroup SL(2,F) where
  carrier := { D δ | δ : Fˣ }
  mul_mem' := by
              intro S Q hS hQ
              simp at *
              obtain ⟨δS, hδS⟩ := hS
              obtain ⟨δQ, hδQ⟩ := hQ
              use δS * δQ
              rw [← hδS, ← hδQ, lemma_1_1_i]
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
              intro S
              simp
              intro δ hS
              use δ⁻¹
              simp [← hS]

/- Lemma 1.2.1.2 -/
def subgroupGeneratedByT : Subgroup SL(2,F) where
  carrier := { T τ | τ : F}
  mul_mem' := by
              intro S Q hS hQ
              simp at *
              obtain ⟨τS, hτS⟩ := hS
              obtain ⟨τQ, hτQ⟩ := hQ
              use τS + τQ
              rw [← hτS, ← hτQ, lemma_1_1_ii]
  one_mem' := ⟨0, by simp⟩
  inv_mem' := by
              intro S hS
              simp at *
              obtain ⟨τ, hτ⟩ := hS
              use (-τ)
              simp [← hτ]

def subgroupGeneratedByDT : Subgroup SL(2,F) where
  carrier := { D δ * T τ | (δ : Fˣ) (τ : F) }
  mul_mem' := by
              intro A₁ A₂ hA₁ hA₂
              obtain ⟨δ₁, τ₁, h₁⟩ := hA₁
              obtain ⟨δ₂, τ₂, h₂⟩ := hA₂
              dsimp
              use (δ₁ * δ₂), (τ₁*δ₂*δ₂ + τ₂)
              rw [← h₁, ← h₂]
              ext <;> field_simp [D, T]; ring
  one_mem' := ⟨1, 0, by simp⟩
  inv_mem' := by
              intro A hA
              obtain ⟨δ, τ, h⟩ := hA
              dsimp
              use δ⁻¹, -τ * δ⁻¹ * δ⁻¹
              rw [← h]
              simp [D_mul_T_eq_DT, Matrix.SpecialLinearGroup.SL2_inv_expl]
              ext <;> simp [DT]


/- Lemma 1.2.1.3 -/
def subgroupOfD_iso_units_of_F : subgroupGeneratedByD F ≃* Fˣ where
  toFun D := ⟨
              D.val 0 0,
              D.val 1 1,
              by obtain ⟨δ, hδ⟩ := D.property; rw [← hδ]; simp [SpecialMatrices.D],
              by obtain ⟨δ, hδ⟩ := D.property; rw [← hδ]; simp [SpecialMatrices.D]
              ⟩
  invFun δ := ⟨D δ, by simp [subgroupGeneratedByD]⟩
  left_inv A := by
                obtain ⟨δ, hδ⟩ := A.property
                rw [← Subtype.coe_inj, ← hδ]
                ext <;> simp [SpecialMatrices.D, ← hδ]
  right_inv a := by ext; rfl
  map_mul' X Y := by
                obtain ⟨δ₁, hδ₁⟩ := X.property
                obtain ⟨δ₂, hδ₂⟩ := Y.property
                simp only [Subgroup.coe_mul, Fin.isValue, SpecialLinearGroup.coe_mul]
                congr
                repeat'
                  simp_rw [← hδ₁, ← hδ₂]
                  simp [SpecialMatrices.D, mul_comm]

/- Lemma 1.2.1.4 { T τ } ≃* F -/
def subgroupOfT_iso_F : (subgroupGeneratedByT F) ≃* (Multiplicative F) where
  toFun T := T.val 1 0
  invFun τ := ⟨T τ, by simp [subgroupGeneratedByT]⟩
  left_inv T := by
                obtain ⟨τ, hτ⟩ := T.property
                rw [← Subtype.coe_inj, ← hτ]
                ext <;> simp [SpecialMatrices.T, ← hτ]
  right_inv τ := by simp [SpecialMatrices.T]
  map_mul' X Y := by
                  obtain ⟨τ₁, hτ₁⟩ := X.property
                  obtain ⟨τ₂, hτ₂⟩ := Y.property
                  simp only [Subgroup.coe_mul, Fin.isValue, SpecialLinearGroup.coe_mul]
                  simp_rw [← hτ₁, ← hτ₂]
                  simp [SpecialMatrices.T]
                  rfl

open Subgroup

/- Lemma 1.2.2.1 T is a normal subgroup of H = DT -/


/- Lemma 1.2.2.2 H ⧸ T = D -/
-- def quot_iso_subgroupGeneratedByD {F : Type* } [Field F] : subgroupGeneratedByDT F ⧸ subgroupGeneratedByT F ≃* subgroupGeneratedByD F := by sorry

/- Lemma 1.3. Z(SL(2,F)) = ⟨ -I ⟩ .-/
def center_of_SL_2_F : center SL(2,F) ≃* rootsOfUnity 2 F  :=
  Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' 2


instance : Monoid SL(2,F) := Matrix.SpecialLinearGroup.monoid

instance : Module F (Matrix (Fin 2) (Fin 2) F) := by exact module

@[simp]
lemma SpecialLinearGroup.coe_coe {n : ℕ}{S : SL(n, F)} :
  ((S : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = (S : Matrix (Fin n) (Fin n) F) :=  by rfl

@[simp]
lemma GeneralLinearGroup.coe_mk' {R : Type*} [CommRing R] {M : Matrix (Fin 2) (Fin 2) R}
  (hM : Invertible (det M) ) : (GeneralLinearGroup.mk' M hM) = M := by rfl

@[simp]
lemma GeneralLinearGroup.coe_mk'_inv {R : Type*} [CommRing R] {M : Matrix (Fin 2) (Fin 2) R}
  {hM : Invertible (det M) } : (GeneralLinearGroup.mk' M hM)⁻¹ = M⁻¹ := by simp only [coe_units_inv,
    coe_mk']

lemma GL_eq_iff_Matrix_eq {n R : Type* } [Fintype n] [DecidableEq n] [CommRing R] { A B :  GL n R}
  (h : (A :  Matrix n n R) = (B : Matrix n n R) ) : A = B := by
  apply Matrix.GeneralLinearGroup.ext
  rw [← Matrix.ext_iff] at h
  exact h

lemma det_GL_coe_is_unit {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] (G : GL n R) :
  IsUnit (det (G : Matrix n n R)) := by
  have det_G_is_unit : IsUnit (GeneralLinearGroup.det G) := Group.isUnit (GeneralLinearGroup.det G)
  exact ⟨det_G_is_unit.unit, by simp only [IsUnit.unit_spec, GeneralLinearGroup.val_det_apply]⟩

open Polynomial

lemma associated_of_dvd_mul_irreducibles {k : Type*} [Field k] {q p₁ p₂: k[X]}
  (hp₁ : Irreducible p₁) (hp₂ : Irreducible p₂) (hpq : q ∣ p₁ * p₂) :
  (Associated q 1) ∨ Associated q p₁ ∨ Associated q p₂ ∨ Associated q (p₁ * p₂) := by
  rw [dvd_mul] at hpq
  obtain ⟨d₁, d₂, hd₁, hd₂, q_eq⟩ := hpq
  rw [irreducible_iff] at hp₁ hp₂
  rcases hp₁ with ⟨-, hp₁⟩
  rcases hp₂ with ⟨-, hp₂⟩
  rcases hd₁ with ⟨k₁, hk₁⟩
  rcases hd₂ with ⟨k₂, hk₂⟩
  specialize hp₁ d₁ k₁ hk₁
  specialize hp₂ d₂ k₂ hk₂
  rcases hp₁ with (h₁ | h₁)
  · rcases hp₂ with (h₂ | h₂)
    · left
      rw [associated_one_iff_isUnit, q_eq]
      exact (IsUnit.mul h₁ h₂)
    · right; right; left
      rw [q_eq, hk₂, associated_mul_isUnit_right_iff h₂, mul_comm,
          associated_mul_isUnit_left_iff h₁]
  · rcases hp₂ with (h₂ | h₂)
    · right; left
      rw [q_eq, hk₁, associated_mul_isUnit_left_iff h₂, associated_mul_isUnit_right_iff h₁]
    · right; right; right
      rw [q_eq, hk₁, hk₂, mul_assoc, ← mul_assoc k₁, mul_comm k₁, mul_assoc, ← mul_assoc,
      associated_mul_isUnit_right_iff (IsUnit.mul h₁ h₂)]

lemma minpoly_eq_X_sub_C_implies_matrix_is_diagonal { n R : Type*} [Fintype n] [DecidableEq n]
     [ CommRing R ] [NoZeroDivisors R] {M : Matrix n n R} {a : R}
    (hM : Associated (minpoly R M) (X - C a)) : M = diagonal (fun _ ↦ a) := by
    obtain ⟨u, hu⟩ := hM.symm
    let Ξ := minpoly R M
    -- The minimal polynomial evaluated at M must be 0
    have M_eq_diagonal : aeval (M : Matrix n n R) Ξ = 0 := minpoly.aeval _ _
    have Ξ_eq : ∃ u, IsUnit u ∧ Ξ = (X - C a) * u := ⟨u, Units.isUnit _, hu.symm⟩
    -- We rearrange Ξ_eq to isolate Ξ and plug
    obtain ⟨u_inv, u_is_unit, Ξ_eq⟩ := Ξ_eq
    rw [Polynomial.isUnit_iff] at u_is_unit
    obtain ⟨u', u'_is_unit, C_u'_eq_u_inv⟩  := u_is_unit
    have ringHom_u'_is_unit : IsUnit ((algebraMap R (Matrix n n R)) u') :=
      RingHom.isUnit_map _ u'_is_unit
    rw [Ξ_eq, aeval_mul, ← C_u'_eq_u_inv, aeval_C,
       IsUnit.mul_left_eq_zero ringHom_u'_is_unit] at M_eq_diagonal
    simp [map_sub, aeval_X, aeval_C, sub_eq_zero, algebraMap, Algebra.toRingHom] at M_eq_diagonal
    -- This shows M is diagonal
    exact M_eq_diagonal

lemma smul_one_of_minpoly_eq_X_sub_C { R : Type*} {n : ℕ} [ CommRing R ] [NoZeroDivisors R]
  {s : (Fin n → R) →ₗ[R] Fin n → R } {a : R} (hs : Associated (minpoly R s) (X - C a)) :
  s = a • 1 := by
  obtain ⟨unit, hunit⟩ := hs
  let Ξ := minpoly R s
  -- The minimal polynomial evaluated at M must be 0
  have s_eq_smul_one : aeval s Ξ = 0 := minpoly.aeval _ _
  have Ξ_eq : ∃ u_inv, IsUnit u_inv ∧ Ξ = (X - C a) * u_inv := ⟨unit.inv, by simp [← hunit]⟩
  -- We rearrange Ξ_eq to isolate Ξ, and plug in Ξ
  obtain ⟨u_inv, u_inv_is_unit, Ξ_eq⟩ := Ξ_eq
  rw [Polynomial.isUnit_iff] at u_inv_is_unit --------
  obtain ⟨u_inv', u_inv'_is_unit, C_u_inv'_eq_u_inv⟩  := u_inv_is_unit
  have ringHom_u_inv'_is_unit : IsUnit ((algebraMap R ((Fin n → R) →ₗ[R] Fin n → R)) u_inv') :=
    RingHom.isUnit_map _ u_inv'_is_unit
  rw [Ξ_eq, aeval_mul, ← C_u_inv'_eq_u_inv, aeval_C,
    IsUnit.mul_left_eq_zero ringHom_u_inv'_is_unit] at s_eq_smul_one
  simp [map_sub, aeval_X, aeval_C, sub_eq_zero, algebraMap, Algebra.toRingHom] at s_eq_smul_one
  -- This shows S is diagonal
  exact s_eq_smul_one

def GeneralLinearGroup.T [DecidableEq F] (a b d : F) : GL (Fin 2) F :=
  if h : a * d ≠ 0
  then GeneralLinearGroup.mk' !![a, b; 0, d] (by simp; exact invertibleOfNonzero h)
  else 1

lemma exists_sqrt_discriminant [IsAlgClosed F] { a b c : F} :
  ∃ s, s * s = discrim a b c := by
  rw [discrim]
  let P := C 1 * X^2 + C 0 * X + C (- (b^2 - 4 * a * c))
  have deg_P_eq_two : degree P = 2 := by
    dsimp [P]
    rw [Polynomial.degree_quadratic]
    exact one_ne_zero
  have exists_root_of_P := by apply IsAlgClosed.exists_root P (by simp [deg_P_eq_two])
  obtain ⟨s, hs⟩ := exists_root_of_P
  use s
  simp [P] at hs
  rw [add_eq_zero_iff_eq_neg, sq] at hs
  rw [hs]
  ring_nf

lemma upper_triangular_iff_bottom_left_entry_eq_zero {M : Matrix (Fin 2) (Fin 2) F} :
  (∃ a b d, !![a, b; 0, d] = M) ↔ M 1 0 = 0 := by
  constructor
  · rintro  ⟨a, b, d, hM⟩
    simp [← hM]
  · intro h
    use M 0 0, M 0 1, M 1 1
    simp_rw [← h]
    apply Matrix.fin_two_eq <;> rfl

/- A 2×2 matrix, G is conjugate to an upper triangular if there exists an invertible matrix
 such that when conjugated the bottom left entry is annhilated
  -/
lemma isConj_upper_triangular_iff [DecidableEq F] [IsAlgClosed F]
  {M : Matrix (Fin 2) (Fin 2) F} :
  (∃ a b d , ∃ (C : SL(2,F)), (C  * M * C⁻¹ : Matrix (Fin 2) (Fin 2) F) = !![a, b; 0, d]) ↔
    ∃ c : SL(2,F), ((c * M * (c⁻¹)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  constructor
  · rintro ⟨a, b, d, h⟩
    obtain ⟨c, hc⟩ := h
    use c
    rw [hc]
    rfl
  · rintro ⟨c, hc⟩
    rw [← upper_triangular_iff_bottom_left_entry_eq_zero] at hc
    obtain ⟨a, b, d, h⟩ := hc
    use a, b, d
    use c
    rw [h]

@[simp]
lemma Matrix.special_inv_eq {x : F} :
  !![1, 0; x, 1]⁻¹ = !![1, 0; - x, 1] := by simp [inv_def]

lemma Matrix.conj_T_eq {x : F} {a b c d : F} :
  !![1, 0; x, 1] * !![a, b; c, d] * !![1, 0; -x, 1] =
  !![-b * x + a, b; (-b) * x * x + (a -d) * x + c, b*x + d] := by
  simp
  apply Matrix.fin_two_eq <;> ring_nf

def SpecialLinearGroup.mk' {n : ℕ }(M : Matrix (Fin n) (Fin n) F) (h : det M = 1) : SL(n, F) :=
  ⟨M, h⟩

-- Note: I do not IsConj as the the matrix which acts by conjugation has determinant 1
theorem isTriangularizable_of_algClosed [DecidableEq F] [IsAlgClosed F]
  [NeZero (2 : F)] (M : Matrix (Fin 2) (Fin 2) F) :
  ∃ a b d, ∃ (C : SL(2,F)), (C * M * C⁻¹ : Matrix (Fin 2) (Fin 2) F) = !![a, b; 0, d] := by
  let α := M 0 0
  let β := M 0 1
  let γ := M 1 0
  let δ := M 1 1
  have M_coe_eq : M = !![α, β; γ, δ] := by
      apply Matrix.fin_two_eq <;> rfl
  let a := -β
  let b := α - δ
  let c := γ
  rw [isConj_upper_triangular_iff]
  -- if β ≠ 0 then we solve the quadratic to force the bottom left entry to be 0
  by_cases hβ : β ≠ 0
  · obtain ⟨s, hs⟩ := exists_sqrt_discriminant (a := a) (b := b) (c := c)
    let x := (-b + s) / (2 * a)
    use T x
    simp
    simp_rw [M_coe_eq, T, Matrix.conj_T_eq]
    simp
    have ha : a ≠ 0 := by simp [hβ, a]
    rw [← neg_mul, ← neg_mul, mul_assoc, quadratic_eq_zero_iff ha hs.symm]
    left; rfl
  simp at hβ
  -- If β = 0 then we solve the linear polynomial if α - δ ≠ 0
  by_cases had : α - δ ≠ 0
  · let x := -γ / (α - δ)
    use T x
    simp
    simp_rw [M_coe_eq, T, conj_T_eq]
    field_simp [hβ, x]
    ring_nf
  -- If β = 0 and α = δ
  · use W
    simp [M_coe_eq, W, inv_def, hβ]


lemma upper_triangular_isConj_diagonal_of_nonzero_det  [DecidableEq F]
  {a b d : F} (had : a - d ≠ 0) : ∃ C : SL(2,F), C * !![a, b; 0, d] * C⁻¹ = !![a, 0; 0, d] := by
  use ⟨!![1, b / (a - d); 0, 1], by simp⟩
  simp
  apply Matrix.fin_two_eq
  repeat' field_simp
  ring_nf

lemma upper_triangular_isConj_jordan {a b : F} (hb : b ≠ 0) :
  IsConj !![a, b; 0, a] !![a, 1; 0, a] := by
  use GeneralLinearGroup.mk' !![1 / b, 0; 0, 1]
    (by simp; apply invertibleOfNonzero <| inv_ne_zero hb)
  apply Matrix.fin_two_eq
  repeat' field_simp

lemma bottom_triangular_isConj_upper_triangular {a b : F} :
  ∃ C : SL(2,F), C * !![a, 0; -b, a] * C⁻¹ = !![a, b; 0, a] := by
  have h' : det !![0, -1; (1 : F), 0] = 1 := by simp
  use ⟨!![0,-1;(1 : F),0], h'⟩
  simp

lemma mul_left_eq_mul_right_iff {α : Type* }[Monoid α]{N M : α }(c : αˣ) :
  ((c : α) * M = N * (c : α)) ↔ M = c⁻¹ * N * c := by
  constructor
  intro h
  rw [mul_assoc, ← h, ← mul_assoc, Units.inv_mul, one_mul]
  intro h
  rw [h, ← mul_assoc, ← mul_assoc, Units.mul_inv, one_mul]

-- Note: [isConj_iff] can be strengthened for monoids
lemma det_eq_det_IsConj {n : ℕ}{M N : Matrix (Fin n) (Fin n) R} (h : IsConj N M) :
  det N = det M := by
  rw [isConj_comm, IsConj] at h
  obtain ⟨c, hc⟩ := h
  rw [SemiconjBy, mul_left_eq_mul_right_iff] at hc
  rw [hc, Matrix.coe_units_inv, det_conj' c.isUnit N]

-- if underlying matrices are the same then the matrices
-- a subtypes of the special linear group are the same
lemma SpecialLinearGroup.eq_of {S L : SL(2,F) } (h : (S : Matrix ( Fin 2) (Fin 2) F)  = L) :
  S = L := by ext <;> simp [h]

lemma IsConj_coe {M N : Matrix (Fin 2) (Fin 2) F} (hM : det M = 1) (hN : det N = 1)
  (h : ∃ C : SL(2, F), C * M * C⁻¹ = N) : ∃ C : SL(2,F), C * ⟨M, hM⟩ * C⁻¹ = ⟨N, hN⟩ := by
  obtain ⟨C, hC⟩ := h
  use C
  apply SpecialLinearGroup.eq_of
  simp only [SpecialLinearGroup.coe_mul]
  rw [hC]


/-
Lemma 1.5.
Each element of SL(2,F) is conjugate to either
D δ for some δ ∈ Fˣ, or to  ± T τ for some τ ∈ F.
-/
theorem lemma_1_5 [DecidableEq F] [IsAlgClosed F] [NeZero (2 : F)] {S : SL(2, F)} :
  (∃ δ : Fˣ, IsConj (D δ) S) ∨ (∃ τ : F, IsConj (T τ) S) ∨ (∃ τ : F, IsConj (- T τ) S) := by
  have S_IsConj_upper_triangular :
    ∃ a b d, ∃ C : SL(2,F), (C *S * C⁻¹ : Matrix (Fin 2) (Fin 2) F) = !![a, b; 0, d] :=
    @isTriangularizable_of_algClosed F _ _ _ _ (S : Matrix (Fin 2) (Fin 2) F)
  have det_coe_S_eq_one : det (S : Matrix (Fin 2) (Fin 2) F ) = 1 := by simp
  obtain ⟨a, b, d, C, h⟩ := S_IsConj_upper_triangular
  have det_eq_one : det !![a, b; 0, d] = 1 := by
    rw [← det_coe_S_eq_one, ← h]
    simp only [det_mul, SpecialLinearGroup.det_coe, mul_one, one_mul]
  have had := det_eq_one
  simp at had
  have d_eq_inv_a : d = a⁻¹ := Eq.symm (DivisionMonoid.inv_eq_of_mul a d had)
  have a_is_unit : IsUnit a := by exact isUnit_of_mul_eq_one a d had
  have a_ne_zero : a ≠ 0 := by exact left_ne_zero_of_mul_eq_one had
  have det_eq_one' : det !![a, 0; 0, d] = 1 := by simp [d_eq_inv_a]; rw [mul_inv_cancel₀ a_ne_zero]
  by_cases had' : a - d ≠ 0
  · left
    use a_is_unit.unit
    have isConj₁ : ∃ C : SL(2,F), C * S * C⁻¹ =  ⟨!![a, b ; 0, d], det_eq_one⟩ := by
      use C
      apply SpecialLinearGroup.eq_of
      simp only [SpecialLinearGroup.coe_mul]
      rw [h]
    have isConj₂ :
      ∃ C : SL(2,F), C * ⟨!![a,b; 0,d], det_eq_one⟩ * C⁻¹ = ⟨!![a,0;0,d], det_eq_one'⟩ := by
      apply IsConj_coe
      apply upper_triangular_isConj_diagonal_of_nonzero_det _ had'
    simp_rw [← isConj_iff, d_eq_inv_a] at isConj₁ isConj₂
    simp only [D, IsUnit.unit_spec]
    apply IsConj.trans isConj₂.symm isConj₁.symm
  · right
    simp [sub_eq_zero] at had'
    simp [← had', ← sq] at det_eq_one'
    rcases det_eq_one' with (a_eq_one | a_eq_neg_one)
    · left
      rw [← had', a_eq_one] at h
      have det_eq_one'' : det !![1, b; 0, 1] = 1 := by norm_num
      use -b
      have isConj₁ : ∃ C : SL(2,F), C * (T (-b)) * C⁻¹ = ⟨!![1, b; 0, 1], det_eq_one''⟩ := by
        apply IsConj_coe
        exact bottom_triangular_isConj_upper_triangular _
      have isConj₂ : ∃ C : SL(2,F), C * S * C⁻¹ = ⟨!![1, b; 0, 1], det_eq_one''⟩ := by
        use C
        apply SpecialLinearGroup.eq_of
        simp only [SpecialLinearGroup.coe_mul, h]
      rw [← isConj_iff] at isConj₁ isConj₂
      apply IsConj.trans isConj₁ isConj₂.symm
    · right
      rw [← had', a_eq_neg_one] at h
      have det_eq_one'' : det !![-1, b; 0, -1] = 1 := by norm_num
      have T_eq : - T b = !![-1, 0; -b, -1] := by simp [T]
      use b
      have isConj₁ : ∃ C : SL(2,F), C * (-T (b)) * C⁻¹ = ⟨!![-1, b; 0, -1], det_eq_one''⟩ := by
        apply IsConj_coe
        simp only [T_eq]
        exact bottom_triangular_isConj_upper_triangular _
      have isConj₂ : ∃ C : SL(2,F), C * S * C⁻¹ = ⟨!![-1, b; 0, -1], det_eq_one''⟩ := by
        use C
        apply SpecialLinearGroup.eq_of
        simp only [SpecialLinearGroup.coe_mul, h]
      rw [← isConj_iff] at isConj₁ isConj₂
      apply IsConj.trans isConj₁ isConj₂.symm


/- Proposition 1.6.i N_L(T₁) ⊆ H, where T₁ is any subgroup of T with order greater than 1. -/

/- Proposition 1.6.ii C_L(± T τ) = T × Z where τ ≠ 0 -/

/- Proposition 1.7. (i) N_L (D₁) = ⟨D, W⟩, where D₁ is any subgroup of D with order greater than 2.-/

/- Proposition 1.8. Let a and b be conjugate elements in a group G. Then ∃ x ∈ G such that xCG (a)x−1 = CG (b).-/
-- lemma proposition_1_8 { G : Type* } [Group G] (a b : G) (hab : IsConj a b) : ∃ x : G, ConjAct(centralizer { a }) = centralizer { b } := by sorry  :=

/-
Corollary 1.9.
The centraliser of an element x in L is abelian unless x belongs to the centre of L.
-/
lemma corollary_1_9 (S : SL(2,F)) (hx : x ∉ center SL(2,F)): IsCommutative (centralizer { S }) := by sorry
