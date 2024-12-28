import Mathlib
-- import ClassificationOfSubgroups.SpecialCases


set_option linter.style.longLine true

universe u

open Matrix MatrixGroups

variable
  (F : Type u) [Field F]
  (n : Type u) [Fintype n]
  (R : Type u) [CommRing R]

instance : Group SL(2,F) := by infer_instance

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

def t {F : Type*} [Field F] (τ : F): SL(2,F) :=
  ⟨!![1, 0; τ, 1], by simp⟩

@[simp]
lemma t_zero_eq_one : t (0 : F) = 1 := by ext <;> rfl

def d {F : Type*} [Field F] (δ : Fˣ) : SL(2, F) :=
  ⟨!![(δ : F), (0 : F); (0 :F) , (δ⁻¹ : F)], by norm_num⟩

lemma d_eq_diagonal (δ : Fˣ) :
  (d δ : Matrix (Fin 2) (Fin 2) F) = diagonal (fun i ↦ if i.val = 0 then (δ : F) else δ⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [d]

@[simp]
lemma d_one_eq_one : d (1 : Fˣ) = 1 := by ext <;> simp [d]

@[simp]
lemma d_neg_one_eq_neg_one : d (-1 : Fˣ) = -1 := by ext <;> simp [d, inv_neg_one]

lemma d_coe_eq : (d (δ : Fˣ) : Matrix (Fin 2) (Fin 2) F) = !![(δ : F), 0; 0, δ⁻¹] := by
  apply Matrix.fin_two_eq
  repeat' simp [d]

lemma d_0_0_is_unit (δ : Fˣ) : IsUnit ((d δ) 0 0) := by simp [d]

lemma t_eq_d_iff {δ : Fˣ} {τ : F} : d δ = t τ ↔ δ = 1 ∧ τ = 0 := by
  constructor
  · intro h
    have δ_eq_one : d δ 0 0 = 1 := by simp [h, t]
    simp [d] at δ_eq_one
    have τ_eq_zero : t τ 1 0 = 0 := by simp [← h, d]
    simp [t] at τ_eq_zero
    exact ⟨δ_eq_one, τ_eq_zero⟩
  · rintro ⟨rfl, rfl⟩
    simp

def w {F : Type*} [Field F] : SL(2, F) :=
  ⟨!![0,1;-1,0], by norm_num⟩

def dt {F : Type*} [Field F] (δ : Fˣ) (τ : F) : SL(2, F) :=
  ⟨!![δ, 0; τ * δ⁻¹, δ⁻¹], by norm_num⟩

def dw {F : Type*} [Field F] (δ : Fˣ) : SL(2,F) :=
  ⟨!![0, δ; -δ⁻¹, 0], by norm_num⟩

lemma d_mul_t_eq_dt (δ : Fˣ) (τ : F) : d δ * t τ = dt δ τ := by ext <;> simp [d, t, dt, mul_comm]

lemma d_mul_w_eq_dw (δ : Fˣ) : d δ * w = dw δ := by ext <;> simp [d, w, dw]

@[simp]
lemma inv_d_eq (δ : Fˣ) : (d δ)⁻¹ = d (δ⁻¹) := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl, d]; rfl

@[simp]
lemma inv_t_eq (τ : F) : (t τ)⁻¹ = t (-τ) := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl, t]; rfl


end SpecialMatrices


/-
Lemma 1.1. For any δ, ρ ∈ Fˣ and τ, µ ∈ F we have:
(i) D δ * D ρ = D (δ * ρ),
(ii) T τ *  T μ = T (τ + µ),
(iii) D δ * T τ * (D δ)⁻¹ = T (τ * δ⁻²),
(iv) W * D δ * W⁻¹ = (D δ)⁻¹.
-/
open SpecialMatrices
-- (i)
lemma lemma_1_1_i (δ ρ : Fˣ) : d δ * d ρ = d (δ * ρ) := by ext <;> simp [d, mul_comm]

-- (ii)
lemma lemma_1_1_ii (τ μ : F) : t τ * t μ = t (τ + μ) := by ext <;> simp [t]

-- (iii)
lemma lemma_1_1_iii (δ : Fˣ) (τ : F) : d δ * t τ * (d δ)⁻¹ = t (τ * δ⁻¹ * δ⁻¹) := by
  simp; ext <;> simp [t, d, mul_comm]

-- (iv)
lemma lemma_1_1_iv (δ : Fˣ) : w * (d δ) * w⁻¹ = (d δ)⁻¹ := by simp; ext <;> simp [d, w]

namespace SpecialSubgroups

/- Lemma 1.2.1.1-/
def D (F : Type*) [Field F] : Subgroup SL(2,F) where
  carrier := { d δ | δ : Fˣ }
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
def T (F : Type*) [Field F]: Subgroup SL(2,F) where
  carrier := { t τ | τ : F }
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

lemma D_meet_T_eq_bot : D F ⊓ T F = ⊥ := by
  ext x
  constructor
  · rintro ⟨x_mem_D, x_mem_T⟩
    obtain ⟨δ, hδ⟩ := x_mem_D
    obtain ⟨τ, hτ⟩ := x_mem_T
    rw [← hτ] at hδ
    rw [t_eq_d_iff] at hδ
    obtain ⟨-, rfl⟩ := hδ
    simp [← hτ]
  · intro h
    simp at h
    constructor
    · simp [h]; exact Subgroup.one_mem (D F)
    · simp [h]; exact Subgroup.one_mem (T F)

def H (F : Type*) [Field F] : Subgroup SL(2,F) where
  carrier := { d δ * t τ | (δ : Fˣ) (τ : F) }
  mul_mem' := by
              intro A₁ A₂ hA₁ hA₂
              obtain ⟨δ₁, τ₁, h₁⟩ := hA₁
              obtain ⟨δ₂, τ₂, h₂⟩ := hA₂
              dsimp
              use (δ₁ * δ₂), (τ₁*δ₂*δ₂ + τ₂)
              rw [← h₁, ← h₂]
              ext <;> field_simp [d, t]; ring
  one_mem' := ⟨1, 0, by simp⟩
  inv_mem' := by
              intro A hA
              obtain ⟨δ, τ, h⟩ := hA
              dsimp
              use δ⁻¹, -τ * δ⁻¹ * δ⁻¹
              rw [← h]
              simp [d_mul_t_eq_dt, Matrix.SpecialLinearGroup.SL2_inv_expl]
              ext <;> simp [dt]

def lower_triangular [DecidableEq F] (a c d : F) : SL(2, F) :=
  if h : a * d = 1 then ⟨!![a, 0; c, d], by simp [h]⟩ else 1

-- it is in fact a surjection
lemma mem_H_iff_lower_triangular [DecidableEq F] {x : SL(2,F)} :
  x ∈ H F ↔ ∃ a c d, a * d = 1 ∧ (x : Matrix (Fin 2) (Fin 2) F) = !![a, 0; c, d] := by
  constructor
  · intro hx
    obtain ⟨δ, τ, h⟩ := hx
    use δ, τ * δ⁻¹, δ⁻¹
    rw [← h]
    split_ands
    simp
    ext; simp [d, t, lower_triangular, mul_comm]
  · rintro ⟨a, c, d, had, hx⟩
    have a_is_unit : IsUnit a := by exact isUnit_of_mul_eq_one a d had
    have a_inv_eq_d : a⁻¹ = d := by exact DivisionMonoid.inv_eq_of_mul a d had
    use a_is_unit.unit, c * a_is_unit.unit
    simp [SpecialMatrices.d, t, lower_triangular, had]
    ext <;> field_simp [a_inv_eq_d, had, hx]; exact Eq.symm (eq_one_div_of_mul_eq_one_right had)

lemma mem_H_iff_lower_triangular' [DecidableEq F] {x : SL(2,F)} :
  x ∈ H F ↔ ∃ a c d, (x : Matrix (Fin 2) (Fin 2) F) = !![a, 0; c, d] := by
  constructor
  · intro hx
    obtain ⟨δ, τ, h⟩ := hx
    use δ, τ * δ⁻¹, δ⁻¹
    rw [← h]
    ext; simp [d, t, lower_triangular, mul_comm]
  · rintro ⟨a, c, d, hx⟩
    have had : det (x : Matrix (Fin 2) (Fin 2) F) = 1 := by simp
    simp [hx] at had
    have a_is_unit : IsUnit a := by exact isUnit_of_mul_eq_one a d had
    have a_inv_eq_d : a⁻¹ = d := by exact DivisionMonoid.inv_eq_of_mul a d had
    use a_is_unit.unit, c * a_is_unit.unit
    simp [SpecialMatrices.d, t, lower_triangular, had]
    ext <;> field_simp [a_inv_eq_d, had, hx]; exact Eq.symm (eq_one_div_of_mul_eq_one_right had)


end SpecialSubgroups


/- Lemma 1.2.1.3 -/
def D_iso_units_of_F (F : Type*) [Field F] : SpecialSubgroups.D F ≃* Fˣ where
  toFun d := ⟨
              d.val 0 0,
              d.val 1 1,
              by obtain ⟨δ, hδ⟩ := d.property; rw [← hδ]; simp [SpecialMatrices.d],
              by obtain ⟨δ, hδ⟩ := d.property; rw [← hδ]; simp [SpecialMatrices.d]
              ⟩
  invFun δ := ⟨d δ, by use δ⟩
  left_inv A := by
                obtain ⟨δ, hδ⟩ := A.property
                rw [← Subtype.coe_inj, ← hδ]
                ext <;> simp [SpecialMatrices.d, ← hδ]
  right_inv a := by ext; rfl
  map_mul' X Y := by
                obtain ⟨δ₁, hδ₁⟩ := X.property
                obtain ⟨δ₂, hδ₂⟩ := Y.property
                simp only [Subgroup.coe_mul, Fin.isValue, SpecialLinearGroup.coe_mul]
                congr
                repeat'
                  simp_rw [← hδ₁, ← hδ₂]
                  simp [SpecialMatrices.d, mul_comm]

/- Lemma 1.2.1.4 { T τ } ≃* F -/
def T_iso_F (F : Type*) [Field F]: SpecialSubgroups.T F ≃* (Multiplicative F) where
  toFun T := T.val 1 0
  invFun τ := ⟨t τ, by use τ⟩
  left_inv T := by
                obtain ⟨τ, hτ⟩ := T.property
                rw [← Subtype.coe_inj, ← hτ]
                ext <;> simp [t, ← hτ]
  right_inv τ := by simp [t]
  map_mul' X Y := by
                  obtain ⟨τ₁, hτ₁⟩ := X.property
                  obtain ⟨τ₂, hτ₂⟩ := Y.property
                  simp only [Subgroup.coe_mul, Fin.isValue, SpecialLinearGroup.coe_mul]
                  simp_rw [← hτ₁, ← hτ₂]
                  simp [t]
                  rfl

open Subgroup

/- Lemma 1.2.2.1 T is a normal subgroup of H = D T -/


/- Lemma 1.2.2.2 H ⧸ T = D -/
-- def quot_iso_subgroupGeneratedByD {F : Type* } [Field F] :
--   subgroupGeneratedByDT F ⧸ subgroupGeneratedByT F ≃* subgroupGeneratedByD F := by sorry

/- Lemma 1.3. Z(SL(2,F)) = ⟨ -I ⟩ .-/
def center_of_SL_2_F : center SL(2,F) ≃* rootsOfUnity 2 F  :=
  Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' 2

-- Lemma 1.4 If p ≠ 2, then SL(2,F) contains a unique element of order 2.

#check Subgroup.normalClosure

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

lemma lower_triangular_iff_top_right_entry_eq_zero {M : Matrix (Fin 2) (Fin 2) F} :
  (∃ a c d, !![a, 0; c, d] = M) ↔ M 0 1 = 0 := by
  constructor
  · rintro  ⟨a, b, d, hM⟩
    simp [← hM]
  · intro h
    use M 0 0, M 1 0, M 1 1
    simp_rw [← h]
    apply Matrix.fin_two_eq <;> rfl

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

lemma exists_root_of_special_poly [IsAlgClosed F] (a b c d : F) (hb : b ≠ 0):
  ∃ x : F, -b * x * x + (a - d) * x + c = 0 := by
  let P := C (-b) * X^2 + C (a - d) * X + C c
  have deg_P_eq_two : degree P = 2 := by
    dsimp [P]
    rw [Polynomial.degree_quadratic]
    simp [hb]
  have exists_root_of_P := by apply IsAlgClosed.exists_root P (by simp [deg_P_eq_two])
  obtain ⟨x, hx⟩ := exists_root_of_P
  use x
  simp [P] at hx
  ring_nf at hx ⊢
  exact hx

lemma Matrix.conj_t_eq {x : F} {a b c d : F} :
  t x * !![a, b; c, d] * t (-x) =
  !![-b * x + a, b; (-b) * x * x + (a -d) * x + c, b*x + d] := by
  simp [SpecialMatrices.t]
  apply Matrix.fin_two_eq <;> ring_nf

def SpecialLinearGroup.mk' {n : ℕ }(M : Matrix (Fin n) (Fin n) F) (h : det M = 1) : SL(n, F) :=
  ⟨M, h⟩

-- Note: I do not use IsConj as the the matrix which acts by conjugation has determinant 1
theorem isTriangularizable_of_algClosed [DecidableEq F] [IsAlgClosed F]
  (M : Matrix (Fin 2) (Fin 2) F) :
  ∃ a b d, ∃ (C : SL(2,F)), (C * M * C⁻¹ : Matrix (Fin 2) (Fin 2) F) = !![a, b; 0, d] := by
  let α := M 0 0
  let β := M 0 1
  let γ := M 1 0
  let δ := M 1 1
  have M_coe_eq : M = !![α, β; γ, δ] := by
      apply Matrix.fin_two_eq <;> rfl
  -- Is conjugate to an upper triangular matrix iff there exists a matrix such that
  -- when conjugated kills the bottom left entry
  rw [isConj_upper_triangular_iff]
  -- If β ≠ 0 then we solve the quadratic to force the bottom left entry to be 0
  by_cases hβ : β ≠ 0
  · obtain ⟨x, hx⟩ := by apply exists_root_of_special_poly F α β γ δ hβ
    use t x
    simp [M_coe_eq, t, Matrix.conj_t_eq]
    ring_nf at hx ⊢
    exact hx
  simp at hβ
  -- If β = 0 then we solve the linear polynomial if α - δ ≠ 0
  by_cases had : α - δ ≠ 0
  · let x := -γ / (α - δ)
    use t x
    simp [M_coe_eq, Matrix.conj_t_eq]
    field_simp [hβ, x]
    ring_nf
  -- If β = 0 and α = δ
  · use w
    simp [M_coe_eq, w, inv_def, hβ]


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

lemma lower_triangular_isConj_upper_triangular {a b : F} :
  ∃ C : SL(2,F), C * !![a, 0; -b, a] * C⁻¹ = !![a, b; 0, a] := by
  have h' : det !![0, -1; (1 : F), 0] = 1 := by simp
  use ⟨!![0,-1;(1 : F),0], h'⟩
  simp

lemma mul_left_eq_mul_right_iff {α : Type*}[Monoid α]{N M : α }(c : αˣ) :
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

-- If underlying matrices are the same then the matrices
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
theorem lemma_1_5 [DecidableEq F] [IsAlgClosed F] {S : SL(2, F)} :
  (∃ δ : Fˣ, IsConj (d δ) S) ∨ (∃ τ : F, IsConj (t τ) S) ∨ (∃ τ : F, IsConj (- t τ) S) := by
  -- S is conjugate to an upper triangular matrix
  have S_IsConj_upper_triangular :
    ∃ a b d, ∃ C : SL(2,F), (C * S * C⁻¹ : Matrix (Fin 2) (Fin 2) F) = !![a, b; 0, d] :=
    @isTriangularizable_of_algClosed F _ _ _ (S : Matrix (Fin 2) (Fin 2) F)
  have det_coe_S_eq_one : det (S : Matrix (Fin 2) (Fin 2) F ) = 1 := by simp
  obtain ⟨a, b, d, C, h⟩ := S_IsConj_upper_triangular
  -- Because !![a, b; 0, d] is conjugate to S it also has determinant 1
  have det_eq_one : det !![a, b; 0, d] = 1 := by
    rw [← det_coe_S_eq_one, ← h]
    simp only [det_mul, SpecialLinearGroup.det_coe, mul_one, one_mul]
  have had := det_eq_one
  -- The determinant being equal to 1 implies a * d = 1
  simp at had
  -- so the inverse of a is equal to d
  have d_eq_inv_a : d = a⁻¹ := Eq.symm (DivisionMonoid.inv_eq_of_mul a d had)
  -- Therefore a is a unit
  have a_is_unit : IsUnit a := by exact isUnit_of_mul_eq_one a d had
  -- Furthermore, a is nonzero
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
    simp only [SpecialMatrices.d, IsUnit.unit_spec]
    -- conjugation is transitive
    apply IsConj.trans isConj₂.symm isConj₁.symm
  · right
    simp [sub_eq_zero] at had'
    simp [← had', ← sq] at det_eq_one'
    rcases det_eq_one' with (a_eq_one | a_eq_neg_one)
    · left
      rw [← had', a_eq_one] at h
      have det_eq_one'' : det !![1, b; 0, 1] = 1 := by norm_num
      use -b
      have isConj₁ : ∃ C : SL(2,F), C * (t (-b)) * C⁻¹ = ⟨!![1, b; 0, 1], det_eq_one''⟩ := by
        apply IsConj_coe
        exact lower_triangular_isConj_upper_triangular _
      have isConj₂ : ∃ C : SL(2,F), C * S * C⁻¹ = ⟨!![1, b; 0, 1], det_eq_one''⟩ := by
        use C
        apply SpecialLinearGroup.eq_of
        simp only [SpecialLinearGroup.coe_mul, h]
      rw [← isConj_iff] at isConj₁ isConj₂
      apply IsConj.trans isConj₁ isConj₂.symm
    · right
      rw [← had', a_eq_neg_one] at h
      have det_eq_one'' : det !![-1, b; 0, -1] = 1 := by norm_num
      have T_eq : - t b = !![-1, 0; -b, -1] := by simp [t]
      use b
      have isConj₁ : ∃ C : SL(2,F), C * (-t b) * C⁻¹ = ⟨!![-1, b; 0, -1], det_eq_one''⟩ := by
        apply IsConj_coe
        simp only [T_eq]
        exact lower_triangular_isConj_upper_triangular _
      have isConj₂ : ∃ C : SL(2,F), C * S * C⁻¹ = ⟨!![-1, b; 0, -1], det_eq_one''⟩ := by
        use C
        apply SpecialLinearGroup.eq_of
        simp only [SpecialLinearGroup.coe_mul, h]
      rw [← isConj_iff] at isConj₁ isConj₂
      -- conjugation is transitive
      apply IsConj.trans isConj₁ isConj₂.symm

open SpecialSubgroups


-- lemma mem_T_iff {x : SL(2,F)} : x ∈ T F ↔ ∃ τ, t τ = x := by
--   constructor
--   · intro hx
--     obtain ⟨τ, hτ⟩ := hx

/- Proposition 1.6.i N_L(T₁) ⊆ H, where T₁ is any subgroup of T with order greater than 1. -/
lemma proposition_1_6 [DecidableEq F] { T₁ : Subgroup (SL(2,F)) } (hT₁ : 1 < Nat.card T₁ ) (h : T₁ ≤ T F) : normalizer T₁ ≤ H F := by
  intro x hx
  rw [mem_normalizer_iff] at hx
  by_cases h' : ∃ τ, τ ≠ 0 ∧ t τ ∈ T₁
  · obtain ⟨τ, τ_ne_zero, hτ⟩  := h'
    specialize hx (t τ)
    rw [hx] at hτ
    let α := x.1 0 0
    let β := x.1 0 1
    let γ := x.1 1 0
    let δ := x.1 1 1
    have x_eq : x = !![α, β; γ, δ] := by apply Matrix.fin_two_eq <;> rfl
    have : x * t τ * x⁻¹ ∈ T F := by exact h hτ
    obtain ⟨τ' , hτ'⟩ := this
    simp [x_eq] at hτ'
    -- uses decidable equality
    rw [mem_H_iff_lower_triangular']
    sorry
  · push_neg at h'
    have : T₁ = ⊥ := by
      rw [eq_bot_iff_forall]
      intro x hx
      obtain ⟨τ, rfl⟩ := h hx
      specialize h' τ
      rw [not_imp_not] at h'
      specialize h' hx
      simp [h']
    have : Nat.card T₁ = 1 := by simp [this]
    -- contradiction with assumption that Nat.card T₁ > 1
    linarith



#check Subgroup.closure_singleton_one
#check centralizer
#check normalizer


/- Proposition 1.6.ii C_L(± T τ) = T × Z where τ ≠ 0 -/
-- lemma proposition_1_6 :
/-
Proposition 1.7.
(i) N_L (D₁) = ⟨D, W⟩, where D₁ is any subgroup of D with order greater than 2.
-/

/-
Proposition 1.8.
Let a and b be conjugate elements in a group G. Then ∃ x ∈ G such that x C_G(a) x⁻¹ = C_G (b).
-/
-- lemma proposition_1_8 { G : Type* } [Group G] (a b : G) (hab : IsConj a b) :
--    ∃ x : G, ConjAct ( centralizer { a }) = centralizer { b } := by sorry  :=

/-
Corollary 1.9.
The centraliser of an element x in L is abelian unless x belongs to the centre of L.
-/
lemma corollary_1_9 (S : SL(2,F)) (hx : x ∉ center SL(2,F)): IsCommutative (centralizer { S }) := by sorry
