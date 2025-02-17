import ClassificationOfSubgroups.Ch3_PropertiesOfSLOverAlgClosedField.S2_SpecialSubgroups
import Mathlib.Algebra.GroupWithZero.Conj
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.RingTheory.Artinian.Instances
import Mathlib.RingTheory.FiniteLength

set_option autoImplicit false
set_option linter.style.longLine true

open Matrix MatrixGroups Subgroup Pointwise

open SpecialMatrices SpecialSubgroups

universe u

variable
  (F : Type u) [Field F]
  (n : Type u) [Fintype n]
  (R : Type u) [CommRing R]
  {G : Type u} [Group G]

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
    (hM : minpoly R M = (X - C a)) : M = diagonal (fun _ ↦ a) := by
    -- The minimal polynomial evaluated at M must be 0
    have M_eq_diagonal : aeval (M : Matrix n n R) (minpoly R M) = 0 := minpoly.aeval _ _
    simp [hM, algebraMap, sub_eq_zero] at M_eq_diagonal
    -- This shows M is diagonal
    exact M_eq_diagonal

lemma lower_triangular_iff_top_right_entry_eq_zero {M : Matrix (Fin 2) (Fin 2) F} :
  (∃ a c d, !![a, 0; c, d] = M) ↔ M 0 1 = 0 := by
  constructor
  · rintro  ⟨a, b, d, hM⟩
    simp [← hM]
  · intro h
    use M 0 0, M 1 0, M 1 1
    simp_rw [← h]
    ext <;> rfl

lemma upper_triangular_iff_bottom_left_entry_eq_zero {M : Matrix (Fin 2) (Fin 2) F} :
  (∃ a b d, !![a, b; 0, d] = M) ↔ M 1 0 = 0 := by
  constructor
  · rintro  ⟨a, b, d, hM⟩
    simp [← hM]
  · intro h
    use M 0 0, M 0 1, M 1 1
    simp_rw [← h]
    ext <;> rfl

lemma det_eq_mul_diag_of_upper_triangular (S : SL(2,F)) (hγ : S.1 1 0  = 0) :
  S 0 0 * S 1 1 = 1 := by
  have det_eq_one : det (S.val) = 1 := by simp
  simp only [det_fin_two, hγ, mul_zero, sub_zero] at det_eq_one
  exact det_eq_one

lemma det_eq_mul_diag_of_lower_triangular (S : SL(2,F)) (hβ : S.1 0 1 = 0) :
  S 0 0 * S 1 1 = 1 := by
  have det_eq_one : det (S.val) = 1 := by simp
  simp only [det_fin_two, hβ, zero_mul, sub_zero] at det_eq_one
  exact det_eq_one


lemma SpecialLinearGroup.fin_two_diagonal_iff (S : SL(2,F)) :
  S 0 1 = 0 ∧ S 1 0 = 0 ↔ ∃ δ : Fˣ, d δ = S := by
  constructor
  · rintro ⟨hβ, hγ⟩
    rcases get_entries F S with ⟨α, β, γ, δ, hα, -, -, hδ, -⟩
    have det_eq_mul_diagonal := det_eq_mul_diag_of_lower_triangular F S hβ
    have α_is_unit : IsUnit α := isUnit_of_mul_eq_one α δ (hα ▸ hδ ▸ det_eq_mul_diagonal)
    have δ_is_unit : IsUnit δ := isUnit_of_mul_eq_one_right α δ (hα ▸ hδ ▸ det_eq_mul_diagonal)
    have δ_ne_zero : S.1 1 1 ≠ 0 := by exact IsUnit.ne_zero <| hδ.symm ▸ δ_is_unit
    use α_is_unit.unit
    rw [mul_eq_one_iff_eq_inv₀ δ_ne_zero] at det_eq_mul_diagonal
    ext <;> simp [d, hα, hβ, hγ, det_eq_mul_diagonal]
  · rintro ⟨δ, h⟩
    rw [SpecialLinearGroup.fin_two_ext_iff] at h
    rcases h with ⟨-, h₁, h₂, -⟩
    split_ands <;> simp [d, ← h₁, ← h₂]

lemma SpecialLinearGroup.fin_two_antidiagonal_iff (S : SL(2,F)) :
  S 0 0 = 0 ∧ S 1 1 = 0 ↔ ∃ δ : Fˣ, (d δ) * w = S := by
  constructor
  · rintro ⟨hα, hδ⟩
    have det_eq_one : det (S : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [SpecialLinearGroup.det_coe]
    rw [det_fin_two, hα, hδ, zero_mul, zero_sub, ← neg_mul, neg_mul_comm] at det_eq_one
    have β_is_unit : IsUnit (S 0 1) := by exact isUnit_of_mul_eq_one (S 0 1) (-S 1 0) det_eq_one
    rw [← neg_mul_comm] at det_eq_one
    have neg_β_inv_eq : -(S 0 1)⁻¹ = S 1 0 := by
      rw [neg_inv]
      refine inv_eq_of_mul_eq_one_right det_eq_one
    use β_is_unit.unit
    ext <;>
    simp [d, w, hα, hδ, neg_β_inv_eq]
  · rintro ⟨δ, rfl⟩
    split_ands  <;>
    simp [d, w]


lemma SpecialLinearGroup.fin_two_shear_iff (S : SL(2,F)) :
  S 0 0 = S 1 1 ∧ S 0 1 = 0 ↔ (∃ τ, t τ = S) ∨ ∃ τ, -t τ = S := by
  constructor
  · rintro ⟨α_eq_δ, β_eq_zero⟩
    have α_eq_one_or_neg_one := α_eq_δ.symm ▸ det_eq_mul_diag_of_lower_triangular F S β_eq_zero
    rw [← sq, sq_eq_one_iff] at α_eq_one_or_neg_one
    rcases α_eq_one_or_neg_one with (α_eq_one | α_eq_neg_one)
    · left
      use S.1 1 0
      ext <;> simp [t, α_eq_one, β_eq_zero, α_eq_δ ▸ α_eq_one]
    · right
      use - S.1 1 0
      ext <;> simp [t, α_eq_neg_one, β_eq_zero, α_eq_δ ▸ α_eq_neg_one]
  · rintro (⟨τ,h⟩ | ⟨τ, h⟩)
    repeat' rw [SpecialLinearGroup.fin_two_ext_iff] at h; rcases h with ⟨hα, hβ, -, hδ⟩
    · simp [← hα, ← hδ, ← hβ, t]
    · simp [← hα, ← hδ, ← hβ, t]



/- A 2×2 matrix, G is conjugate to an upper triangular if there exists an invertible matrix
 such that when conjugated the bottom left entry is annhilated
  -/
lemma isConj_upper_triangular_iff [DecidableEq F] [IsAlgClosed F]
  {M : Matrix (Fin 2) (Fin 2) F} :
  (∃ a b d , ∃ (C : SL(2,F)), (C  * M * C⁻¹ : Matrix (Fin 2) (Fin 2) F) = !![a, b; 0, d]) ↔
    ∃ c : SL(2,F), ((c * M * (c⁻¹)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  constructor
  · rintro ⟨a, b, d, c, hc⟩
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
  ext; ring_nf

def SpecialLinearGroup.mk' {n : ℕ}(M : Matrix (Fin n) (Fin n) F) (h : det M = 1) : SL(n, F) :=
  ⟨M, h⟩

-- Note: I do not use IsConj as the the matrix which acts by conjugation has determinant 1
theorem isTriangularizable_of_algClosed [DecidableEq F] [IsAlgClosed F]
  (M : Matrix (Fin 2) (Fin 2) F) :
  ∃ a b d, ∃ (C : SL(2,F)), (C * M * C⁻¹ : Matrix (Fin 2) (Fin 2) F) = !![a, b; 0, d] := by
  let α := M 0 0
  let β := M 0 1
  let γ := M 1 0
  let δ := M 1 1
  have M_coe_eq : M = !![α, β; γ, δ] := by ext <;> rfl
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
  ext
  repeat' field_simp
  ring_nf

lemma upper_triangular_isConj_jordan {a b : F} (hb : b ≠ 0) :
  IsConj !![a, b; 0, a] !![a, 1; 0, a] := by
  use GeneralLinearGroup.mk' !![1 / b, 0; 0, 1]
    (by simp; apply invertibleOfNonzero <| inv_ne_zero hb)
  ext
  repeat' field_simp

lemma lower_triangular_isConj_upper_triangular {a b : F} :
  ∃ C : SL(2,F), C * !![a, 0; -b, a] * C⁻¹ = !![a, b; 0, a] := by
  have h' : det !![0, -1; (1 : F), 0] = 1 := by simp
  use ⟨!![0,-1;(1 : F),0], h'⟩
  simp

lemma mul_left_eq_mul_right_iff {α : Type*}[Monoid α]{N M : α }(c : αˣ) :
  ((c : α) * M = N * (c : α)) ↔ M = c⁻¹ * N * c := by
  constructor
  · intro h
    rw [mul_assoc, ← h, ← mul_assoc, Units.inv_mul, one_mul]
  · intro h
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
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hC]


/-
Lemma 1.5.
Each element of SL(2,F) is conjugate to either
D δ for some δ ∈ Fˣ, or to  ± T τ for some τ ∈ F.
-/
theorem SL2_IsConj_d_or_IsConj_t_or_IsConj_neg_t [DecidableEq F] [IsAlgClosed F] (S : SL(2, F)) :
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
  obtain rfl | had' := eq_or_ne a d
  · right
    simp [← sq] at det_eq_one'
    rcases det_eq_one' with (a_eq_one | a_eq_neg_one)
    · left
      rw [a_eq_one] at h
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
      rw [a_eq_neg_one] at h
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
  · left
    use a_is_unit.unit
    have isConj₁ : ∃ C : SL(2,F), C * S * C⁻¹ =  ⟨!![a, b ; 0, d], det_eq_one⟩ := by
      use C
      apply SpecialLinearGroup.eq_of
      simp only [SpecialLinearGroup.coe_mul]
      rw [h]
    have isConj₂ :
      ∃ C : SL(2,F), C * ⟨!![a, b; 0,d], det_eq_one⟩ * C⁻¹ = ⟨!![a,0;0,d], det_eq_one'⟩ := by
      apply IsConj_coe
      apply upper_triangular_isConj_diagonal_of_nonzero_det _
      intro h
      rw [sub_eq_zero] at h
      contradiction
    simp_rw [← isConj_iff, d_eq_inv_a] at isConj₁ isConj₂
    simp only [SpecialMatrices.d, IsUnit.unit_spec]
    -- conjugation is transitive
    apply IsConj.trans isConj₂.symm isConj₁.symm


#min_imports
