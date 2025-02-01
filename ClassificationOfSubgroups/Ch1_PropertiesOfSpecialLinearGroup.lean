import Mathlib
import ClassificationOfSubgroups.SpecialMatrices
import ClassificationOfSubgroups.SpecialSubgroups

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

instance : Group SL(2,F) := by infer_instance


lemma IsCommutative_iff {G : Type*} [Group G] (H : Subgroup G) :
  IsCommutative H ↔ ∀ x y : H, x * y = y * x := by
  constructor
  · intro h x y
    have := @mul_comm_of_mem_isCommutative G _ H h x y (by simp) (by simp)
    exact SetLike.coe_eq_coe.mp this
  · intro h
    rw [← @le_centralizer_iff_isCommutative]
    intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    simp at hx
    specialize h ⟨x, hx⟩ ⟨y, hy⟩
    simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq] at h
    exact h

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
    ext <;> simp [d, t, mul_comm]
  · rintro ⟨a, c, d, had, hx⟩
    have a_is_unit : IsUnit a := by exact isUnit_of_mul_eq_one a d had
    have a_inv_eq_d : a⁻¹ = d := by exact DivisionMonoid.inv_eq_of_mul a d had
    use a_is_unit.unit, c * a_is_unit.unit
    simp [SpecialMatrices.d, t, lower_triangular, had]
    ext <;> field_simp [a_inv_eq_d, had, hx]; exact Eq.symm (eq_one_div_of_mul_eq_one_right had)

lemma mem_H_iff_lower_triangular' [DecidableEq F] {x : SL(2,F)} :
  x ∈ H F ↔ ∃ a c d, !![a, 0; c, d] = (x : Matrix (Fin 2) (Fin 2) F) := by
  constructor
  · intro hx
    obtain ⟨δ, τ, h⟩ := hx
    use δ, τ * δ⁻¹, δ⁻¹
    rw [← h]
    ext <;> simp [d, t, mul_comm]
  · rintro ⟨a, c, d, hx⟩
    have had : det (x : Matrix (Fin 2) (Fin 2) F) = 1 := by simp
    simp [← hx] at had
    have a_is_unit : IsUnit a := by exact isUnit_of_mul_eq_one a d had
    have a_inv_eq_d : a⁻¹ = d := by exact DivisionMonoid.inv_eq_of_mul a d had
    use a_is_unit.unit, c * a_is_unit.unit
    simp [SpecialMatrices.d, t, lower_triangular, had]
    ext <;> field_simp [a_inv_eq_d, had, ← hx]; exact Eq.symm (eq_one_div_of_mul_eq_one_right had)


/- Lemma 1.2.1.3 -/
def D_iso_units (F : Type*) [Field F] : SpecialSubgroups.D F ≃* Fˣ where
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
                simp [Subgroup.coe_mul, Fin.isValue, SpecialLinearGroup.coe_mul]
                congr
                repeat'
                  simp_rw [← hδ₁, ← hδ₂]
                  simp [SpecialMatrices.d, mul_comm]

lemma IsCommutative_D : IsCommutative (D F) := by
  rw [IsCommutative_iff]
  rintro ⟨x, ⟨δ₁, hδ₁⟩⟩ ⟨y, ⟨δ₂, hδ₂⟩⟩
  simp [@Subtype.ext_val_iff]
  rw [← hδ₁, ← hδ₂]
  simp [mul_comm]


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

lemma IsCommutative_T : IsCommutative (T F) := by
  rw [IsCommutative_iff]
  rintro ⟨x, ⟨τ₁, hτ₁⟩⟩ ⟨y, ⟨τ₂, hτ₂⟩⟩
  simp [@Subtype.ext_val_iff]
  rw [← hτ₁, ← hτ₂]
  simp [add_comm]

/- Lemma 1.2.2.2 H ⧸ T = D -/
-- def quot_iso_subgroupGeneratedByD {F : Type* } [Field F] :
--   H F ⧸ T F ≃* D F := by sorry -- needs HasQuotient

/- Lemma 1.3. Z(SL(2,F)) = ⟨ -I ⟩ .-/
-- def center_of_SL_2_F : center SL(2,F) ≃* rootsOfUnity 2 F  :=
--   Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' 2





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
    simp [hM, algebraMap, Algebra.toRingHom, sub_eq_zero] at M_eq_diagonal
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


/-
Proposition 1.6.i
N_L(T₁) ⊆ H, where T₁ is any subgroup of T with order greater than 1. -/
lemma normalizer_subgroup_T_leq_H [DecidableEq F] { T₀ : Subgroup (SL(2,F)) }
 (hT₀ : 1 < Nat.card T₀ ) (h : T₀ ≤ T F) : normalizer T₀ ≤ H F := by
  intro x hx
  rw [mem_normalizer_iff] at hx
  by_cases h' : ∃ τ, τ ≠ 0 ∧ t τ ∈ T₀
  · obtain ⟨τ, τ_ne_zero, hτ⟩  := h'
    specialize hx (t τ)
    rw [hx] at hτ
    let α := x.1 0 0
    let β := x.1 0 1
    let γ := x.1 1 0
    let δ := x.1 1 1
    have x_eq : x = !![α, β; γ, δ] := by ext <;> rfl
    have : x * t τ * x⁻¹ ∈ T F := by exact h hτ
    obtain ⟨τ' , hτ'⟩ := this
    simp [x_eq] at hτ'
    -- uses decidable equality
    rw [mem_H_iff_lower_triangular', lower_triangular_iff_top_right_entry_eq_zero]
    have β_eq_zero : t τ' 0 1 = 0 := by simp [t]
    rw [hτ'] at β_eq_zero
    simp [x_eq, t] at β_eq_zero
    ring_nf at β_eq_zero
    rw [neg_eq_zero] at β_eq_zero
    apply eq_zero_of_ne_zero_of_mul_right_eq_zero τ_ne_zero at β_eq_zero
    rw [sq_eq_zero_iff] at β_eq_zero
    simp [x_eq]
    exact β_eq_zero
  · push_neg at h'
    have T₀_eq_bot : T₀ = ⊥ := by
      rw [eq_bot_iff_forall]
      intro x hx
      obtain ⟨τ, rfl⟩ := h hx
      specialize h' τ
      rw [not_imp_not] at h'
      specialize h' hx
      simp [h']
    have : Nat.card T₀ = 1 := by simp [T₀_eq_bot]
    -- contradiction with the assumption that Nat.card T₁ > 1
    linarith

def TZ : Subgroup SL(2,F) where
  carrier := { t τ | τ : F } ∪ { - t τ | τ : F }
  mul_mem' := by
    rintro x y (⟨τ₁, rfl⟩ | ⟨τ₁, rfl⟩) (⟨τ₂, rfl⟩ | ⟨τ₂, rfl⟩)
    repeat' simp
  one_mem' := by
    rw [← t_zero_eq_one]; left; use 0
  inv_mem' :=  by
    rintro x (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
    repeat' simp


def TZ' : Subgroup SL(2,F) where
  carrier := T F * Z F
  mul_mem' := by
    rintro a b ⟨t₁, ht₁, ⟨z₁, hz₁, rfl⟩⟩ ⟨t₂, ht₂, ⟨z₂, hz₂, rfl⟩⟩
    simp only [SetLike.mem_coe] at ht₁ ht₂ hz₁ hz₂ ⊢
    group
    have hz₁' := hz₁
    simp [← center_SL2_F_eq_Z ] at hz₁'
    rw [mul_assoc t₁, (mem_center_iff.mp hz₁' t₂).symm]
    group
    use t₁ * t₂
    constructor
    · exact Subgroup.mul_mem _ ht₁ ht₂
    use z₁ * z₂
    constructor
    · exact Subgroup.mul_mem _ hz₁ hz₂
    group
  one_mem' := by
    use 1
    constructor
    · use 0, t_zero_eq_one F
    use 1
    constructor
    · simp
    group
  inv_mem' := by
    rintro x ⟨t, ht, ⟨z, hz, rfl⟩⟩
    simp at ht
    have hz' := hz
    simp [← center_SL2_F_eq_Z] at hz
    simp only [_root_.mul_inv_rev,
       (mem_center_iff.mp ((Subgroup.inv_mem_iff (center SL(2, F))).mpr hz) t⁻¹).symm]
    use t⁻¹
    constructor
    · simp [ht]
    use z⁻¹
    constructor
    · exact (Subgroup.inv_mem_iff (Z F)).mpr hz'
    group

lemma TZ_eq_TZ' {F : Type*} [Field F] : TZ' F = TZ F := by
  ext x
  constructor
  · rintro ⟨t, ht, z, hz, rfl⟩
    simp at hz ht
    obtain ⟨τ, rfl⟩ := ht
    -- z = 1 or z = -1
    rcases hz with (rfl | rfl)
    · left
      use τ
      simp
    · right
      use τ
      simp
  · intro hx
    rcases hx with (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
    · use t τ
      constructor
      · use τ
      use 1
      constructor
      · simp
      · simp
    · use t τ
      constructor
      · use τ
      use -1
      constructor
      · simp
      · simp


lemma T_mul_Z_subset_TZ :
  ((T F) : Set SL(2,F)) * ((Z F) : Set SL(2,F)) ⊆ ((TZ F) : Set SL(2,F)) := by
  rintro x ⟨t', ht', z, hz, hτ, h⟩
  obtain ⟨τ, rfl⟩ := ht'
  dsimp [Z] at hz
  dsimp
  rw [closure_neg_one_eq] at hz
  simp [TZ]
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with (rfl | rfl)
  left
  use τ
  rw [mul_one]
  right
  use τ
  simp


lemma T_join_Z_eq_TZ : T F ⊔ Z F = TZ F := by
  ext x
  constructor
  · intro hx
    rw [sup_eq_closure_mul, mem_closure] at hx
    exact hx (TZ F) (T_mul_Z_subset_TZ F)
  · rintro (⟨τ, rfl⟩ | ⟨τ, rfl⟩) <;> rw [sup_eq_closure_mul]
    · have mem_Z_mul_T : t τ ∈ ((T F) : Set SL(2,F)) * (Z F) := by
        rw [Set.mem_mul]
        use t τ
        split_ands
        simp [Z, closure_neg_one_eq]
        use τ
        simp
      apply Subgroup.subset_closure mem_Z_mul_T
    · have mem_Z_mul_T : -t τ ∈ ((T F) : Set SL(2,F)) * (Z F) := by
        rw [Set.mem_mul]
        use t τ
        split_ands
        simp [Z, closure_neg_one_eq]
        use τ
        simp
      apply Subgroup.subset_closure mem_Z_mul_T



-- ordering propositions so when proving it can be done more efficiently
#check Set.mem_mul



lemma IsCommutative_TZ : IsCommutative (TZ F) := by
  refine le_centralizer_iff_isCommutative.mp ?_
  rintro x (⟨τ₁, rfl⟩ | ⟨τ₁, rfl⟩)
  repeat
  rw [mem_centralizer_iff]
  rintro y (⟨τ₂, rfl⟩ | ⟨τ₂, rfl⟩)
  repeat' simp [add_comm]

lemma centralizer_neg_eq_centralizer {x : SL(2,F)} : centralizer {x} = centralizer {-x} := by
  ext; constructor <;> simp [mem_centralizer_iff_commutator_eq_one]

/- Proposition 1.6.ii C_L(± T τ) = T × Z where τ ≠ 0 -/
def centralizer_t_eq_TZ {τ : F} (hτ : τ ≠ 0) : centralizer { t τ } = TZ F := by
  ext x
  constructor
  · intro hx
    simp [mem_centralizer_iff] at hx
    rw [SpecialLinearGroup.fin_two_ext_iff] at hx
    simp [t] at hx
    obtain ⟨top_right, -, bottom_left, -⟩ := hx
    rcases get_entries F x with ⟨α, β, γ, δ, hα, hβ, -, hδ, x_eq⟩
    simp [x_eq, hτ] at top_right bottom_left
    rw [add_comm γ] at bottom_left
    have α_eq_δ : τ * α = τ * δ := by rw [mul_comm τ δ, eq_iff_eq_of_add_eq_add bottom_left]
    rw [mul_eq_mul_left_iff, or_iff_not_imp_right] at α_eq_δ
    specialize α_eq_δ hτ
    simp [TZ]
    -- is a shear matrix if diagonal entries are equal and top right entry is zero
    rw [← SpecialLinearGroup.fin_two_shear_iff]
    constructor
    -- diagonal entries are equal
    · rw [← hα, ← hδ, α_eq_δ]
    -- top right entry is zero
    · rw [← hβ, top_right]
  · rintro (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
    repeat
    rw [mem_centralizer_iff]
    intro y hy
    simp at hy
    rw [hy]
    simp [add_comm]

theorem val_eq_neg_one {F : Type* } [Field F] {a : Fˣ} : (a : F) = -1 ↔ a = (-1 : Fˣ) := by
  rw [Units.ext_iff, Units.coe_neg_one];


lemma ex_of_card_D_gt_two {D₀ : Subgroup SL(2,F) }(hD₀ : 2 < Nat.card D₀) (D₀_leq_D : D₀ ≤ D F) :
  ∃ δ : Fˣ, (δ : F) ≠ 1 ∧ (δ : F) ≠ -1 ∧ d δ ∈ D₀ := by
  by_contra! h
  have D₀_le_Z : D₀.carrier ≤ Z F := by
    simp
    intro x hx
    obtain ⟨δ, rfl⟩ := D₀_leq_D hx
    rw [Set.mem_insert_iff]
    by_cases h₀ : (δ : F) = 1
    · left;
      rw [Units.val_eq_one] at h₀
      rw [h₀, d_one_eq_one]
    · by_cases h₁ : (δ : F) = -1
      · right;
        push_cast at h₁
        rw [val_eq_neg_one] at h₁
        rw [h₁, d_neg_one_eq_neg_one, Set.mem_singleton_iff]
      · rw [← ne_eq] at h₀ h₁
        specialize h δ h₀ h₁
        contradiction
  have card_D₀_leq_two : Nat.card D₀ ≤ 2 :=
    le_trans (Subgroup.card_le_of_le D₀_le_Z) (card_Z_le_two _)
  linarith


lemma mem_D_iff {S : SL(2,F)} : S ∈ D F ↔ ∃ δ : Fˣ, d δ = S := by rfl


lemma mem_D_w_iff {S : SL(2,F)} : S ∈ (D F : Set SL(2,F)) * {w} ↔ ∃ δ : Fˣ, d δ * w = S := by
  constructor
  · rintro ⟨d', ⟨δ, rfl⟩, w, ⟨rfl⟩, rfl⟩
    use δ
  · rintro ⟨δ, rfl⟩
    simp [D]
    use δ
    rw [mul_assoc, w_mul_w_eq_neg_one, mul_neg, mul_one, neg_neg]

/-
Proposition 1.7.
(i) N_L (D₁) = ⟨D, W⟩, where D₁ is any subgroup of D with order greater than 2.
-/
lemma normalizer_subgroup_D_eq_DW { D₀ : Subgroup (SL(2,F)) }
 (hD₀ : 2 < Nat.card D₀ ) (D₀_leq_D : D₀ ≤ D F) : normalizer D₀ ≤ DW F := by
  intro x hx
  rw [@mem_normalizer_iff] at hx
  have ⟨δ', h₀, h₁, hδ'⟩ := ex_of_card_D_gt_two F hD₀ D₀_leq_D
  specialize hx (d δ')
  rw [hx] at hδ'
  have mem_D := D₀_leq_D hδ'
  rw [mem_D_iff, ← SpecialLinearGroup.fin_two_diagonal_iff] at mem_D
  rcases get_entries F x with ⟨α, β, γ, δ, hα, hβ, hγ, hδ, x_eq⟩
  rcases mem_D with ⟨top_right, bottom_left⟩
  simp [d, x_eq] at top_right bottom_left
  ring_nf at top_right bottom_left
  have top_right_eq : -(α * ↑δ' * β) + α * β * (↑δ')⁻¹ = α * β * ((↑δ')⁻¹ - ↑δ') := by ring
  have bottom_left_eq : ↑δ' * γ * δ - (↑δ')⁻¹ * γ * δ  = γ * δ * (↑δ' - (↑δ')⁻¹) := by ring
  replace top_right := top_right_eq ▸ top_right
  replace bottom_left := bottom_left_eq ▸ bottom_left
  have det_eq_one : det (x : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [SpecialLinearGroup.det_coe]
  have δ_sub_δ_inv_ne_zero : (δ' : F)⁻¹ - δ' ≠ 0 := by
    field_simp
    intro h
    rw [sub_eq_zero, ← sq] at h
    symm at h
    rw [sq_eq_one_iff] at h
    apply not_or_intro h₀ h₁ h
  have δ_inv_neg_δ_ne_zero : (δ') - (δ' : F)⁻¹ ≠ 0 := by
    rw [← neg_ne_zero, neg_sub]; exact δ_sub_δ_inv_ne_zero
  have α_or_β_eq_zero : α * β = 0 :=
    eq_zero_of_ne_zero_of_mul_right_eq_zero δ_sub_δ_inv_ne_zero top_right
  have γ_or_δ_eq_zero : γ * δ = 0 :=
    eq_zero_of_ne_zero_of_mul_right_eq_zero δ_inv_neg_δ_ne_zero bottom_left
  rw [mul_eq_zero] at α_or_β_eq_zero γ_or_δ_eq_zero
  rcases α_or_β_eq_zero with (α_eq_zero | β_eq_zero) <;>
  rcases γ_or_δ_eq_zero with (γ_eq_zero | δ_eq_zero)
  · have det_eq_zero : det (x : Matrix (Fin 2) (Fin 2) F) = 0 := by
      rw [det_fin_two, ← hα, ← hγ, α_eq_zero, γ_eq_zero, mul_zero, zero_mul, sub_zero]
    rw [det_eq_zero] at det_eq_one
    absurd zero_ne_one det_eq_one
    trivial
  · apply Dw_leq_DW
    rw [mem_D_w_iff, ← SpecialLinearGroup.fin_two_antidiagonal_iff]
    simp_rw [← hα, ← hδ, α_eq_zero, δ_eq_zero]
    trivial
  · apply D_leq_DW
    rw [mem_D_iff, ← SpecialLinearGroup.fin_two_diagonal_iff]
    simp_rw [← hβ, ← hγ, β_eq_zero, γ_eq_zero]
    trivial
  · have det_eq_zero : det (x : Matrix (Fin 2) (Fin 2) F) = 0 := by
      rw [det_fin_two, ← hβ, ← hδ, β_eq_zero, δ_eq_zero, mul_zero, zero_mul, sub_zero]
    rw [det_eq_zero] at det_eq_one
    absurd zero_ne_one det_eq_one
    trivial

lemma Field.self_eq_inv_iff (x : F) (x_ne_zero : x ≠ 0) : x = x⁻¹ ↔ x = 1 ∨ x = - 1 := by
  rw [← sq_eq_one_iff, sq, propext (mul_eq_one_iff_eq_inv₀ x_ne_zero)]

lemma Units.val_neg_one : ((-1 : Fˣ) : F) = -1 := by simp only [Units.val_neg, val_one]

lemma Units.val_eq_neg_one (x : Fˣ) : (x : F) = -1 ↔ x = (-1 : Fˣ) := by
  rw [← Units.val_neg_one, eq_iff]

lemma centralizer_d_eq_D (δ : Fˣ) (δ_ne_one : δ ≠ 1) (δ_ne_neg_one : δ ≠ -1) :
  centralizer {d δ} = D F := by
  ext x
  constructor
  · intro hx
    simp [mem_centralizer_iff] at hx
    rcases get_entries F x with ⟨a, b, c, d, _ha, hb', hc', _hd, x_eq⟩
    simp [SpecialLinearGroup.fin_two_ext_iff, SpecialMatrices.d, x_eq] at hx
    obtain ⟨-, hb, hc, -⟩ := hx
    have δ_ne_zero : (δ : F) ≠ 0 := Units.ne_zero δ
    have δ_ne_δ_inv : (δ : F) ≠ δ⁻¹ := by
      intro h
      rw [Field.self_eq_inv_iff F _ δ_ne_zero] at h
      simp_rw [Units.val_eq_one, Units.val_eq_neg_one] at h
      absurd not_or.mpr ⟨δ_ne_one, δ_ne_neg_one⟩ h
      trivial
    rw [mul_comm, mul_eq_mul_left_iff] at hb hc
    replace hb := Or.resolve_left hb δ_ne_δ_inv
    replace hc := Or.resolve_left hc δ_ne_δ_inv.symm
    rw [mem_D_iff, ← SpecialLinearGroup.fin_two_diagonal_iff]
    simp [hb, hc, ← hb', ← hc']
  · rintro ⟨δ', rfl⟩
    simp [mem_centralizer_iff, mul_comm]

lemma centralizer_d_eq_D' (δ : Fˣ) (hd: d δ ∉ center SL(2,F)) : centralizer {d δ} = D F := by
  simp [center_SL2_F_eq_Z, ← ne_eq] at hd
  apply centralizer_d_eq_D F δ
  · rintro rfl
    simp at hd
  · rintro rfl
    simp at hd

open MulAction MulAut

/-
Proposition 1.8.
Let a and b be conjugate elements in a group G. Then ∃ x ∈ G such that x C_G(a) x⁻¹ = C_G (b).
-/
lemma conjugate_centralizers_of_IsConj  (a b : G) (hab : IsConj a b) :
  ∃ x : G, conj x • (centralizer { a }) = centralizer { b } := by
  rw [isConj_iff] at hab
  obtain ⟨x, hc⟩ := hab
  use x
  ext y
  simp [centralizer, MulAut.conj]
  constructor
  · rintro ⟨y', y'_in_cen, hy'⟩
    simp at hy' y'_in_cen ⊢
    rw [Set.mem_centralizer_iff]
    rintro m ⟨rfl⟩
    have : a * y' = y' * a := by exact y'_in_cen a rfl
    rw [← hy', ← hc]
    group
    rw [mul_assoc x a, this]
    group
  · intro hy
    simp [Set.mem_centralizer_iff] at hy
    have : y = b * y * b⁻¹ := by rw [hy]; group
    simp [← hc] at this hy
    use a * x⁻¹ * y * x * a⁻¹
    split_ands
    · simp
      rw [Set.mem_centralizer_iff]
      simp_rw [Set.mem_singleton_iff, forall_eq, inv_mul_cancel_right]
      nth_rewrite 1 [← mul_one a, ← inv_mul_cancel x]
      have helper: a * (x⁻¹ * x) * (a * x⁻¹ * y * x * a⁻¹) =
        a * x⁻¹ * (x * a * x⁻¹ * y * x * a⁻¹) := by group
      rw [helper, hy]
      group
    · simp
      group at hy ⊢
      rw [hy]
      group


lemma conjugate_IsComm_of_IsComm' {G : Type*} [Group G] (c : G)(H K : Subgroup G)
  (hK : IsCommutative K)(h : conj c • K = H) : IsCommutative H := by
  rw [IsCommutative_iff]
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  rw [le_antisymm_iff] at h
  obtain ⟨- , H_le_conj_K⟩ := h
  rcases H_le_conj_K hx with ⟨c₁, hc₁, eq_x⟩
  rcases H_le_conj_K hy with ⟨c₂, hc₂, eq_y⟩
  simp at eq_x eq_y
  have := @mul_comm_of_mem_isCommutative G _ K _ c₁ c₂ hc₁ hc₂
  simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq]
  rw [← eq_x, ← eq_y]
  group
  simp
  rw [mul_assoc, this]
  group

lemma conjugate_IsComm_of_IsComm {G : Type*} [Group G] (c : G)(K : Subgroup G)
  (hK : IsCommutative K) : IsCommutative (conj c • K) := by
  let H := conj c • K
  have H_eq : MulAut.conj c • K = H := rfl
  exact @conjugate_IsComm_of_IsComm' G _ c H K hK H_eq

lemma MulAut.conj_smul_symm {G : Type*} [Group G] (H K : Subgroup G) (c : G)
 (h : conj c • H = K) : ∃ c' : G, conj c' • K = H := ⟨c⁻¹, by simp [← h]⟩
/-
Corollary 1.9.
The centraliser of an element x in L is abelian unless x belongs to the centre of L.
-/
lemma IsCommutative_centralizer_of_not_mem_center [IsAlgClosed F] [DecidableEq F](x : SL(2,F))
  (hx : x ∉ center SL(2,F)) : IsCommutative (centralizer { x }) := by
  rcases SL2_IsConj_d_or_IsConj_t_or_IsConj_neg_t F x with
    (⟨δ, x_IsConj_d⟩ | ⟨τ, x_IsConj_t⟩ | ⟨τ, x_IsConj_neg_t⟩ )
  · obtain ⟨x, centralizer_x_eq⟩ := conjugate_centralizers_of_IsConj (d δ) x x_IsConj_d
    have δ_ne_one : δ ≠ 1 := by
      rintro rfl
      simp at x_IsConj_d
      rw [← x_IsConj_d, center_SL2_F_eq_Z] at hx
      simp at hx
    have δ_ne_neg_one : δ ≠ -1 := by
      rintro rfl
      simp at x_IsConj_d
      rw [← x_IsConj_d, center_SL2_F_eq_Z] at hx
      simp at hx
    rw [← centralizer_x_eq, centralizer_d_eq_D _ _ δ_ne_one δ_ne_neg_one]
    apply conjugate_IsComm_of_IsComm
    exact IsCommutative_D F
  · obtain ⟨x, centralizer_S_eq⟩ := conjugate_centralizers_of_IsConj (t τ) x x_IsConj_t
    have τ_ne_zero : τ ≠ 0 := by
      rintro rfl
      simp at x_IsConj_t
      rw [← x_IsConj_t, center_SL2_F_eq_Z] at hx
      simp at hx
    rw [← centralizer_S_eq, centralizer_t_eq_TZ F τ_ne_zero]
    apply conjugate_IsComm_of_IsComm
    exact IsCommutative_TZ F
  · obtain ⟨x, centralizer_S_eq⟩ := conjugate_centralizers_of_IsConj (-t τ) x x_IsConj_neg_t
    have τ_ne_zero : τ ≠ 0 := by
      rintro rfl
      simp at x_IsConj_neg_t
      rw [← x_IsConj_neg_t, center_SL2_F_eq_Z] at hx
      simp at hx
    rw [← centralizer_S_eq,  ← centralizer_neg_eq_centralizer, centralizer_t_eq_TZ F τ_ne_zero]
    apply conjugate_IsComm_of_IsComm
    exact IsCommutative_TZ F
