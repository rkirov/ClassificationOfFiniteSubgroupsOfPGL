import Mathlib

open Matrix MatrixGroups Subgroup Pointwise

universe u

variable
  (F : Type u) [Field F]
  (n : Type u) [Fintype n]
  (R : Type u) [CommRing R]

@[ext]
lemma Matrix.fin_two_ext { R : Type*} [CommSemiring R] {M N : Matrix (Fin 2) (Fin 2) R}
  (h₀₀ : M 0 0 = N 0 0)(h₀₁ : M 0 1 = N 0 1)(h₁₀ : M 1 0 = N 1 0)(h₁₁ : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

@[ext]
lemma SpecialLinearGroup.fin_two_ext (A B : SL(2,R))
    (h₀₀ : A.1 0 0 = B.1 0 0) (h₀₁ : A.1 0 1 = B.1 0 1) (h₁₀ : A.1 1 0 = B.1 1 0)
    (h₁₁ : A.1 1 1 = B.1 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

namespace SpecialMatrices

def t {F : Type*} [Field F] (τ : F): SL(2,F) :=
  ⟨!![1, 0; τ, 1], by simp⟩

section Shear

@[simp]
lemma t_zero_eq_one : t (0 : F) = 1 := by ext <;> rfl

lemma t_eq_t_iff (τ μ : F) : t τ = t μ ↔ τ = μ := by
  constructor
  · intro h
    rw [SpecialLinearGroup.fin_two_ext_iff] at h
    obtain ⟨-, -, h, -⟩ := h
    exact h
  · exact fun a ↦ congrArg t a

lemma t_eq_one_iff (τ : F) : t τ = 1 ↔ τ = 0 := by
  exact (t_zero_eq_one F).symm ▸ t_eq_t_iff F τ 0

@[simp]
lemma t_inv (τ : F) : (t τ)⁻¹ = t (-τ) := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl, t]; rfl

@[simp]
lemma inv_neg_t_eq (τ : F) : (- t τ)⁻¹ = - t (-τ) := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext <;> simp [t]

-- (ii)
@[simp]
lemma t_mul_t_eq_t_add (τ μ : F) : t τ * t μ = t (τ + μ) := by ext <;> simp [t]

@[simp]
lemma t_pow_eq_t_mul (τ : F) (n : ℕ) : (t τ)^n = t (n • τ) := by
  induction n
  case zero => simp
  case succ k hk =>
    simp [pow_add, hk]
    congr
    ring

lemma order_t_eq_char {p : ℕ} [hp : Fact (Nat.Prime p)] [hC : CharP F p]
  (τ : F) (hτ : τ ≠ 0) : orderOf (t τ) = p := by
  refine orderOf_eq_prime ?hg ?hg1
  · simp
  · contrapose! hτ
    exact (t_eq_one_iff F τ).mp hτ

end Shear

section Diagonal

def d {F : Type*} [Field F] (δ : Fˣ) : SL(2, F) :=
  ⟨!![(δ : F), (0 : F); (0 :F) , (δ⁻¹ : F)], by norm_num⟩

@[simp]
lemma inv_d_eq_d_inv (δ : Fˣ) : (d δ)⁻¹ = d (δ⁻¹) := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl, d]; rfl

lemma d_eq_inv_d_inv (δ : Fˣ) : d δ = (d δ⁻¹)⁻¹ := by
  rw [inv_d_eq_d_inv, inv_inv]

lemma d_eq_diagonal (δ : Fˣ) :
  (d δ : Matrix (Fin 2) (Fin 2) F) = diagonal (fun i ↦ if i.val = 0 then (δ : F) else δ⁻¹) := by
  ext <;> simp [d]

@[simp]
lemma d_one_eq_one : d (1 : Fˣ) = 1 := by ext <;> simp [d]

@[simp]
lemma d_neg_one_eq_neg_one : d (-1 : Fˣ) = -1 := by ext <;> simp [d, inv_neg_one]

@[simp]
lemma neg_d_eq_d_neg (δ : Fˣ) : - d δ = d (-δ) :=  by ext <;> simp [d, inv_neg]

lemma d_coe_eq { δ : Fˣ} : (d (δ : Fˣ) : Matrix (Fin 2) (Fin 2) F) = !![(δ : F), 0; 0, δ⁻¹] := by
  apply Matrix.fin_two_ext
  repeat' simp [d]

lemma d_0_0_is_unit (δ : Fˣ) : IsUnit ((d δ) 0 0) := by simp [d]

-- (i)
@[simp]
lemma d_mul_d_eq_d_mul (δ ρ : Fˣ) : d δ * d ρ = d (δ * ρ) := by ext <;> simp [d, mul_comm]

end Diagonal

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

section Rotation

-- Defines the matrix which corresponds to a rotation by `π / 2` radians
def w {F : Type*} [Field F] : SL(2, F) :=
  ⟨!![0,1;-1,0], by norm_num⟩

@[simp]
lemma w_inv {F : Type*} [Field F] :
  (w : SL(2,F))⁻¹  = - w := by ext <;> simp [w]

lemma w_mul_w_eq_neg_one: w * w = (-1 : SL(2,F)) := by ext <;> simp [w]

end Rotation

section Interactions

def dt {F : Type*} [Field F] (δ : Fˣ) (τ : F) : SL(2, F) :=
  ⟨!![δ, 0; τ * δ⁻¹, δ⁻¹], by norm_num⟩

-- Lemma 1.1.iii
lemma d_mul_t_mul_d_inv_eq_t' (δ : Fˣ) (τ : F) : d δ * t τ * (d δ)⁻¹ = t (τ * δ⁻¹ * δ⁻¹) := by
  simp; ext <;> simp [t, d, mul_comm]

def dw {F : Type*} [Field F] (δ : Fˣ) : SL(2,F) :=
  ⟨!![0, δ; -δ⁻¹, 0], by norm_num⟩

lemma d_mul_t_eq_dt (δ : Fˣ) (τ : F) : d δ * t τ = dt δ τ := by ext <;> simp [d, t, dt, mul_comm]

lemma d_mul_w_eq_dw (δ : Fˣ) : d δ * w = dw δ := by ext <;> simp [d, w, dw]

@[simp]
lemma inv_of_d_mul_w (δ : Fˣ) : (d δ * w)⁻¹ = d (-δ) * w := by
  simp [Matrix.mul_inv_rev]
  ext <;> simp [d, w, inv_neg]

-- (iv)
lemma w_mul_d_mul_inv_w_eq_inv_d (δ : Fˣ) : w * (d δ) * w⁻¹ = (d δ)⁻¹ := by
  simp; ext <;> simp [d, w]

@[simp]
lemma w_mul_d_eq_d_inv_w  (δ : Fˣ):  w * (d δ) = (d δ)⁻¹ * w :=  by
  rw [← mul_inv_eq_iff_eq_mul]
  exact w_mul_d_mul_inv_w_eq_inv_d _ _

@[simp]
lemma neg_d_mul_w (δ : Fˣ) : -(d δ * w) = d (-δ) * w := by rw [← neg_mul, neg_d_eq_d_neg]

end Interactions

end SpecialMatrices
