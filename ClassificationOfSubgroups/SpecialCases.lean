import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic


namespace SpecialCases

open scoped MatrixGroups

open Matrix

universe u v

variable (n : Type u) [Fintype n] [DecidableEq n] (F : Type v) [Field F]

@[inherit_doc]
scoped[MatrixGroups] notation "GL(" n ", " R ")" => Matrix.GeneralLinearGroup (Fin n) R

-- theorem coe_mk (A : Matrix n n R) (h : IsUnit (det A)) : ↑(⟨A, h.1, h.2, h.3⟩ : GeneralLinearGroup n R) = A :=
--   rfl

variable (R : Type u) [CommRing R] in
theorem GL2_det_of_adjugate_is_unit (A : GL(2,R)) : IsUnit (det ((A.1.adjugate))) := by
  rw [adjugate_fin_two, det_fin_two]
  simp
  simp_rw [mul_comm (A 1 1) _, ← det_fin_two]
  exact isUnits_det_units A

lemma GL2_left_inv (A : (GeneralLinearGroup (Fin 2) F)): ((det A.1)⁻¹ • A.1.adjugate) * A.1 = 1 := by
    rw [smul_mul, adjugate_mul]
    refine inv_smul_smul₀ ?_ 1
    exact det_ne_zero_of_right_inverse A.3

lemma GL2_right_inv (A : (GeneralLinearGroup (Fin 2) F)): A.1 * ((det A.1)⁻¹ • A.1.adjugate) = 1 := by
    rw [mul_eq_one_comm]
    exact GL2_left_inv F A

local notation:1024 "↑ₘ" A:1024 => ((A : GeneralLinearGroup n F) : Matrix n n F)

@[simp]
theorem coe_inv (A : GeneralLinearGroup n F) : ↑ₘA⁻¹ = (det A.1)⁻¹ • adjugate A := by
  rw [← Units.mul_eq_one_iff_inv_eq, mul_eq_one_comm, smul_mul, adjugate_mul]
  refine inv_smul_smul₀ ?_ 1
  exact det_ne_zero_of_right_inverse A.3


instance : CommRing F := Field.toCommRing

@[simp]
theorem GL2_inv_expl (A : GL(2, F)) :
    ((A⁻¹ :  GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = (det A.1)⁻¹ • !![A.1 1 1, -A.1 0 1; -A.1 1 0, A.1 0 0] := by
    rw [coe_inv, ← @adjugate_fin_two]




end SpecialCases
