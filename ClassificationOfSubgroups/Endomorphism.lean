import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Basis.VectorSpace


universe u v

variable (F : Type u) (M : Type v) [Field F] [AddCommGroup M] [Module F M] (σ : F →+* F)


instance : DivisionRing F := by exact Field.toDivisionRing

-- instance : NonAssocSemiring F
open Basis

example : M →ₗ[F] M where
  toFun v := 3 • v
  map_add' _ _ := smul_add ..
  map_smul' _ _ := smul_comm ..

#check ofVectorSpaceIndex

def mul_scalar (μ : F) : M →ₗ[F] M where
  toFun := fun x => μ • x
  map_add' := by intro x y; simp only [smul_add]
  map_smul' := by intro m x; simp only [smul_smul, RingHom.id_apply, mul_comm]

-- How to construct a suitable linear mapping so that I can show that the endomorphism sends an arbitrary vector to a scalar multiple of itself

theorem exists_scalar_of_commutes { φ : Module.End F M } (hφ : IsUnit φ) {x : M} (h : ∀ (ϕ : Module.End F M), IsUnit ϕ → φ (ϕ x) = ϕ (φ x)): ∃ μ : F, φ x = μ • x := by
  -- obtain ⟨s, hs⟩ := Basis.exists_basis F M
  sorry

theorem exists_scalar_of_scalar { φ : Module.End F M } (hφ₁ : IsUnit φ) : ∃ μ : F, ∀ y : M,  φ y = μ • y := by
  sorry

theorem commutes_of_exists_scalar { φ : Module.End F M } (hφ₁ : IsUnit φ) (hφ₂ : ∀ y : M, ∃ μ : F, φ y = μ • y) { x : M }: ∀ ϕ : Module.End F M, IsUnit ϕ → ϕ (φ x) = φ (ϕ x) := by
  sorry
