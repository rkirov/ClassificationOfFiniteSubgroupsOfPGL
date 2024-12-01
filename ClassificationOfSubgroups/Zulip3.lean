import Mathlib

universe u

variable (F : Type u) [Field F]

open Matrix MatrixGroups

instance : Group SL(2,F) := by infer_instance

@[ext]
lemma SL2_ext {F : Type*} [Field F] (A B : SL(2,F))
    (h00 : A.1 0 0 = B.1 0 0) (h01 : A.1 0 1 = B.1 0 1) (h10 : A.1 1 0 = B.1 1 0)
    (h11 : A.1 1 1 = B.1 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

def SpecialMatrices.D {F : Type*} [Field F] (δ : Fˣ) : SL(2, F) :=
  ⟨!![(δ : F), (0 : F); (0 :F) , (δ⁻¹ : F)], by norm_num⟩

open SpecialMatrices

@[simp]
lemma D_1_eq_one : D (1 : Fˣ) = 1 := by ext <;> simp [D]

@[simp]
lemma inv_D_eq (δ : Fˣ) : (D δ)⁻¹ = D (δ⁻¹) := by simp [Matrix.SpecialLinearGroup.SL2_inv_expl, D]; rfl

lemma lemma_1_1_i (δ ρ : Fˣ) : D δ * D ρ = D (δ * ρ) := by ext <;> simp [D, mul_comm]

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

/- Lemma 1.2.1.3 -/
def subgroupOfD_iso_units_of_F : subgroupGeneratedByD F ≃* Fˣ where
  toFun D := by
            use D.val 0 0, D.val 1 1
            repeat'
              obtain ⟨δ, hδ⟩ := D.property
              rw [← hδ]
              simp [SpecialMatrices.D]
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
