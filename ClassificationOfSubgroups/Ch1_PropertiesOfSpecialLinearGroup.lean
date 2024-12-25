import Mathlib
import ClassificationOfSubgroups.SpecialCases


set_option linter.style.longLine true

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

namespace SpecialMatrices
def T {F : Type*} [Field F] (τ : F): SL(2, F) :=
  ⟨!![1, 0; τ, 1], by norm_num⟩

@[simp]
lemma T_0_eq_one : T (0 : F) = 1 := by ext <;> rfl

def D {F : Type*} [Field F] (δ : Fˣ) : SL(2, F) :=
  ⟨!![(δ : F), (0 : F); (0 :F) , (δ⁻¹ : F)], by norm_num⟩

lemma D_eq_diagonal (δ : Fˣ) : (D δ : Matrix (Fin 2) (Fin 2) F) = diagonal (fun i ↦ if i.val = 0 then (δ : F) else δ⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [D]

@[simp]
lemma D_one_eq_one : D (1 : Fˣ) = 1 := by ext <;> simp [D]

@[simp]
lemma D_neg_one_eq_neg_one : D (-1 : Fˣ) = -1 := by ext <;> simp [D, inv_neg_one]


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
def subgroupGeneratedByT (F : Type*)  [Field F] : Subgroup SL(2,F) where
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

def subgroupGeneratedByDT (F : Type*) [Field F] : Subgroup SL(2,F) where
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
def subgroupOfT_iso_F {F : Type*} [Field F] : (subgroupGeneratedByT F) ≃* (Multiplicative F) where
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
def center_of_SL_2_F : center SL(2,F) ≃* rootsOfUnity 2 F  := by apply Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity' 2


-- instance Module.End (Matrix (Fin 2) (Fin 2) F) := by sorry



instance : Monoid SL(2,F) := Matrix.SpecialLinearGroup.monoid

instance : Module F (Matrix (Fin 2) (Fin 2) F) := by exact module


def toEnd (S : SL(2,F)) : ((Fin 2) → F) →ₗ[F] ((Fin 2) → F) where
  toFun v := S *ᵥ v
  map_add' v w := by exact mulVec_add _ v w
  map_smul' a v := by exact mulVec_smul _ a v

-- theorem Matrix2_square_zero_of_is_nilpotent {F : Type*} [Field F] {F : Type*} [Field F] (n : Module.End F (Fin 2 → F)) (hn : IsNilpotent n)  : n^2 = 0 := by
--   obtain ⟨m, hm⟩ := hn
--   by_cases hm' : (1 ≤ m)
--   by_cases h : (∃ v : Fin 2 → F, v ∉ LinearMap.ker n)
--   · obtain ⟨v, hv⟩ := h
--     rw [LinearMap.mem_ker] at hv
--     let b : (Fin 2) → (Fin 2 → F) := fun i => match i with
--                                               | 0 => v
--                                               | 1 => n v

--     have b_indep: LinearIndependent F b := by
--       rw [linearIndependent_fin2]
--       constructor
--       · simp [b, hv]
--       · intro α h₀
--         simp_rw [b] at h₀
--         have h₁ : (n^(m - 1)) (α •  n v) = 0 := by rw [LinearMap.map_smul_of_tower, ← LinearMap.mul_apply, mul_eq_comp, ← iterate_succ, Nat.sub_one_add_one_eq_of_pos hm', hm]; simp
--         rw [h₀] at h₁
--         have zero_le_m : 0 ≤ m := by linarith
--         have : n v = 0 := by
--           induction m using @Nat.decreasingInduction' (n := (m))
--           case h k' hk'₁ hk'₂ hk'₃  => sorry
--           case mn k' => exact le_refl m
--           case hP k' => sorry
--         sorry

-- example (b : ι → V) (b_indep : LinearIndependent K b)
--     (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) (i : ι) :
--     Basis.mk b_indep (fun v _ ↦ b_spans v) i = b i :=
--   Basis.mk_apply b_indep (fun v _ ↦ b_spans v) i
-- theorem Matrix2_is_nilpotent_iff_zero_or_upper_triangular {F : Type*} [Field F] (n : Module.End F (Fin 2 → F)) (hn : IsNilpotent n) : IsConj n 0 ∨ IsConj n !![0, 1; 0, 0] := by sorry

open Submodule Cardinal Module

-- theorem theorem_1_5₁ [IsAlgClosed F] (S : SL(2,F)) : (∃ δ : Fˣ, @IsConj (GL (Fin 2) F) _ S (D δ)) ∨ (∃ τ : F, @IsConj (GL (Fin 2) F) _ S (T τ)) := by
--   let s := (Matrix.toLin (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) (S : Matrix (Fin 2) (Fin 2) F))
--   obtain ⟨ξ₁, hξ₁⟩ := by apply Module.End.exists_eigenvalue s
--   obtain ⟨v₁, hv₁, v_ne_zero⟩ := by apply Module.End.HasEigenvalue.exists_hasEigenvector hξ₁
--   let H₁ := span F {v₁}
--   by_cases exists_linearly_independependent : ∃ v ∉ H₁, v ∉ LinearMap.ker (s - ξ₁ • 1)
--   · obtain ⟨v₂, v₂_not_in_H₁, v₂_not_in_eigenspace⟩ := exists_linearly_independependent
--     have v₂_ne_zero : v₂ ≠ 0 := by
--       intro v₂_eq_zero
--       have v₂_in_eigenspace : v₂ ∈ LinearMap.ker (s - ξ₁ • 1) := by simp [v₂_eq_zero]
--       contradiction
--     -- We define the complementary space spanned by v₂, H₂
--     let H₂ := span F {v₂}
--     -- We now show that they are indeed complementary
--     have H₁_IsCompl_H₂ : IsCompl H₁ H₂ :=  by
--       rw [isCompl_iff]
--       constructor
--       -- We prove they are disjoint
--       case left =>
--         rw [disjoint_iff]
--         ext w
--         constructor
--         · rintro ⟨w_in_H₁, w_in_H₂⟩
--           rw [← zero_eq_bot]
--           simp [H₁, H₂, LinearMap.span_singleton_eq_range] at w_in_H₁ w_in_H₂
--           sorry
--         sorry
--       -- We prove they are codisjoint
--       case right =>
--         rw [codisjoint_iff]
--         sorry
--     -- s restricted to the eigenspace that is the map s' : V ⧸ H₁ → V ⧸ H₁ has an eigenvalue, ξ₂ which is equal to s ∘ can_H₁ = s'
--     -- and a corresponding eigenvector v₂' which when pulled back through can_H₁ is v₂, the desired eigenvector which spans H₂.
--     sorry
--   -- Every other vector that does not belong to the span of v₁ belongs to the kernel of s - ξ₁ • 1
--   · push_neg at exists_linearly_independependent
--     sorry

#check LinearMap.span_singleton_eq_range
#check rank_fin_fun
#check rank_top
#check rank_submodule_le_one_iff
#check Submodule.rank_sup_add_rank_inf_eq
#check Submodule.mem_inf
#check Submodule.span_le
-- [https://leanprover-community.github.io/mathematics_in_lean/C09_Linear_Algebra.html#matrices-bases-and-dimension]
/- Requires Jordan Normal Form -/
/- Lemma 1.5. Each element of SL(2,F) is conjugate to either D δ for some δ ∈ Fˣ, or to  ± T τ for some τ ∈ F .-/
-- open Polynomial in
-- theorem theorem_1_5₂ [IsAlgClosed F] (S : SL(2,F)) : (∃ δ : Fˣ, @IsConj (GL (Fin 2) F) _ S (D δ)) ∨ (∃ τ : F, @IsConj (GL (Fin 2) F) _ S (T τ)) := by
--   let inst1 : PerfectField F := IsAlgClosed.perfectField F
--   obtain ⟨n, hn, f, hf, n_is_nilpotent, f_is_semisimple, hfn⟩ := @Module.End.exists_isNilpotent_isSemisimple F ((Fin 2) → F) _ _ _ (@toEnd F _ S) _ _--((toLinAlgEquiv (Pi.basisFun F (Fin 2))) S)
--   rw [← LinearMap.isNilpotent_toMatrix_iff (Pi.basisFun F (Fin 2))] at n_is_nilpotent
--   rw [@Module.End.isSemisimple_iff] at f_is_semisimple

--   -- Obtain eigenvalue, ξ₁ and eigenvector v₁
--   obtain ⟨ξ₁, hξ₁⟩ := by apply Module.End.exists_eigenvalue f--(Matrix.toLin (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) (S : Matrix (Fin 2) (Fin 2) F))
--   obtain ⟨v₁, hv₁, v₁_ne_zero⟩ := by apply Module.End.HasEigenvalue.exists_hasEigenvector hξ₁
--   -- Define the submodule generated by v₁
--   let H₁ := Submodule.span F {v₁}
--   have rank_H₁_leq_one_cardinal : Module.rank F H₁ ≤ 1 := by
--     dsimp [H₁]
--     rw [rank_submodule_le_one_iff]
--     exact ⟨v₁, mem_span_singleton_self _, le_refl _⟩
--   have rank_H₁_not_lt_one_cardinal : ¬ Module.rank F H₁ < 1 := by simp [H₁, v₁_ne_zero]
--   have rank_H₁_eq_one_cardinal : Module.rank F H₁ = 1 := by apply eq_of_le_of_not_lt rank_H₁_leq_one_cardinal rank_H₁_not_lt_one_cardinal
--   have rank_H₁_eq_one := Module.rank_eq_one_iff_finrank_eq_one.mp rank_H₁_eq_one_cardinal
--   have H₁_submodule_of_comap :  H₁ ≤ Submodule.comap f H₁:= by
--     intro w hw
--     simp [H₁, LinearMap.span_singleton_eq_range] at hw ⊢
--     rw [Module.End.mem_unifEigenspace_one] at hv₁
--     rcases hw with ⟨α, rfl⟩
--     use α * ξ₁
--     rw [LinearMap.map_smul, hv₁, smul_smul]
--     done
--   -- From Jordan-Chevallier obtain complementary submodule H₂
--   obtain ⟨H₂, H₂_submodule_of_comap, H₁_is_compl_to_H₂⟩ := f_is_semisimple H₁ H₁_submodule_of_comap
--   rcases H₁_is_compl_to_H₂ with ⟨H₁_disjoint_H₂, H₁_codisjoint_H₂⟩
--   apply Disjoint.le_bot at H₁_disjoint_H₂
--   apply Codisjoint.top_le at H₁_codisjoint_H₂
--   rw [le_bot_iff, ← Submodule.zero_eq_bot] at H₁_disjoint_H₂
--   rw [top_le_iff] at H₁_codisjoint_H₂
--   -- by_cases exists_v_in_H₂ : ∃ v ∈ H₂, v ∉ LinearMap.ker (f - ξ₁ • 1)
--   -- obtain ⟨v₂, v₂_in_H₂, v₂_not_in_eigenspace_f_ξ₁⟩ := exists_v_in_H₂
--   -- have v₂_subset_H₂: {v₂} ⊆ (H₂ : Set (Fin 2 → F)) := by
--   --       intro v hv
--   --       rcases hv with ⟨rfl⟩
--   --       exact v₂_in_H₂
--   -- -- We now show v₂ generates H₂
--   -- have v₂_ne_zero : v₂ ≠ 0 := by
--   --   by_contra h
--   --   have v₂_in_eigenspace_f_ξ₁ : v₂ ∈ LinearMap.ker (f - ξ₁ • 1) := by rw [h]; exact Submodule.zero_mem _
--   --   contradiction
--   -- have v₂_not_in_H₁ : v₂ ∉ H₁ := by
--   --   intro v₂_in_H₁
--   --   have v₂_in_meet : v₂ ∈ H₁ ⊓ H₂ := Submodule.mem_inf.mpr ⟨v₂_in_H₁, v₂_in_H₂⟩
--   --   rw [H₁_disjoint_H₂, zero_eq_bot, Submodule.mem_bot] at v₂_in_meet
--   --   -- v₂ = 0  and v₂ ≠ 0, a contradiction
--   --   contradiction
--   have rank_nullity := rank_sup_add_rank_inf_eq H₁ H₂
--   rw [
--     H₁_disjoint_H₂, zero_eq_bot, rank_bot, add_zero, H₁_codisjoint_H₂, rank_top,
--     rank_H₁_eq_one_cardinal, rank_fin_fun
--   ] at rank_nullity
--   have rank_H₂_leq_one_cardinal : Module.rank F H₂ ≤ 1 := by
--     by_contra not_leq
--     simp at not_leq
--     have : (2 : Cardinal.{u}) < 2 :=
--       calc
--         2 = 1 + Module.rank F ↥H₂ := by apply rank_nullity
--         _ < 1 + 1 := by sorry--apply add_lt_add_left
--         _ = 2 := by rw [one_add_one_eq_two]
--     -- linarith should work :(
--     norm_num at this
--   have exists_generator_for_H₂ : ∃ v ∈ H₂, H₂ ≤ span F {v} := by rw [← rank_submodule_le_one_iff]; exact rank_H₂_leq_one_cardinal
--   obtain ⟨v₂, v₂_in_H₂, H₂_leq_span_v₂⟩ := exists_generator_for_H₂
--   have v₂_generates_H₂ : span F {v₂} = H₂ := by
--     ext w
--     constructor
--     · intro w_in_span_v₂
--       rw [LinearMap.span_singleton_eq_range] at w_in_span_v₂
--       obtain ⟨α, rfl⟩ := w_in_span_v₂
--       simp [smul_mem, v₂_in_H₂]
--     · intro w_in_H₂
--       exact H₂_leq_span_v₂ w_in_H₂
--       done
--   -- We show nilpotent part is either 0 or is zero every except the top right entry
--   by_cases h : (∃ v : Fin 2 → F, v ∉ LinearMap.ker n)
--   -- the nilpotent part, n is conjugate to [[0,0],[1,0]]
--   obtain ⟨v, hv⟩ := h
--   obtain ⟨m, hm⟩ := n_is_nilpotent
--   sorry
--   -- nilpotent part equals zero, n = 0, so f + n = f and so when changing basis
--   sorry


#check IsAlgClosed.exists_root

-- open Polynomial in
-- theorem theorem_1_5₃ [IsAlgClosed F] (S : SL(2,F)) : (∃ δ : Fˣ, @IsConj (GL (Fin 2) F) _ S (D δ)) ∨ (∃ τ : F, @IsConj (GL (Fin 2) F) _ S (T τ)) := by
--   --by brute force
--   let α : F := S.1 0 0
--   let β : F := S.1 0 1
--   let γ : F := S.1 1 0
--   let δ : F := S.1 1 1
--   have one_eq : 1 = α * δ - β * γ :=
--     calc 1 = det (S : Matrix (Fin 2) (Fin 2) F) := by rw [SpecialLinearGroup.det_coe]
--     _ = α * δ - β * γ := by simp_rw [Matrix.det_fin_two]
--   let P : F[X] := C β * X^2 + C (δ - α) * X + C γ
--   -- We split on the case where β, the top-left entry, is 0
--   by_cases hβ' : S.1 0 1 = 0
--   -- If β = 0 then det S = α * δ - β γ = α * δ = 1 which implies α = δ⁻¹
--   · have hβ : β = 0 := by simp_rw [β, hβ']
--     have : α * δ = 1 := by simp [hβ] at one_eq; exact one_eq.symm
--     sorry
--   -- If β ≠ 0 then after multiplying out the matrices we get a p
--   have deg_P_nonzero : degree P ≠ 0 := by
--     simp_rw [P]
--     rw [Polynomial.degree_quadratic hβ']
--     simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
--   rcases IsAlgClosed.exists_root P deg_P_nonzero with ⟨ξ, hξ⟩
--   sorry

open Polynomial

-- lemma SpecialLinearGroup.coe_coe ↑↑⟨!![0, 1; -1, 0], ⋯⟩
@[simp]
lemma GeneralLinearGroup.coe_mk' {R : Type*} [CommRing R] {M : Matrix (Fin 2) (Fin 2) R}
  (hM : Invertible (det M) ) : (GeneralLinearGroup.mk' M hM) = M := by rfl

lemma GeneralLinearGroup.coe_mk'_inv {R : Type*} [CommRing R] {M : Matrix (Fin 2) (Fin 2) R}
  {hM : Invertible (det M) } : (GeneralLinearGroup.mk' M hM)⁻¹ = M⁻¹ := by simp

lemma GL_eq_iff_Matrix_eq {n R : Type* } [Fintype n] [DecidableEq n] [CommRing R] { A B :  GL n R}
  (h : (A :  Matrix n n R) = (B : Matrix n n R) ) : A = B := by
  apply Matrix.GeneralLinearGroup.ext
  rw [← Matrix.ext_iff] at h
  exact h

lemma det_GL_coe_is_unit {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] (G : GL n R) :
  IsUnit (det (G : Matrix n n R)) := by
  have det_G_is_unit : IsUnit (GeneralLinearGroup.det G) := Group.isUnit (GeneralLinearGroup.det G)
  exact ⟨det_G_is_unit.unit, by simp only [IsUnit.unit_spec, GeneralLinearGroup.val_det_apply]⟩

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

lemma Matrix.fin_two_eq { R: Type*} [CommSemiring R] {M N : Matrix (Fin 2) (Fin 2) R}
  (h₀₀ : M 0 0 = N 0 0)(h₀₁ : M 0 1 = N 0 1)(h₁₀ : M 1 0 = N 1 0)(h₁₁ : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact h₀₀
  · exact h₀₁
  · exact h₁₀
  · exact h₁₁

lemma smul_one_of_minpoly_eq_X_sub_C { R : Type*} {n : ℕ} [ CommRing R ] [NoZeroDivisors R]
  {s : (Fin n → R) →ₗ[R] Fin n → R } {a : R} (hs : Associated (minpoly R s) (X - C a)) :
  s = a • 1 := by
  obtain ⟨unit, hunit⟩ := hs
  let Ξ := minpoly R s
    -- The minimal polynomial evaluated at M must be 0
  have s_eq_smul_one : aeval s Ξ = 0 := minpoly.aeval _ _
  have Ξ_eq : ∃ u_inv, IsUnit u_inv ∧ Ξ = (X - C a) * u_inv := ⟨unit.inv, by simp [← hunit]⟩
  -- We rearrange Ξ_eq to isolate Ξ and plug
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

def GeneralLinearGroup.T {F : Type*} [Field F] [DecidableEq F] (a b d : F) : GL (Fin 2) F :=
  if h : a * d ≠ 0
  then GeneralLinearGroup.mk' !![a, b; 0, d] (by simp; exact invertibleOfNonzero h)
  else 1

lemma bottom_left_entry_T_eq_zero {F : Type*} [Field F] [DecidableEq F] (a b d : F) :
  ((GeneralLinearGroup.T a b d) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
  simp_rw [GeneralLinearGroup.T]
  by_cases h : a * d ≠ 0
  · simp [h]
  · simp [h]

lemma exists_sqrt_discriminant {F : Type*} [Field F] [IsAlgClosed F] { a b c : F} :
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
lemma isConj_upper_triangular_iff {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
  {G : GL (Fin 2) F} :
  (∃ a b d, a* d ≠ 0 ∧ IsConj G (GeneralLinearGroup.T a b d)) ↔ ∃ c, (c * G * c⁻¹).1 1 0 = 0 := by
  constructor
  · rintro ⟨a, b, d, h⟩
    rw [isConj_iff] at h
    obtain ⟨_had, c, hc⟩ := h
    use c
    rw [hc]
    simp [bottom_left_entry_T_eq_zero]
  · rintro ⟨c, hc⟩
    rw [← upper_triangular_iff_bottom_left_entry_eq_zero] at hc
    obtain ⟨a, b, d, h⟩ := hc
    use a, b, d
    rw [isConj_iff]
    have det_is_unit := det_GL_coe_is_unit (c * G * c⁻¹)
    simp [← h] at det_is_unit
    constructor
    · simp [det_is_unit]
    · use c
      simp [GeneralLinearGroup.T, det_is_unit]
      apply GL_eq_iff_Matrix_eq
      rw [GeneralLinearGroup.coe_mk']
      exact h.symm

@[simp]
lemma  Matrix.special_inv_eq {F : Type*} [ Field F] {x : F} :
  !![1, 0; x, 1]⁻¹ = !![1, 0; - x, 1] := by simp [inv_def]

lemma Matrix.conj_special_eq {F : Type*} [Field F] {x : F} {a b c d : F} :
  !![1, 0; x, 1] * !![a, b; c, d] * !![1, 0; x, 1]⁻¹ =
  !![-b * x + a, b; (-b) * x * x + (a -d) * x + c, b*x + d] := by
  simp
  apply Matrix.fin_two_eq <;> ring_nf


theorem isTriangularizable_of_algClosed {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
  [NeZero (2 : F)] {G : GL (Fin 2) F} :
  ∃ a b d, a * d ≠ 0 ∧ IsConj G (GeneralLinearGroup.T a b d ) := by
  let α := G.1 0 0
  let β := G.1 0 1
  let γ := G.1 1 0
  let δ := G.1 1 1
  have G_coe_eq : (G : Matrix (Fin 2) (Fin 2) F) =  !![α, β; γ, δ] := by
      apply Matrix.fin_two_eq <;> rfl
  let a := - β
  let b := α - δ
  let c := γ
  rw [isConj_upper_triangular_iff]
  -- if β ≠ 0 then we solve the quadratic to force the bottom left entry to be 0
  by_cases hβ : β ≠ 0
  · obtain ⟨s, hs⟩ := exists_sqrt_discriminant (a := a) (b := b) (c := c)
    let x := (-b + s) / (2 * a)
    use GeneralLinearGroup.mk' !![1, 0; x, 1]
      (by rw [det_fin_two_of, mul_one, zero_mul, sub_zero]; exact invertibleOne)
    simp_rw [GeneralLinearGroup.coe_mul, G_coe_eq, GeneralLinearGroup.coe_mk',
      GeneralLinearGroup.coe_mk'_inv, Matrix.conj_special_eq]
    simp
    have ha : a ≠ 0 := by simp [hβ, a]
    rw [← neg_mul, ← neg_mul, mul_assoc, quadratic_eq_zero_iff ha hs.symm]
    left; rfl
  simp at hβ
  -- If β = 0 then we solve the linear polynomial if α - δ ≠ 0
  by_cases had : α - δ ≠ 0
  · let x := -γ / (α - δ)
    use GeneralLinearGroup.mk' !![1, 0; x, 1] (by simp; exact invertibleOne)
    simp_rw [GeneralLinearGroup.coe_mul, G_coe_eq, GeneralLinearGroup.coe_mk',
      GeneralLinearGroup.coe_mk'_inv, Matrix.conj_special_eq]
    field_simp [hβ, x]
    ring_nf
  -- If β = 0 and α = δ
  · use W.coeToGL
    simp [W, G_coe_eq]
    sorry

lemma upper_triangular_isConj_diagonal_of_nonzero_det {F : Type* } [DecidableEq F] [Field F]
  {a b d : F} (had : a - d ≠ 0 ) : IsConj !![a, b; 0, d] !![a, 0; 0, d] := by
  use GeneralLinearGroup.mk' !![1, b / (a - d); 0, 1] (by simp; exact invertibleOne)
  apply Matrix.fin_two_eq
  repeat' field_simp
  ring_nf

lemma upper_triangular_isConj_jordan {F : Type*} [Field F] {a b : F} (hb : b ≠ 0) :
  IsConj !![a, b; 0, a] !![a, 1; 0, a] := by
  use GeneralLinearGroup.mk' !![1 / b, 0; 0, 1]
    (by simp; apply invertibleOfNonzero <| inv_ne_zero hb)
  apply Matrix.fin_two_eq
  repeat' field_simp






lemma lin_map_eq_iff_matrix_eq { n R : Type* } [ Fintype n] [ DecidableEq n ] [CommRing R] { A B :  GL n R }(h : Matrix.toLin' (A : Matrix n n R) = Matrix.toLin' B ) : A = B := by
  apply Matrix.GeneralLinearGroup.ext
  rw [EmbeddingLike.apply_eq_iff_eq, ← Matrix.ext_iff] at h
  exact h

lemma Matrix.eq_of_apply_eq {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] {M N : Matrix n n R} (h : ∀ x : n → R, M *ᵥ x = N *ᵥ x) : M = N := by
  sorry


def GeneralLinearGroup.D { F : Type* } [DecidableEq F] [Field F] (a d : F) : GL (Fin 2) F :=
  if h : a * d ≠ 0 then (GeneralLinearGroup.mk' (diagonal (fun i => if i = 0 then a else d)) (by simp; exact invertibleOfNonzero h)) else 1

def GeneralLinearGroup.J { F : Type* } [DecidableEq F] [Field F] (a d : F) : GL (Fin 2) F :=
  if h : a * d ≠ 0 then GeneralLinearGroup.mk' !![(a : F), (1 : F); (0 : F), (d : F)] (by simp; exact invertibleOfNonzero h) else 1

-- lemma jordan_normal_expl_2 { F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F] { G : GL (Fin 2) F} : ∃ a d : F, a * d ≠ 0 ∧ (IsConj G (GeneralLinearGroup.D a d) ∨ IsConj G (GeneralLinearGroup.J a d ))  := by
--   let g := Matrix.toLin' (G : Matrix (Fin 2) (Fin 2) F)
--   have det_G_ne_zero : det (G : Matrix (Fin 2) (Fin 2) F) ≠ 0 := by sorry
--   have G_eq_g_toMatrix : (G : Matrix (Fin 2) (Fin 2) F) = LinearMap.toMatrix' g := by simp_rw [LinearMap.toMatrix'_toLin' _]
--   let χ := charpoly (G : Matrix (Fin 2) (Fin 2) F)
--   have χ_splits := IsAlgClosed.splits χ
--   have χ_ne_zero : χ ≠ 0 := Monic.ne_zero_of_ne (by simp) (charpoly_monic _)
--   have set_of_roots_eq := Polynomial.degree_eq_card_roots χ_ne_zero χ_splits
--   rw [splits_iff_exists_multiset] at χ_splits
--   obtain ⟨roots, hr⟩ := χ_splits
--   have lc_eq_one : χ.leadingCoeff = 1 := Polynomial.Monic.leadingCoeff $ Matrix.charpoly_monic _
--   simp [lc_eq_one] at hr
--   -- the degree of χ is 2
--   have deg_χ_eq_two : degree χ = 2 := Matrix.charpoly_degree_eq_dim _
--   have natDeg_χ_eq_two : natDegree χ = 2 := natDegree_eq_of_degree_eq_some deg_χ_eq_two
--   -- the multiset containing the roots of χ is 2
--   rw [deg_χ_eq_two] at set_of_roots_eq
--   have roots_eq := deg_χ_eq_two
--   rw [hr] at roots_eq
--   -- if the product of monics is of degree two then the multiset of roots is of size 2
--   simp only [degree_multiset_prod, Multiset.map_map, Function.comp_apply, degree_X_sub_C,
--     Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one] at roots_eq
--   norm_cast at roots_eq
--   -- if the size of the multiset is 2 then there must exist two elements in the multiset
--   -- these elements of the multiset are the eigenvalues
--   rw [Multiset.card_eq_two] at roots_eq
--   obtain ⟨ξ₁, ξ₂, hr'⟩ := roots_eq
--   simp [hr'] at hr
--   let Ξ := minpoly F (G : Matrix (Fin 2) (Fin 2) F)
--   have minpoly_dvd_charpoly : Ξ ∣ χ := Matrix.minpoly_dvd_charpoly _
--   have deg_Ξ: natDegree Ξ ≤ 2 := natDeg_χ_eq_two.symm ▸ natDegree_le_of_dvd minpoly_dvd_charpoly χ_ne_zero
--   rw [hr] at minpoly_dvd_charpoly
--   have Ξ_ne_zero : Ξ ≠ 0 := minpoly.ne_zero_of_finite _ _
--   -- degree of minpoly is either 1 or 2
--   let inst : EuclideanDomain F[X] := by infer_instance
--   have not_associated_to_unit : ¬ (∃ u : F[X], IsUnit u ∧ Associated Ξ u) := by
--     -- Suppose for a contradiction that they are associate
--     intro associated_to_unit
--     have Ξ_is_unit : IsUnit Ξ := by
--       obtain ⟨u, u_is_unit, associated_u_Ξ⟩ := associated_to_unit
--       apply Associated.isUnit associated_u_Ξ.symm u_is_unit
--     -- minpoly is not a unit, a contradiction
--     have Ξ_is_not_a_unit : ¬ IsUnit Ξ := minpoly.not_isUnit _ _
--     contradiction
--   have p₁_is_irreducible : Irreducible (X - C ξ₁) := irreducible_X_sub_C _
--   have p₂_is_irreducible : Irreducible (X - C ξ₂) := irreducible_X_sub_C _

--   -- Therefore, either Ξ is associate to (X - C ξ₁), (X - C ξ₂) or (X - C ξ₁) * (X - C ξ₂)
--   rcases (or_iff_right not_associated_to_unit).mp $ dvd_mul_of_irreducibles p₁_is_irreducible p₂_is_irreducible minpoly_dvd_charpoly
--     with (associate_to_p₁ | associate_to_p₂ | associate_to_χ)
--   -- Ξ is associate to (X - C ξ₁)
--   · have G_eq_diagonal : (G : Matrix (Fin 2) (Fin 2) F) = diagonal (fun _ ↦ ξ₁) := minpoly_eq_X_sub_C_implies_matrix_is_diagonal associate_to_p₁
--     have det_G_is_unit : IsUnit (det (G : Matrix (Fin 2) (Fin 2) F)) := by simp [det_G_ne_zero]
--     have ξ₁_ne_zero : ξ₁ ≠ 0 := by simp [G_eq_diagonal] at det_G_is_unit; simp [det_G_is_unit]
--     use ξ₁, ξ₁
--     constructor
--     · simp [ξ₁_ne_zero]
--     · left
--       rw [isConj_iff]
--       use 1
--       simp
--       ext
--       simp [G_eq_diagonal, GeneralLinearGroup.D, ξ₁_ne_zero, GeneralLinearGroup.toMatrix]
--   -- Ξ is associate to (X - C ξ₂)
--   · have G_eq_diagonal : (G : Matrix (Fin 2) (Fin 2) F) = diagonal (fun _ ↦ ξ₂) := minpoly_eq_X_sub_C_implies_matrix_is_diagonal associate_to_p₂
--     have det_G_is_unit : IsUnit (det (G : Matrix (Fin 2) (Fin 2) F)) := by simp [det_G_ne_zero]
--     have ξ₂_ne_zero : ξ₂ ≠ 0 := by simp [G_eq_diagonal] at det_G_is_unit; simp [det_G_is_unit]
--     use ξ₂, ξ₂
--     constructor
--     · simp [ξ₂_ne_zero]
--     · left
--       rw [isConj_iff]
--       use 1
--       simp
--       ext
--       simp [G_eq_diagonal, GeneralLinearGroup.D, ξ₂_ne_zero, GeneralLinearGroup.toMatrix]
--   -- Ξ is associate to (X - C ξ₁) * (X - C ξ₂)
--   · replace associate_to_χ := associate_to_χ.symm
--     rw [Associated] at associate_to_χ
--     obtain ⟨u, Ξ_eq⟩ := associate_to_χ
--     obtain ⟨u', u'_is_unit, C_u'_eq_u⟩ := Polynomial.isUnit_iff.mp u.isUnit
--     let Ξ' := minpoly F g
--     have aeval_G_eq_zero : aeval (G : Matrix (Fin 2) (Fin 2) F) Ξ = 0 := by apply minpoly.aeval
--     have coe_minpoly : Ξ' = Ξ := Matrix.minpoly_toLin' _
--     have ξ₁_is_root_of_Ξ' : IsRoot Ξ' ξ₁ := by simp_rw [coe_minpoly, ← Ξ_eq, IsRoot.def, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul]
--     have ξ₂_is_root_of_Ξ' : IsRoot Ξ' ξ₂ := by simp_rw [coe_minpoly, ← Ξ_eq, IsRoot.def, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, zero_mul]
--     rw [← Module.End.hasEigenvalue_iff_isRoot] at ξ₁_is_root_of_Ξ' ξ₂_is_root_of_Ξ'
--     by_cases hξ : ξ₁ ≠ ξ₂
--     · obtain ⟨v₁, hv₁⟩ := Module.End.HasEigenvalue.exists_hasEigenvector ξ₁_is_root_of_Ξ'
--       obtain ⟨v₂, hv₂⟩ := Module.End.HasEigenvalue.exists_hasEigenvector ξ₂_is_root_of_Ξ'
--       -- We define the set of eigenvalues
--       let e : Fin 2 → F := fun n => if n.val = 0 then ξ₁ else ξ₂
--       -- the eigenvalues are distinct
--       have he : Function.Injective e := by
--         intro i j hij
--         fin_cases i <;> fin_cases j
--         · rfl
--         · contradiction
--         · symm at hij; contradiction
--         · rfl
--       -- we define the eigenbasis
--       let b : Fin 2 → (Fin 2  → F) := fun n => if n.val = 0 then v₁ else v₂
--       -- the eigenvectors are linearly independent
--       have lin_ind : LinearIndependent F b := by
--         apply Module.End.eigenvectors_linearIndependent' g e he
--         intro i
--         fin_cases i <;> dsimp [e, b]
--         · exact hv₁
--         · exact hv₂
--       -- dimension of vector space equals 2, so the eigenbasis span the vector space
--       have card_eq : Fintype.card (Fin 2) = finrank F (Fin 2 → F) := by simp
--       -- the eigenvectors span the vector space and thus are a basis
--       let eigenbasis : Basis (Fin 2) F (Fin 2 → F) := basisOfLinearIndependentOfCardEqFinrank lin_ind card_eq
--       let std : Basis (Fin 2) F (Fin 2 → F) := Pi.basisFun F (Fin 2)
--       -- Change of basis from (e₁, e₂) to (v₁, v₂)
--       let eigenbasis_invertible := eigenbasis.invertibleToMatrix std
--       -- We show P⁻¹ * S * P = D ξ₁
--       have reindex : (eigenbasis.toMatrix ⇑std)⁻¹ = std.toMatrix eigenbasis := by
--         rw [Matrix.inv_eq_left_inv]
--         rw [Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]
--       let P' :=  eigenbasis.toMatrix (Pi.basisFun F (Fin 2))
--       have det_P_invertible : Invertible (det P') := by apply Matrix.detInvertibleOfInvertible
--       -- have det_P_is_unit : IsUnit (det P) := by apply isUnit_of_invertible
--       let P := Matrix.GeneralLinearGroup.mk' P' det_P_invertible
--       have P'_eq_coe_P : (P : Matrix (Fin 2) (Fin 2) F) = P' := rfl
--       have key : ∀ x : Fin 2 → F, (P * G * P⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ x = diagonal (fun i => if i = 0 then ξ₁ else ξ₂ ) *ᵥ  x := by
--         intro x
--         simp_rw [G_eq_g_toMatrix]
--         simp only [coe_units_inv, Fin.isValue, P]
--         simp_rw [GeneralLinearGroup.toMatrix, P', reindex, std]
--         rw [← eigenbasis.sum_repr x]
--         rw [← Matrix.mulVec_mulVec]
--         -- simp [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
--         rw [← Basis.linearCombination_repr eigenbasis x]
--         simp [Finsupp.linearCombination]
--         simp [Finsupp.sum]
--         simp [eigenbasis, b]
--         simp [LinearMap.codRestrict]
--         dsimp [lin_ind]
--         sorry
--         -- simp [Basis.smul_apply]
--         -- simp [LinearMap.toMatrix_mulVec_repr]
--       sorry
--     · -- if the eigenvalues are the same
--       -- the generalized eigenspace must span the whole vector space
--       simp at hξ
--       rw [hξ, ← sq] at Ξ_eq
--     -- The minimal polynomial evaluated at M must be 0
--       have aeval_minpoly : aeval (G : Matrix (Fin 2) (Fin 2) F) Ξ = 0 := minpoly.aeval _ _
--     -- We rearrange Ξ_eq to isolate Ξ and plug
--       have ringHom_u'_is_unit : IsUnit ((algebraMap F (Matrix (Fin 2) (Fin 2) F)) u') := RingHom.isUnit_map _ u'_is_unit
--       rw [← Ξ_eq, aeval_mul, ← C_u'_eq_u, aeval_C, IsUnit.mul_left_eq_zero ringHom_u'_is_unit] at aeval_minpoly
--       by_cases h : ∃ v, v ∉ LinearMap.ker (g - ξ₁ • 1)
--       · -- we get the generalized eigenvector
--         obtain ⟨v₁, hv₁⟩ := h
--         -- we use the generalized eigenvector to get the eigenvector
--         let v₂ := (g - ξ₁ • 1) v₁
--         have map_sq_eq_zero : (g - ξ₁ • 1)^2 = 0 := by
--           simp [G_eq_g_toMatrix, algebraMap, Algebra.toRingHom] at aeval_minpoly
--           sorry
--         have v₂_is_eigenvector : (g - ξ₁ • 1) v₂ = 0 := by
--           simp_rw [v₂, ← LinearMap.mul_apply, ← sq, map_sq_eq_zero, LinearMap.zero_apply]
--         sorry
--         -- Every vector is an eigenvector, this contradicts the minimal polynomial being a quadratic
--       · push_neg at h
--         have ker_eq_top : LinearMap.ker (g - ξ₁ • 1) = ⊤ := by
--           ext v; constructor
--           · intro _; simp
--           · intro hv; exact h v
--         rw [LinearMap.ker_eq_top] at ker_eq_top
--         have poly_annhilates_S : aeval (G : Matrix (Fin 2) (Fin 2) F) (X - C ξ₁)  = 0 := by
--           rw [sub_eq_zero] at ker_eq_top
--           rw [ker_eq_top] at G_eq_g_toMatrix
--           simp [G_eq_g_toMatrix, algebraMap, Algebra.toRingHom, smul_one_eq_diagonal]
--         have minpoly_is_minimal : Ξ ∣ (X - C ξ₁) := minpoly.dvd _ _ poly_annhilates_S
--         have contr : degree Ξ ≤ degree (X - C ξ₁) := by apply Polynomial.degree_le_of_dvd minpoly_is_minimal (X_sub_C_ne_zero _)
--         -- Contradiction, minpoly has greater degree than (X - C ξ₁) which is annhilated by S.
--         simp [degree_X_sub_C, ← Ξ_eq, degree_eq_zero_of_isUnit] at contr



-- represenation of vector in terms of basis vectors, for all x : Fin 2 → F, x =  c₁ • v₁ + c₂ • v₂ for some c₁, c₂ ∈ F



-- lemma Matrix.eq_iff_

-- two matrices are the same iff for all vectors x, M x = N x
-- lemma Matrix.eq_iff { n R : Type*} [Fintype n ] [ DecidableEq n] [CommRing R] {M N : Matrix n n R} : M = N ↔

-- If p is associated to q then there exists some unit u, such that p = u * q
-- lemma associated_iff {p q : F[X] }: Associated p q ↔ ∃ u, IsUnit u ∧ p = q * u := by
--   constructor
--   · intro hpq
--     obtain ⟨u, hu⟩ := hpq.symm
--     exact ⟨u, u.isUnit, hu.symm⟩
--   · rintro ⟨u, u_is_unit, hpq⟩
--     rw [Associated]

-- open Polynomial in
-- theorem theorem_1_5₄ [IsAlgClosed F] (S : SL(2,F)) : (∃ δ : Fˣ, IsConj (S.coeToGL) (D δ)) ∨ (∃ τ : F, IsConj (S.coeToGL) (T τ)) := by
--   -- let s := (Matrix.toLin (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) (S : Matrix (Fin 2) (Fin 2) F))
--   let s := Matrix.toLin' (S : Matrix (Fin 2) (Fin 2) F)
--   -- let χ' := LinearMap.charpoly s
--   let χ := charpoly (S : Matrix (Fin 2) (Fin 2) F)
--   have χ_splits := IsAlgClosed.splits χ
--   have χ_ne_zero : χ ≠ 0 := Monic.ne_zero_of_ne (by simp) (charpoly_monic _)
--   have set_of_roots_eq := Polynomial.degree_eq_card_roots χ_ne_zero χ_splits
--   rw [splits_iff_exists_multiset] at χ_splits
--   obtain ⟨roots, hr⟩ := χ_splits
--   have lc_eq_one : χ.leadingCoeff = 1 := Polynomial.Monic.leadingCoeff $ Matrix.charpoly_monic _
--   simp [lc_eq_one] at hr
--   -- the degree of χ is 2
--   have deg_χ_eq_two : degree χ = 2 := Matrix.charpoly_degree_eq_dim _
--   have natDeg_χ_eq_two : natDegree χ = 2 := natDegree_eq_of_degree_eq_some deg_χ_eq_two
--   -- the multiset containing the roots of χ is 2
--   rw [deg_χ_eq_two] at set_of_roots_eq
--   have roots_eq := deg_χ_eq_two
--   rw [hr] at roots_eq
--   -- if the product of monics is of degree two then the multiset of roots is of size 2
--   simp only [degree_multiset_prod, Multiset.map_map, Function.comp_apply, degree_X_sub_C,
--     Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one] at roots_eq
--   norm_cast at roots_eq
--   -- if the size of the multiset is 2 then there must exist two elements in the multiset
--   -- these elements of the multiset are the eigenvalues
--   rw [Multiset.card_eq_two] at roots_eq
--   obtain ⟨ξ₁, ξ₂, hr'⟩ := roots_eq
--   simp [hr'] at hr
--   let Ξ := minpoly F (S : Matrix (Fin 2) (Fin 2) F)
--   have minpoly_dvd_charpoly : Ξ ∣ χ := Matrix.minpoly_dvd_charpoly _
--   have deg_Ξ: natDegree Ξ ≤ 2 := natDeg_χ_eq_two.symm ▸ natDegree_le_of_dvd minpoly_dvd_charpoly χ_ne_zero
--   rw [hr] at minpoly_dvd_charpoly
--   have Ξ_ne_zero : Ξ ≠ 0 := minpoly.ne_zero_of_finite _ _
--   -- degree of minpoly is either 1 or 2
--   have not_associated_to_unit : ¬ (∃ u : F[X], IsUnit u ∧ Associated Ξ u) := by
--     -- Suppose for a contradiction that they are associate
--     intro associated_to_unit
--     have Ξ_is_unit : IsUnit Ξ := by
--       obtain ⟨u, u_is_unit, associated_u_Ξ⟩ := associated_to_unit
--       apply Associated.isUnit associated_u_Ξ.symm u_is_unit
--     -- minpoly is not a unit, a contradiction
--     have Ξ_is_not_a_unit : ¬ IsUnit Ξ := minpoly.not_isUnit _ _
--     contradiction
--   have p₁_is_irreducible : Irreducible (X - C ξ₁) := irreducible_X_sub_C _
--   have p₂_is_irreducible : Irreducible (X - C ξ₂) := irreducible_X_sub_C _
--   -- Therefore, either Ξ is associate to (X - C ξ₁), (X - C ξ₂) or (X - C ξ₁) * (X - C ξ₂)
--   rcases (or_iff_right not_associated_to_unit).mp $ dvd_mul_of_irreducibles p₁_is_irreducible p₂_is_irreducible minpoly_dvd_charpoly
--     with (associated_p₁ | associated_p₂ | associated_χ)
--   · -- We show matrix must be ± 1
--     -- First we show S is diagonal
--     have S_eq_diagonal : (S : Matrix (Fin 2) (Fin 2) F) = diagonal (fun _ ↦ ξ₁) := minpoly_eq_X_sub_C_implies_matrix_is_diagonal associated_p₁
--     have ξ₁_eq : det (S : Matrix (Fin 2) (Fin 2) F) = 1 := SpecialLinearGroup.det_coe S
--     -- Because S has determinant det S = ξ₁^2 = 1, either ξ₁ = 1 or ξ₂ = -1
--     simp [S_eq_diagonal, det_fin_two, ← sq] at ξ₁_eq
--     rcases ξ₁_eq with (ξ₁_eq_one | ξ₁_eq_minus_one)
--     · left
--       use 1, 1
--       simp [ξ₁_eq_one] at S_eq_diagonal
--       simp [SemiconjBy, S_eq_diagonal]
--       apply GL_eq_iff_Matrix_eq S_eq_diagonal
--     · left
--       use -1, 1
--       simp [ξ₁_eq_minus_one, ← Matrix.smul_one_eq_diagonal] at S_eq_diagonal
--       simp [SemiconjBy, S_eq_diagonal]
--       apply GL_eq_iff_Matrix_eq S_eq_diagonal
--   · -- We show the matrix must be ± 1
--     -- First we show S is diagonal
--     have S_eq_diagonal : (S : Matrix (Fin 2) (Fin 2) F) = diagonal (fun _ ↦ ξ₂) := minpoly_eq_X_sub_C_implies_matrix_is_diagonal associated_p₂
--     have ξ₂_eq : det (S : Matrix (Fin 2) (Fin 2) F) = 1 := SpecialLinearGroup.det_coe S
--     simp [S_eq_diagonal, det_fin_two, ← sq] at ξ₂_eq
--     rcases ξ₂_eq with (ξ₂_eq_one | ξ₂_eq_minus_one)
--     · left
--       use 1, 1
--       simp [ξ₂_eq_one] at S_eq_diagonal
--       simp [SemiconjBy, S_eq_diagonal]
--       apply GL_eq_iff_Matrix_eq S_eq_diagonal
--     · left
--       use -1, 1
--       simp [ξ₂_eq_minus_one, ← Matrix.smul_one_eq_diagonal] at S_eq_diagonal
--       simp [SemiconjBy]
--       apply GL_eq_iff_Matrix_eq S_eq_diagonal
--   · obtain ⟨u, hu⟩ := associated_χ
--     have Ξ_eq : ∃ u_inv, IsUnit u_inv ∧ Ξ = (X - C ξ₁) * (X - C ξ₂) * u_inv := ⟨u.inv, by simp [← hu]⟩
--     -- We rearrange Ξ_eq to isolate Ξ, then we substitute
--     obtain ⟨u_inv, u_inv_is_unit, Ξ_eq⟩ := Ξ_eq
--     obtain ⟨u_inv', u_inv'_is_unit, C_u_inv'_eq_u_inv⟩ := Polynomial.isUnit_iff.mp u_inv_is_unit
--     -- let s := (Matrix.toLin' (S : Matrix (Fin 2) (Fin 2) F))
--     let s := (Matrix.toLin (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) (S : Matrix (Fin 2) (Fin 2) F))
--     let Ξ' := minpoly F s
--     have coe : Ξ' = Ξ := Matrix.minpoly_toLin' _
--     have ξ₁_is_root_of_Ξ' : IsRoot Ξ' ξ₁ := by simp only [coe, Ξ_eq, IsRoot.def, eval_mul,
--       eval_sub, eval_X, eval_C, sub_self, zero_mul]
--     have ξ₂_is_root_of_Ξ' : IsRoot Ξ' ξ₂ := by simp [Ξ_eq, coe]
--     rw [← Module.End.hasEigenvalue_iff_isRoot] at ξ₁_is_root_of_Ξ' ξ₂_is_root_of_Ξ'
--     by_cases hξ : ξ₁ ≠ ξ₂
--     · left
--       obtain ⟨v₁, hv₁⟩ := Module.End.HasEigenvalue.exists_hasEigenvector ξ₁_is_root_of_Ξ'
--       obtain ⟨v₂, hv₂⟩ := Module.End.HasEigenvalue.exists_hasEigenvector ξ₂_is_root_of_Ξ'
--       -- we define the set of eigenvalues
--       let e : Fin 2 → F := fun n => if n.val = 0 then ξ₁ else ξ₂
--       -- the eigenvalues are distinct
--       have he : Function.Injective e := by
--         intro i j hij
--         fin_cases i <;> fin_cases j
--         · rfl
--         · contradiction
--         · symm at hij; contradiction
--         · rfl
--       -- we define the eigenbasis
--       let b : Fin 2 → (Fin 2  → F) := fun n => if n.val = 0 then v₁ else v₂
--       -- the eigenvectors are linearly independent
--       have lin_ind : LinearIndependent F b := by
--         apply Module.End.eigenvectors_linearIndependent' s e he
--         intro i
--         fin_cases i <;> dsimp [e, b]
--         · exact hv₁
--         · exact hv₂
--       -- dimension of vector space equals 2
--       have card_eq : Fintype.card (Fin 2) = finrank F (Fin 2 → F) := by simp
--       -- the eigenvectors span the vector space and thus are a basis
--       let eigenbasis : Basis (Fin 2) F (Fin 2 → F) := basisOfLinearIndependentOfCardEqFinrank lin_ind card_eq
--       -- Change of basis from (e₁, e₂) to (v₁, v₂)
--       let eigenbasis_invertible := eigenbasis.invertibleToMatrix (Pi.basisFun F (Fin 2))
--       -- We show P⁻¹ * S * P = D ξ₁
--       have reindex : (eigenbasis.toMatrix ⇑(Pi.basisFun F (Fin 2)))⁻¹ = (Pi.basisFun F (Fin 2)).toMatrix eigenbasis := by
--         rw [Matrix.inv_eq_left_inv]
--         simp [Matrix.inv_eq_left_inv, Basis.toMatrix_mul_toMatrix, Basis.toMatrix_self]
--       let P' :=  eigenbasis.toMatrix (Pi.basisFun F (Fin 2))
--       have det_P_invertible : Invertible (det P') := by apply Matrix.detInvertibleOfInvertible
--       -- have det_P_is_unit : IsUnit (det P) := by apply isUnit_of_invertible
--       let P := Matrix.GeneralLinearGroup.mk' P' det_P_invertible
--       have P'_eq_coe_P : (P : Matrix (Fin 2) (Fin 2) F) = P' := rfl
--       have S_as_linear_map : (S : Matrix (Fin 2) (Fin 2) F) = LinearMap.toMatrix (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) s := by simp only [LinearMap.toMatrix_toLin,
--         s]
--       have key : ∀ x : Fin 2 → F, (P * S * P⁻¹ : Matrix (Fin 2) (Fin 2) F) *ᵥ x = diagonal (fun i => if i = 0 then ξ₁ else ξ₂ ) *ᵥ  x := by
--         intro x
--         rw [S_as_linear_map]
--         simp [P]
--         simp_rw [GeneralLinearGroup.toMatrix, P', reindex]
--         simp [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
--         rw [← Basis.linearCombination_repr eigenbasis x]
--         simp [Finsupp.linearCombination]
--         simp [Finsupp.sum]
--         simp [eigenbasis]
--         simp [LinearMap.codRestrict]
--         dsimp [lin_ind]
--         sorry
--         -- simp [Basis.smul_apply]
--         -- simp [LinearMap.toMatrix_mulVec_repr]
--       sorry
--     · -- if the eigenvalues are the same
--       -- the generalized eigenspace must span the whole vector space
--       simp at hξ
--       rw [hξ, ← sq] at Ξ_eq
--     -- The minimal polynomial evaluated at M must be 0
--       have aeval_minpoly : aeval (S : Matrix (Fin 2) (Fin 2) F) Ξ = 0 := minpoly.aeval _ _
--     -- We rearrange Ξ_eq to isolate Ξ and plug
--       have ringHom_u_inv'_is_unit : IsUnit ((algebraMap F (Matrix (Fin 2) (Fin 2) F)) u_inv') := RingHom.isUnit_map _ u_inv'_is_unit
--       rw [Ξ_eq, aeval_mul, ← C_u_inv'_eq_u_inv, aeval_C, IsUnit.mul_left_eq_zero ringHom_u_inv'_is_unit] at aeval_minpoly
--       -- simp at genEigen_rank2
--       -- eigenvector of s
--       -- obtain ⟨v₁, hv₁⟩ := Module.End.HasEigenvalue.exists_hasEigenvector ξ₁_is_root_of_Ξ'
--       -- there exists a generalized eigenvector
--       have S_as_linear_map : (S : Matrix (Fin 2) (Fin 2) F) = LinearMap.toMatrix (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) s := by simp only [LinearMap.toMatrix_toLin, s]
--       by_cases h : ∃ v, v ∉ LinearMap.ker (s - ξ₁ • 1)
--       · -- we get the generalized eigenvector
--         obtain ⟨v₁, hv₁⟩ := h
--         -- we use the generalized eigenvector to get the eigenvector
--         let v₂ := (s - ξ₁ • 1) v₁
--         have map_sq_eq_zero : (s - ξ₁ • 1)^2 = 0 := by
--           simp [S_as_linear_map, algebraMap, Algebra.toRingHom] at aeval_minpoly
--           sorry
--         have v₂_is_eigenvector : (s - ξ₁ • 1) v₂ = 0 := by
--           simp_rw [v₂, ← LinearMap.mul_apply, ← sq, map_sq_eq_zero, LinearMap.zero_apply]
--         sorry
--         -- every vector is an eigenvector
--       · push_neg at h
--         have ker_eq_top : LinearMap.ker (s - ξ₁ • 1) = ⊤ := by
--           ext v; constructor
--           · intro _; simp
--           · intro hv; exact h v
--         rw [LinearMap.ker_eq_top] at ker_eq_top
--         have poly_annhilates_S : aeval (S : Matrix (Fin 2) (Fin 2) F) (X - C ξ₁)  = 0 := by
--           rw [sub_eq_zero] at ker_eq_top
--           rw [ker_eq_top] at S_as_linear_map
--           simp [S_as_linear_map, algebraMap, Algebra.toRingHom, smul_one_eq_diagonal]
--         have minpoly_is_minimal : Ξ ∣ (X - C ξ₁) := minpoly.dvd _ _ poly_annhilates_S
--         have contr : degree Ξ ≤ degree (X - C ξ₁) := by apply Polynomial.degree_le_of_dvd minpoly_is_minimal (X_sub_C_ne_zero _)
--         -- contradiction, minpoly has greater degree than (X - C ξ₁) which is annhilated by S.
--         simp [degree_X_sub_C, Ξ_eq, degree_eq_zero_of_isUnit u_inv_is_unit] at contr


-- open Polynomial in
-- theorem theorem_1_5₅ [IsAlgClosed F] (S : SL(2,F)) : (∃ δ : Fˣ, IsConj (S.coeToGL) (D δ)) ∨ (∃ τ : F, IsConj (S.coeToGL) (T τ)) := by
--   -- let s := (Matrix.toLin (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) (S : Matrix (Fin 2) (Fin 2) F))
--   let s := Matrix.toLin' (S : Matrix (Fin 2) (Fin 2) F)
--   have s_eq_S_toLin : s = Matrix.toLin' (S : Matrix (Fin 2) (Fin 2) F) := rfl
--   have S_eq_s_toMatrix : S = LinearMap.toMatrix' s := by simp [s]
--   -- let χ' := LinearMap.charpoly s
--   let χ := LinearMap.charpoly s
--   have χ_splits := IsAlgClosed.splits χ
--   have χ_ne_zero : χ ≠ 0 := Monic.ne_zero_of_ne (by simp) (charpoly_monic _)
--   have set_of_roots_eq := Polynomial.degree_eq_card_roots χ_ne_zero χ_splits
--   rw [splits_iff_exists_multiset] at χ_splits
--   obtain ⟨roots, hr⟩ := χ_splits
--   have lc_eq_one : χ.leadingCoeff = 1 := Polynomial.Monic.leadingCoeff $ Matrix.charpoly_monic _
--   simp [lc_eq_one] at hr
--   -- the degree of χ is 2
--   have finrank_eq_two : finrank F (Fin 2 → F) = 2 := by simp
--   have natDeg_χ_eq_two : natDegree χ = 2 := finrank_eq_two.symm ▸ LinearMap.charpoly_natDegree _
--   have deg_χ_eq_two : degree χ = (2 : ℕ) := by rw [degree_eq_iff_natDegree_eq χ_ne_zero]; exact natDeg_χ_eq_two
--   -- the multiset containing the roots of χ is 2
--   rw [deg_χ_eq_two ] at set_of_roots_eq
--   have roots_eq := deg_χ_eq_two
--   rw [hr] at roots_eq
--   -- if the product of monics is of degree two then the multiset of roots is of size 2
--   simp only [degree_multiset_prod, Multiset.map_map, Function.comp_apply, degree_X_sub_C,
--     Multiset.map_const', Multiset.sum_replicate, nsmul_eq_mul, mul_one] at roots_eq
--   norm_cast at roots_eq
--   -- if the size of the multiset is 2 then there must exist two elements in the multiset
--   -- these elements of the multiset are the eigenvalues
--   rw [Multiset.card_eq_two] at roots_eq
--   obtain ⟨ξ₁, ξ₂, hr'⟩ := roots_eq
--   simp [hr'] at hr
--   let Ξ := minpoly F s
--   have minpoly_dvd_charpoly : Ξ ∣ χ := LinearMap.minpoly_dvd_charpoly _
--   have deg_Ξ: natDegree Ξ ≤ 2 := natDeg_χ_eq_two.symm ▸ natDegree_le_of_dvd minpoly_dvd_charpoly χ_ne_zero
--   rw [hr] at minpoly_dvd_charpoly
--   have Ξ_ne_zero : Ξ ≠ 0 := minpoly.ne_zero_of_finite _ _
--   -- degree of minpoly is either 1 or 2
--   let inst : EuclideanDomain F[X] := by infer_instance
--   have not_associated_to_unit : ¬ (∃ u : F[X], IsUnit u ∧ Associated Ξ u) := by
--     -- Suppose for a contradiction that they are associate
--     intro associated_to_unit
--     have Ξ_is_unit : IsUnit Ξ := by
--       obtain ⟨u, u_is_unit, associated_u_Ξ⟩ := associated_to_unit
--       apply Associated.isUnit associated_u_Ξ.symm u_is_unit
--     -- minpoly is not a unit, a contradiction
--     have Ξ_is_not_a_unit : ¬ IsUnit Ξ := minpoly.not_isUnit _ _
--     contradiction
--   have p₁_is_irreducible : Irreducible (X - C ξ₁) := irreducible_X_sub_C _
--   have p₂_is_irreducible : Irreducible (X - C ξ₂) := irreducible_X_sub_C _
--   -- Therefore, either Ξ is associate to (X - C ξ₁), (X - C ξ₂) or (X - C ξ₁) * (X - C ξ₂)
--   rcases (or_iff_right not_associated_to_unit).mp $ dvd_mul_of_irreducibles p₁_is_irreducible p₂_is_irreducible minpoly_dvd_charpoly
--     with (associated_p₁ | associated_p₂ | associated_χ)
--   · -- We show matrix must be ± 1
--     -- First we show S is diagonal
--     have s_eq_smul_one : s = ξ₁ • 1 := smul_one_of_minpoly_eq_X_sub_C associated_p₁
--     have ξ₁_eq : LinearMap.det s = (1 : F) := by simp [s]
--     -- Because S has determinant det S = ξ₁^2 = 1, either ξ₁ = 1 or ξ₂ = -1
--     simp [s_eq_smul_one, det_fin_two, ← sq] at ξ₁_eq
--     rcases ξ₁_eq with (ξ₁_eq_one | ξ₁_eq_minus_one)
--     · left
--       use 1, 1
--       simp [ξ₁_eq_one] at s_eq_smul_one
--       simp [SemiconjBy, s_eq_smul_one]
--       apply lin_map_eq_iff_matrix_eq
--       -- rw [← s_eq_S_toLin]
--       sorry
--       -- apply GL_eq_iff_Matrix_eq s_eq_smul_one
--     · left
--       use -1, 1
--       simp [ξ₁_eq_minus_one, ← Matrix.smul_one_eq_diagonal] at s_eq_smul_one
--       simp [SemiconjBy, s_eq_smul_one]
--       -- apply GL_eq_iff_Matrix_eq s_eq_smul_one
--       sorry
--   · -- We show the matrix must be ± 1
--     -- First we show S is diagonal
--     sorry
--     -- have S_eq_diagonal : (S : Matrix (Fin 2) (Fin 2) F) = diagonal (fun _ ↦ ξ₂) := minpoly_eq_X_sub_C_implies_matrix_is_diagonal associated_p₂
--     -- have ξ₂_eq : det (S : Matrix (Fin 2) (Fin 2) F) = 1 := SpecialLinearGroup.det_coe S
--     -- simp [S_eq_diagonal, det_fin_two, ← sq] at ξ₂_eq
--     -- rcases ξ₂_eq with (ξ₂_eq_one | ξ₂_eq_minus_one)
--     -- · left
--     --   use 1, 1
--     --   simp [ξ₂_eq_one] at S_eq_diagonal
--     --   simp [SemiconjBy, S_eq_diagonal]
--     --   apply GL_eq_iff_Matrix_eq S_eq_diagonal
--     -- · left
--     --   use -1, 1
--     --   simp [ξ₂_eq_minus_one, ← Matrix.smul_one_eq_diagonal] at S_eq_diagonal
--     --   simp [SemiconjBy]
--     --   apply GL_eq_iff_Matrix_eq S_eq_diagonal
--   · obtain ⟨u, hu⟩ := associated_χ
--     have Ξ_eq : ∃ u_inv, IsUnit u_inv ∧ Ξ = (X - C ξ₁) * (X - C ξ₂) * u_inv := ⟨u.inv, by simp [← hu]⟩
--     -- We rearrange Ξ_eq to isolate Ξ, then we substitute
--     obtain ⟨u_inv, u_inv_is_unit, Ξ_eq⟩ := Ξ_eq
--     obtain ⟨u_inv', u_inv'_is_unit, C_u_inv'_eq_u_inv⟩ := Polynomial.isUnit_iff.mp u_inv_is_unit
--     -- let s := (Matrix.toLin' (S : Matrix (Fin 2) (Fin 2) F))
--     -- let s := (Matrix.toLin (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) (S : Matrix (Fin 2) (Fin 2) F))
--     -- let Ξ' := minpoly F s
--     -- have coe : Ξ' = Ξ := Matrix.minpoly_toLin' _
--     have ξ₁_is_root_of_Ξ : IsRoot Ξ ξ₁ := by simp [Ξ_eq]
--     have ξ₂_is_root_of_Ξ : IsRoot Ξ ξ₂ := by simp [Ξ_eq]
--     rw [← Module.End.hasEigenvalue_iff_isRoot] at ξ₁_is_root_of_Ξ ξ₂_is_root_of_Ξ
--     by_cases hξ : ξ₁ ≠ ξ₂
--     · left
--       obtain ⟨v₁, hv₁⟩ := Module.End.HasEigenvalue.exists_hasEigenvector ξ₁_is_root_of_Ξ
--       obtain ⟨v₂, hv₂⟩ := Module.End.HasEigenvalue.exists_hasEigenvector ξ₂_is_root_of_Ξ
--       -- we define the set of eigenvalues
--       let e : Fin 2 → F := fun n => if n.val = 0 then ξ₁ else ξ₂
--       -- the eigenvalues are distinct
--       have he : Function.Injective e := by
--         intro i j hij
--         fin_cases i <;> fin_cases j
--         · rfl
--         · contradiction
--         · symm at hij; contradiction
--         · rfl
--       -- we define the eigenbasis
--       let b : Fin 2 → (Fin 2  → F) := fun n => if n.val = 0 then v₁ else v₂
--       -- the eigenvectors are linearly independent
--       have lin_ind : LinearIndependent F b := by
--         apply Module.End.eigenvectors_linearIndependent' s e he
--         intro i
--         fin_cases i <;> dsimp [e, b]
--         · exact hv₁
--         · exact hv₂
--       -- dimension of vector space equals 2
--       have card_eq : Fintype.card (Fin 2) = finrank F (Fin 2 → F) := by simp
--       -- the eigenvectors span the vector space and thus are a basis
--       let eigenbasis : Basis (Fin 2) F (Fin 2 → F) := basisOfLinearIndependentOfCardEqFinrank lin_ind card_eq
--       -- Change of basis from (e₁, e₂) to (v₁, v₂)
--       let eigenbasis_invertible := eigenbasis.invertibleToMatrix (Pi.basisFun F (Fin 2))
--       -- We show P⁻¹ * S * P = D ξ₁
--       have ξ₁_is_unit : IsUnit ξ₁ := by sorry -- this is a stub
--       use IsUnit.unit ξ₁_is_unit
--       let P' :=  eigenbasis.toMatrix (Pi.basisFun F (Fin 2))
--       have det_P_invertible : Invertible (det P') := by apply Matrix.detInvertibleOfInvertible
--       -- have det_P_is_unit : IsUnit (det P) := by apply isUnit_of_invertible
--       let P := Matrix.GeneralLinearGroup.mk' P' det_P_invertible
--       -- have P_is_unit : IsUnit P := by rw [Matrix.isUnit_iff_isUnit_det]; apply det_P_is_unit
--       -- have S_as_linear_map : (S : Matrix (Fin 2) (Fin 2) F) = LinearMap.toMatrix (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) s := by simp [s]
--       -- rw [isConj_iff (S : Matrix (Fin 2) (Fin 2) F) _]
--       -- use (IsUnit.unit P_is_unit)⁻¹
--       simp
--       use P
--       have reindex : (eigenbasis.toMatrix ⇑(Pi.basisFun F (Fin 2)))⁻¹ = (Pi.basisFun F (Fin 2)).toMatrix eigenbasis := by sorry -- simp [Basis.toMatrix_mul_toMatrix_flip ]
--       -- coerce to Matrix
--       have key : (P * S * P⁻¹ : Matrix (Fin 2) (Fin 2) F) = ((D ξ₁_is_unit.unit) : Matrix (Fin 2) (Fin 2) F) := by
--         rw [S_eq_s_toMatrix]
--         simp [P]
--         simp_rw [GeneralLinearGroup.toMatrix, P', reindex]
--         -- simp [basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix]
--         -- apply Basis.ext
--         -- when applying
--         let std := Pi.basisFun F (Fin 2)
--         have v₁_repr_std := Basis.linearCombination_repr std v₁
--         have v₂_repr_std := Basis.linearCombination_repr std v₂
--         ext i j
--         rw [D_eq_diagonal]
--         sorry
--       -- have := Basis.invertibleToMatrix.proof_2 eigenbasis (Pi.basisFun F (Fin 2))
--       apply GL_eq_iff_Matrix_eq key
--     · -- if the eigenvalues are the same
--       -- the generalized eigenspace must span the whole vector space
--       simp at hξ
--       rw [hξ, ← sq] at Ξ_eq
--     -- The minimal polynomial evaluated at M must be 0
--       have aeval_minpoly : aeval s Ξ = 0 := minpoly.aeval _ _
--     -- We rearrange Ξ_eq to isolate Ξ and plug
--       have ringHom_u_inv'_is_unit : IsUnit ((algebraMap F (Matrix (Fin 2) (Fin 2) F)) u_inv') := RingHom.isUnit_map _ u_inv'_is_unit
--       rw [Ξ_eq, aeval_mul, ← C_u_inv'_eq_u_inv, aeval_C, IsUnit.mul_left_eq_zero ringHom_u_inv'_is_unit] at aeval_minpoly
--       -- simp at genEigen_rank2
--       -- eigenvector of s
--       -- obtain ⟨v₁, hv₁⟩ := Module.End.HasEigenvalue.exists_hasEigenvector ξ₁_is_root_of_Ξ'
--       -- there exists a generalized eigenvector
--       have S_as_linear_map : (S : Matrix (Fin 2) (Fin 2) F) = LinearMap.toMatrix (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) s := by simp [s]
--       by_cases h : ∃ v, v ∉ LinearMap.ker (s - ξ₁ • 1)
--       · -- we get the generalized eigenvector
--         obtain ⟨v₁, hv₁⟩ := h
--         -- we use the generalized eigenvector to get the eigenvector
--         let v₂ := (s - ξ₁ • 1) v₁
--         have map_sq_eq_zero : (s - ξ₁ • 1)^2 = 0 := by
--           simp [S_as_linear_map, algebraMap, Algebra.toRingHom] at aeval_minpoly
--           sorry
--         have v₂_is_eigenvector : (s - ξ₁ • 1) v₂ = 0 := by
--           simp_rw [v₂, ← LinearMap.mul_apply, ← sq, map_sq_eq_zero, LinearMap.zero_apply]
--         sorry
--         -- every vector is an eigenvector
--       · push_neg at h
--         have ker_eq_top : LinearMap.ker (s - ξ₁ • 1) = ⊤ := by
--           ext v; constructor
--           · intro _; simp
--           · intro hv; exact h v
--         rw [LinearMap.ker_eq_top] at ker_eq_top
--         have poly_annhilates_S : aeval (S : Matrix (Fin 2) (Fin 2) F) (X - C ξ₁)  = 0 := by
--           rw [sub_eq_zero] at ker_eq_top
--           rw [ker_eq_top] at S_as_linear_map
--           simp [S_as_linear_map, algebraMap, Algebra.toRingHom, smul_one_eq_diagonal]
--         have minpoly_is_minimal : Ξ ∣ (X - C ξ₁) := minpoly.dvd _ _ poly_annhilates_S
--         have contr : degree Ξ ≤ degree (X - C ξ₁) := by apply Polynomial.degree_le_of_dvd minpoly_is_minimal (X_sub_C_ne_zero _)
--         -- contradiction, minpoly has greater degree than (X - C ξ₁) which is annhilated by S.
--         simp [degree_X_sub_C, Ξ_eq, degree_eq_zero_of_isUnit u_inv_is_unit] at contr

#check Matrix.mulVec_stdBasis
#check LinearMap.toMatrix_mulVec_repr
#check Pi.single
#check Basis.repr
#check Basis.restrictScalars_toMatrix
#check minpoly.aeval
#check minpoly.unique
#check Basis.ext_elem
#check Basis.toMatrix_self
#check GeneralLinearGroup
#check IsUnit.mul_eq_one_iff_eq_inv
#check Basis.invertibleToMatrix.proof_2
#check LinearMap.toMatrix
#check Matrix.GeneralLinearGroup.mk'
#check Pi.basisFun
#check basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
#check basis_toMatrix_mul_linearMap_toMatrix
#check Basis.invertibleToMatrix
#check Matrix.toLinOfInv
#check rank_fin_fun
#check basisOfLinearIndependentOfCardEqFinrank
#check basis_toMatrix_mul_linearMap_toMatrix
#check Module.End.eigenvectors_linearIndependent'
#check Module.End.hasEigenvalue_of_isRoot










/- Proposition 1.6.i N_L(T₁) ⊆ H, where T₁ is any subgroup of T with order greater than 1. -/

/- Proposition 1.6.ii C_L(± T τ) = T × Z where τ ≠ 0 -/

/- Proposition 1.7. (i) N_L (D₁) = ⟨D, W⟩, where D₁ is any subgroup of D with order greater than 2.-/

/- Proposition 1.8. Let a and b be conjugate elements in a group G. Then ∃ x ∈ G such that xCG (a)x−1 = CG (b).-/
-- lemma proposition_1_8 { G : Type* } [Group G] (a b : G) (hab : IsConj a b) : ∃ x : G, ConjAct(centralizer { a }) = centralizer { b } := by sorry  :=

/- Corollary 1.9. The centraliser of an element x in L is abelian unless x belongs to the centre of L.-/
lemma corollary_1_9 (S : SL(2,F)) : x ∉ center SL(2,F) → IsCommutative (centralizer { S }) := by sorry
