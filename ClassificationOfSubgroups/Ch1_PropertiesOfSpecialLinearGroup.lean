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

namespace SpecialMatrices
def T {F : Type*} [Field F] (τ : F): SL(2, F) :=
  ⟨!![1, 0; τ, 1], by norm_num⟩

@[simp]
lemma T_0_eq_one : T (0 : F) = 1 := by ext <;> rfl

def D {F : Type*} [Field F] (δ : Fˣ) : SL(2, F) :=
  ⟨!![(δ : F), (0 : F); (0 :F) , (δ⁻¹ : F)], by norm_num⟩

@[simp]
lemma D_1_eq_one : D (1 : Fˣ) = 1 := by ext <;> simp [D]

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
-- def subgroupGeneratedByD (F : Type*) [Field F] : Subgroup SL(2,F) where
--   carrier := { D δ | δ : Fˣ }
--   mul_mem' := by
--               intro S Q hS hQ
--               simp at *
--               obtain ⟨δS, hδS⟩ := hS
--               obtain ⟨δQ, hδQ⟩ := hQ
--               use δS * δQ
--               rw [← hδS, ← hδQ, lemma_1_1_i]
--   one_mem' := ⟨1, by simp⟩
--   inv_mem' := by
--               intro S
--               simp
--               intro δ hS
--               use δ⁻¹
--               simp [← hS]

/- Lemma 1.2.1.2 -/
-- def subgroupGeneratedByT (F : Type*)  [Field F] : Subgroup SL(2,F) where
--   carrier := { T τ | τ : F}
--   mul_mem' := by
--               intro S Q hS hQ
--               simp at *
--               obtain ⟨τS, hτS⟩ := hS
--               obtain ⟨τQ, hτQ⟩ := hQ
--               use τS + τQ
--               rw [← hτS, ← hτQ, lemma_1_1_ii]
--   one_mem' := ⟨0, by simp⟩
--   inv_mem' := by
--               intro S hS
--               simp at *
--               obtain ⟨τ, hτ⟩ := hS
--               use (-τ)
--               simp [← hτ]

-- def subgroupGeneratedByDT (F : Type*) [Field F] : Subgroup SL(2,F) where
--   carrier := { D δ * T τ | (δ : Fˣ) (τ : F) }
--   mul_mem' := by
--               intro A₁ A₂ hA₁ hA₂
--               obtain ⟨δ₁, τ₁, h₁⟩ := hA₁
--               obtain ⟨δ₂, τ₂, h₂⟩ := hA₂
--               dsimp
--               use (δ₁ * δ₂), (τ₁*δ₂*δ₂ + τ₂)
--               rw [← h₁, ← h₂]
--               ext <;> field_simp [D, T]; ring
--   one_mem' := ⟨1, 0, by simp⟩
--   inv_mem' := by
--               intro A hA
--               obtain ⟨δ, τ, h⟩ := hA
--               dsimp
--               use δ⁻¹, -τ * δ⁻¹ * δ⁻¹
--               rw [← h]
--               simp [D_mul_T_eq_DT, Matrix.SpecialLinearGroup.SL2_inv_expl]
--               ext <;> simp [DT]



/- Lemma 1.2.1.3 -/
-- def subgroupOfD_iso_units_of_F : subgroupGeneratedByD F ≃* Fˣ where
--   toFun D := ⟨
--               D.val 0 0,
--               D.val 1 1,
--               by obtain ⟨δ, hδ⟩ := D.property; rw [← hδ]; simp [SpecialMatrices.D],
--               by obtain ⟨δ, hδ⟩ := D.property; rw [← hδ]; simp [SpecialMatrices.D]
--               ⟩
--   invFun δ := ⟨D δ, by simp [subgroupGeneratedByD]⟩
--   left_inv A := by
--                 obtain ⟨δ, hδ⟩ := A.property
--                 rw [← Subtype.coe_inj, ← hδ]
--                 ext <;> simp [SpecialMatrices.D, ← hδ]
--   right_inv a := by ext; rfl
--   map_mul' X Y := by
--                 obtain ⟨δ₁, hδ₁⟩ := X.property
--                 obtain ⟨δ₂, hδ₂⟩ := Y.property
--                 simp only [Subgroup.coe_mul, Fin.isValue, SpecialLinearGroup.coe_mul]
--                 congr
--                 repeat'
--                   simp_rw [← hδ₁, ← hδ₂]
--                   simp [SpecialMatrices.D, mul_comm]

/- Lemma 1.2.1.4 { T τ } ≃* F -/
-- def subgroupOfT_iso_F {F : Type*} [Field F] : (subgroupGeneratedByT F) ≃* (Multiplicative F) where
--   toFun T := T.val 1 0
--   invFun τ := ⟨T τ, by simp [subgroupGeneratedByT]⟩
--   left_inv T := by
--                 obtain ⟨τ, hτ⟩ := T.property
--                 rw [← Subtype.coe_inj, ← hτ]
--                 ext <;> simp [SpecialMatrices.T, ← hτ]
--   right_inv τ := by simp [SpecialMatrices.T]
--   map_mul' X Y := by
--                   obtain ⟨τ₁, hτ₁⟩ := X.property
--                   obtain ⟨τ₂, hτ₂⟩ := Y.property
--                   simp only [Subgroup.coe_mul, Fin.isValue, SpecialLinearGroup.coe_mul]
--                   simp_rw [← hτ₁, ← hτ₂]
--                   simp [SpecialMatrices.T]
--                   rfl

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
--         have : ∀ k, (n^k) v = 0 := by
--           intro k
--           have hk := (Nat.zero_le k)
--           induction k using @Nat.decreasingInduction' (n := (m))
--           case h k' hk'₁ hk'₂ hk'₃  => sorry
--           case mn k' => exact le_refl k
--           case hP k' => sorry
--       sorry

-- example (b : ι → V) (b_indep : LinearIndependent K b)
--     (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) (i : ι) :
--     Basis.mk b_indep (fun v _ ↦ b_spans v) i = b i :=
--   Basis.mk_apply b_indep (fun v _ ↦ b_spans v) i
-- theorem Matrix2_is_nilpotent_iff_zero_or_upper_triangular {F : Type*} [Field F] (n : Module.End F (Fin 2 → F)) (hn : IsNilpotent n) : IsConj n 0 ∨ IsConj n !![0, 1; 0, 0] := by sorry
theorem theorem_1_5' [IsAlgClosed F] (S : SL(2,F)) : (∃ δ : Fˣ, @IsConj (GL (Fin 2) F) _ S (D δ)) ∨ (∃ τ : F, @IsConj (GL (Fin 2) F) _ S (T τ)) := by
  obtain ⟨ξ₁, hξ₁⟩ := by apply Module.End.exists_eigenvalue (Matrix.toLin (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) (S : Matrix (Fin 2) (Fin 2) F))
  obtain ⟨v₁, hv₁, v_ne_zero⟩ := by apply Module.End.HasEigenvalue.exists_hasEigenvector hξ₁
  sorry


#check Submodule.span_le
-- theorem helper (x y z w α β γ δ : F) [Field F] :
-- check [https://leanprover-community.github.io/mathematics_in_lean/C09_Linear_Algebra.html#matrices-bases-and-dimension]
#check IsAlgClosed.exists_root
/- Requires Jordan Normal Form -/
/- Lemma 1.5. Each element of SL(2,F) is conjugate to either D δ for some δ ∈ Fˣ, or to  ± T τ for some τ ∈ F .-/
open Polynomial in
theorem theorem_1_5 [IsAlgClosed F] (S : SL(2,F)) : (∃ δ : Fˣ, @IsConj (GL (Fin 2) F) _ S (D δ)) ∨ (∃ τ : F, @IsConj (GL (Fin 2) F) _ S (T τ)) := by
  let inst1 : PerfectField F := IsAlgClosed.perfectField F
  obtain ⟨n, hn, f, hf, n_is_nilpotent, f_is_semisimple, hfn⟩ := @Module.End.exists_isNilpotent_isSemisimple F ((Fin 2) → F) _ _ _ (@toEnd F _ S) _ _--((toLinAlgEquiv (Pi.basisFun F (Fin 2))) S)
  rw [← LinearMap.isNilpotent_toMatrix_iff (Pi.basisFun F (Fin 2))] at n_is_nilpotent
  rw [@Module.End.isSemisimple_iff] at f_is_semisimple
  -- We show nilpotent part is either 0 or is zero every excepty the top right entry
  by_cases h : (∃ v : Fin 2 → F, v ∉ LinearMap.ker n)
  obtain ⟨v, hv⟩ := h
  obtain ⟨m, hm⟩ := n_is_nilpotent
  -- Obtain eigenvalue, ξ₁ and eigenvector v₁
  obtain ⟨ξ₁, hξ₁⟩ := by apply Module.End.exists_eigenvalue f--(Matrix.toLin (Pi.basisFun F (Fin 2)) (Pi.basisFun F (Fin 2)) (S : Matrix (Fin 2) (Fin 2) F))
  obtain ⟨v₁, hv₁, v₁_ne_zero⟩ := by apply Module.End.HasEigenvalue.exists_hasEigenvector hξ₁
  -- Define the submodule generated by v₁
  let H₁ := Submodule.span F {v₁}
  have H₁_submodule_of_comap :  H₁ ≤ Submodule.comap f H₁:= by
    intro w hw
    simp [H₁, LinearMap.span_singleton_eq_range] at hw ⊢
    rw [Module.End.mem_unifEigenspace_one] at hv₁
    rcases hw with ⟨α, rfl⟩
    use α * ξ₁
    rw [LinearMap.map_smul, hv₁, smul_smul]
    done
  -- From Jordan-Chevallier obtain complementary submodule H₂
  obtain ⟨H₂, H₂_submodule_of_comap, H₁_is_compl_to_H₂⟩ := f_is_semisimple H₁ H₁_submodule_of_comap
  -- simp [H₁] at H₁_is_compl_to_H₂
  rcases H₁_is_compl_to_H₂ with ⟨H₁_disjoint_H₂, H₁_codisjoint_H₂⟩
  simp [H₁] at H₁_disjoint_H₂
  by_cases exists_v_in_H₂ : ∃ v ∈ H₂, v ∉ LinearMap.ker (f - ξ₁ • 1)
  obtain ⟨v₂, v₂_in_H₂, v₂_not_in_H₂⟩ := exists_v_in_H₂
  -- We now show v₂ generates H₂
  have v₂_generates_H₁ : H₂ = Submodule.span F {v₂} := by
    ext w
    constructor
    · intro hw
      sorry
    · intro hw
      have v₂_subset_H₂: {v₂} ⊆ (H₂ : Set (Fin 2 → F)) := by
        intro v hv
        rcases hv with ⟨rfl⟩
        exact v₂_in_H₂
      rw [Submodule.mem_span] at hw
      exact hw H₂ v₂_subset_H₂
  sorry
  -- Contradicition with disjointness
  sorry
  sorry




      -- simp [LinearMap.span_singleton_eq_range] at hw
      -- rcases hw with ⟨β, rfl⟩
      -- rw [Submodule.smul_mem_iff]
      -- exact v₂_in_H₂







  -- by brute force
  -- let α : F := S.1 0 0
  -- let β : F := S.1 0 1
  -- let γ : F := S.1 1 0
  -- let δ : F := S.1 1 1
  -- have one_eq : 1 = α * δ - β * γ :=
  --   calc 1 = det (S : Matrix (Fin 2) (Fin 2) F) := by rw [SpecialLinearGroup.det_coe]
  --   _ = α * δ - β * γ := by simp_rw [Matrix.det_fin_two]
  -- let P : F[X] := C β * X^2 + C (δ - α) * X + C γ
  -- -- We split on the case where β, the top-left entry, is 0
  -- by_cases hβ' : S.1 0 1 = 0
  -- -- If β = 0 then det S = α * δ - β γ = α * δ = 1 which implies α = δ⁻¹
  -- · have hβ : β = 0 := by simp_rw [β, hβ']
  --   have : α * δ = 1 := by simp [hβ] at one_eq; exact one_eq.symm
  --   sorry
  -- -- If β ≠ 0 then after multiplying out the matrices we get a p
  -- have deg_P_nonzero : degree P ≠ 0 := by
  --   simp_rw [P]
  --   rw [Polynomial.degree_quadratic hβ']
  --   simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true]
  -- rcases IsAlgClosed.exists_root P deg_P_nonzero with ⟨ξ, hξ⟩

/- Proposition 1.6.i N_L(T₁) ⊆ H, where T₁ is any subgroup of T with order greater than 1. -/

/- Proposition 1.6.ii C_L(± T τ) = T × Z where τ ≠ 0 -/

/- Proposition 1.7. (i) N_L (D₁) = ⟨D, W⟩, where D₁ is any subgroup of D with order greater than 2.-/

/- Proposition 1.8. Let a and b be conjugate elements in a group G. Then ∃ x ∈ G such that xCG (a)x−1 = CG (b).-/
-- lemma proposition_1_8 { G : Type* } [Group G] (a b : G) (hab : IsConj a b) : ∃ x : G, ConjAct(centralizer { a }) = centralizer { b } := by sorry  :=

/- Corollary 1.9. The centraliser of an element x in L is abelian unless x belongs to the centre of L.-/
lemma corollary_1_9 (S : SL(2,F)) : x ∉ center SL(2,F) → IsCommutative (centralizer { S }) := by sorry
