import Mathlib
import ClassificationOfSubgroups.SpecialMatrices

open Matrix MatrixGroups Subgroup Pointwise SpecialMatrices

universe u

variable
  (F : Type u) [Field F]
  (n : Type u) [Fintype n]
  (R : Type u) [CommRing R]
  {G : Type u} [Group G]

namespace SpecialSubgroups

section Diagonal

/- Lemma 1.2.1.1-/
def D (F : Type*) [Field F] : Subgroup SL(2,F) where
  carrier := { d δ | δ : Fˣ }
  mul_mem' := by
              intro S Q hS hQ
              simp at *
              obtain ⟨δS, hδS⟩ := hS
              obtain ⟨δQ, hδQ⟩ := hQ
              use δS * δQ
              rw [← hδS, ← hδQ]
              simp
  one_mem' := ⟨1, by simp⟩
  inv_mem' := by
              intro S
              simp
              intro δ hS
              use δ⁻¹
              simp [← hS]

end Diagonal

/- Lemma 1.2.1.2 -/
def T (F : Type*) [Field F]: Subgroup SL(2,F) where
  carrier := { t τ | τ : F }
  mul_mem' := by
              intro S Q hS hQ
              simp at *
              obtain ⟨τS, hτS⟩ := hS
              obtain ⟨τQ, hτQ⟩ := hQ
              use τS + τQ
              rw [← hτS, ← hτQ]
              simp
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
              rintro A₁ A₂ ⟨δ₁, τ₁, h₁⟩ ⟨δ₂, τ₂, h₂⟩
              use (δ₁ * δ₂), (τ₁*δ₂*δ₂ + τ₂)
              rw [← h₁, ← h₂]
              ext
              · simp [d, t]
              · simp [d, t]
              · field_simp [d, t]; ring
              · simp [d, t, mul_comm]
  one_mem' := ⟨1, 0, by simp⟩
  inv_mem' := by
              rintro A ⟨δ, τ, h⟩
              use δ⁻¹, -τ * δ⁻¹ * δ⁻¹
              rw [← h]
              simp [d_mul_t_eq_dt, Matrix.SpecialLinearGroup.SL2_inv_expl]
              ext <;> simp [dt]

lemma T_leq_H : T F ≤ H F := by
  rintro x ⟨τ, rfl⟩
  rw [H, mem_mk, Set.mem_setOf_eq]
  use 1, τ
  rw [d_one_eq_one, one_mul]

/- Lemma 1.2.2.1 T is a normal subgroup of H = D T -/
lemma T_normal_subgroupOf_H : ((T F).subgroupOf (H F)).Normal := by
  rw [← @normalizer_eq_top]
  ext x
  constructor
  · intro _hx
    exact mem_top _
  · intro hx
    rw [← @subgroupOf_self] at hx
    rw [@mem_subgroupOf] at hx
    obtain ⟨δ, τ, hx⟩ := hx
    rw [@mem_normalizer_iff'']
    intro t'
    constructor
    · rintro ⟨τ', hτ'⟩
      rw [mem_subgroupOf]
      dsimp at hτ' ⊢
      rw [← hx, ← hτ', _root_.mul_inv_rev, t_inv,
        inv_d_eq_d_inv, mul_assoc, mul_assoc (t (-τ)), ← mul_assoc (t τ'),
        ← mul_assoc (d δ⁻¹), ← mul_assoc (d δ⁻¹), d_eq_inv_d_inv F δ,
        d_mul_t_mul_d_inv_eq_t', t_mul_t_eq_t_add, t_mul_t_eq_t_add]
      rw [T, inv_inv, neg_add_cancel_comm_assoc, mem_mk, Set.mem_setOf_eq]
      use τ' * (δ : F) * (δ : F)
    · rintro ⟨τ', hτ'⟩
      rw [mem_subgroupOf]
      dsimp at hτ' ⊢
      have hτ : (t' : SL(2,F)) = (x : SL(2,F)) * t τ' * (x : SL(2,F))⁻¹ := by rw [hτ']; group
      rw [hτ, ← hx]
      rw [_root_.mul_inv_rev, t_inv, inv_d_eq_d_inv, mul_assoc (d δ), t_mul_t_eq_t_add,
         mul_assoc (d δ), ← mul_assoc (t (τ + τ')), t_mul_t_eq_t_add, ← mul_assoc,
         ← inv_d_eq_d_inv, d_mul_t_mul_d_inv_eq_t', add_neg_cancel_comm, Units.val_inv_eq_inv_val]
      use τ' * (δ : F)⁻¹ * (δ :F)⁻¹

def DW : Subgroup SL(2,F) where
  carrier := { d δ | δ : Fˣ} ∪ { d δ * w | δ : Fˣ}
  mul_mem' := by
    rintro x y (⟨δ₁, rfl⟩ | ⟨δ₁, rfl⟩) (⟨δ₂, rfl⟩ | ⟨δ₂, rfl⟩)
    · rw [d_mul_d_eq_d_mul]
      left
      use δ₁ * δ₂
    · rw [← mul_assoc, d_mul_d_eq_d_mul]
      right
      use δ₁ * δ₂
    · rw [mul_assoc, w_mul_d_eq_d_inv_w, inv_d_eq_d_inv, ← mul_assoc, d_mul_d_eq_d_mul]
      right
      use δ₁ * δ₂⁻¹
    · rw [mul_assoc, ← mul_assoc w, w_mul_d_eq_d_inv_w, mul_assoc _ w, w_mul_w_eq_neg_one,
       inv_d_eq_d_inv, ← mul_assoc, d_mul_d_eq_d_mul, mul_neg_one, neg_d_eq_d_neg]
      left
      use -(δ₁ * δ₂⁻¹)
  one_mem' := by left; rw [← d_one_eq_one]; use 1
  inv_mem' := by
    intro x h
    simp at h
    rcases h with (⟨δ, rfl⟩ | ⟨δ, rfl⟩)
    · simp
    · simp

lemma D_leq_DW : D F ≤ DW F := by
  rintro x ⟨δ, rfl⟩
  rw [DW, mem_mk, Set.mem_union, Set.mem_setOf_eq]
  left
  apply exists_apply_eq_apply


lemma Dw_leq_DW : (D F : Set SL(2,F)) * ({w} : Set SL(2,F)) ⊆ (DW F :  Set SL(2,F)) := by
  rintro x ⟨d', hd', w, hw, rfl⟩
  obtain ⟨δ, rfl⟩ := hd'
  rw [DW, coe_set_mk, Set.mem_union, Set.mem_setOf_eq]
  right
  use δ
  rw [Set.mem_singleton_iff] at hw
  rw [hw]

section Center

def Z : Subgroup SL(2,R) := closure {(-1 : SL(2,R))}

lemma get_entries (x : SL(2,F)) : ∃ α β γ δ,
  α = x.1 0 0 ∧ β = x.1 0 1 ∧ γ = x.1 1 0 ∧ δ = x.1 1 1 ∧
  (x : Matrix (Fin 2) (Fin 2) F) = !![α, β; γ, δ] := by
  use x.1 0 0, x.1 0 1, x.1 1 0, x.1 1 1
  split_ands
  repeat' rfl
  ext <;> rfl

lemma neg_one_mem_Z : (-1 : SL(2,F)) ∈ Z F := by simp [Z]

lemma closure_neg_one_eq : (closure {(-1 : SL(2,R))} : Set SL(2,R)) = {1, -1} := by
  ext x
  constructor
  · intro hx
    rw [← zpowers_eq_closure, SetLike.mem_coe, mem_zpowers_iff] at hx
    obtain ⟨k, rfl⟩ := hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    by_cases hk : Even k
    · left
      apply Even.neg_one_zpow hk
    · right;
      rw [Int.not_even_iff_odd] at hk
      -- simp [Odd.neg_pow_zpow hk (-1 : SL(2,F))]
      -- For some reason it picks the special case of the theorem for
      -- Even.neg_one_zpow.{u_2}
      -- {α : Type u_2} [DivisionMonoid α] [HasDistribNeg α] {n : ℤ} (h : Even n) : (-1) ^ n = 1

      sorry
  · intro hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (rfl | rfl)
    · rw [SetLike.mem_coe, mem_closure_singleton]
      use 2
      apply Even.neg_one_zpow (by norm_num)
    · rw [SetLike.mem_coe]
      exact mem_closure_singleton_self (-1)




@[simp]
lemma neg_one_neq_one_of_two_ne_zero [NeZero (2 : F)] : (1 : SL(2,F)) ≠ (-1 : SL(2,F)) := by
  intro h
  have neg_one_eq_one : (1 : SL(2,F)).1 0 0 = (-1 : SL(2,F)).1 0 0 := by nth_rewrite 1 [h]; rfl
  simp at neg_one_eq_one
  symm at neg_one_eq_one
  let inst : Nontrivial F := CommGroupWithZero.toNontrivial
  rw [neg_one_eq_one_iff] at neg_one_eq_one
  let inst : CharP F 2 := ringChar.eq_iff.mp neg_one_eq_one
  have two_eq_zero : (2 : F) = 0 := CharTwo.two_eq_zero
  have two_ne_zero : (2 : F) ≠ 0 := two_ne_zero
  contradiction

lemma Field.one_eq_neg_one_of_two_eq_zero (two_eq_zero : (2 : F) = 0) : 1 = (-1 : F) := by
  rw [← one_add_one_eq_two, add_eq_zero_iff_neg_eq'] at two_eq_zero
  exact two_eq_zero.symm


lemma SpecialLinearGroup.neg_one_eq_one_of_two_eq_zero (two_eq_zero : (2 : F) = 0) :
  1 = (-1 : SL(2,F)) := by
  ext
  <;> simp [Field.one_eq_neg_one_of_two_eq_zero]
  <;> exact Field.one_eq_neg_one_of_two_eq_zero F two_eq_zero



@[simp]
lemma set_Z_eq : (Z R : Set SL(2,R)) = {1, -1} := by
  dsimp [Z]
  rw [closure_neg_one_eq]

@[simp]
lemma Z_carrier_eq : (Z R).carrier = {1, -1} := by
  rw [← set_Z_eq]
  rfl

@[simp]
lemma mem_Z_iff {x : SL(2,R)}: x ∈ Z R ↔ x = 1 ∨ x = -1 := by
  rw [← mem_carrier, Z_carrier_eq, Set.mem_insert_iff, Set.mem_singleton_iff]

-- lemma foo : ↥(Z F) = {1, -1} := by sorry

instance : Finite (Z F) := by
  simp [← @SetLike.coe_sort_coe]
  exact Finite.Set.finite_insert 1 {-1}

lemma center_SL2_F_eq_Z {R : Type*}  [CommRing R] [NoZeroDivisors R]: center SL(2,R) = Z R := by
  ext x
  constructor
  · intro hx
    rw [SpecialLinearGroup.mem_center_iff] at hx
    obtain ⟨z, z_pow_two_eq_one, hz⟩ := hx
    simp at z_pow_two_eq_one hz ⊢
    rcases z_pow_two_eq_one with (rfl | rfl)
    · left
      ext <;> simp [← hz]
    · right
      ext <;> simp [← hz]
  · simp
    rintro (rfl | rfl) <;> simp [mem_center_iff]

instance : Finite (center SL(2,F)) := by
  rw [center_SL2_F_eq_Z]
  exact instFiniteSubtypeSpecialLinearGroupFinOfNatNatMemSubgroupZ F


lemma card_Z_eq_two_of_two_ne_zero [NeZero (2 : F)]: Nat.card (Z F) = 2 := by
  rw [@Nat.card_eq_two_iff]
  -- have neg_one_mem_Z : (-1 : SL(2,F)) ∈ Z F := by simp [Z]
  use 1, ⟨-1, neg_one_mem_Z F⟩
  split_ands
  · intro h
    rw [Subtype.ext_val_iff] at h
    -- -1 ≠ 1 for characteristic different to 2
    simp at h
  · rw [@Set.eq_univ_iff_forall]
    rintro ⟨z, hz⟩
    simp at hz
    rcases hz with (rfl | rfl) <;> simp

lemma card_Z_eq_one_of_two_eq_zero (two_eq_zero : (2 : F) = 0) : Nat.card (Z F) = 1 := by
  rw [@card_eq_one]
  ext x
  simp [(SpecialLinearGroup.neg_one_eq_one_of_two_eq_zero F two_eq_zero).symm]

lemma card_Z_le_two : Nat.card (Z F) ≤ 2 := by
  by_cases h : (2 : F) = 0
  · rw [card_Z_eq_one_of_two_eq_zero _ h]
    linarith
  · let inst : NeZero (2 : F) := { out := h }
    rw [card_Z_eq_two_of_two_ne_zero]


lemma orderOf_neg_one_eq_two [NeZero (2 : F)]: orderOf (-1 : SL(2,F)) = 2 := by
  have order_dvd_two : (orderOf (-1 : SL(2,F))) ∣ 2 ∧ 2 ≠ 0 := by
    split_ands
    rw [orderOf_dvd_iff_pow_eq_one ]; simp
    simp
  have order_neq_one : (orderOf (-1 : SL(2,F))) ≠ 1 := by
    simp only [ne_eq, orderOf_eq_one_iff]
    rw [← ne_eq]
    symm
    apply neg_one_neq_one_of_two_ne_zero
  rw [← Nat.mem_divisors, Nat.Prime.divisors Nat.prime_two, Finset.mem_insert] at order_dvd_two
  rcases order_dvd_two with (order_eq_one | order_eq_two)
  · contradiction
  · rw [Finset.mem_singleton] at order_eq_two
    exact order_eq_two

-- Lemma 1.4 If p ≠ 2, then SL(2,F) contains a unique element of order 2.
lemma exists_unique_orderOf_eq_two [NeZero (2 : F)] : ∃! x : SL(2,F), orderOf x = 2 := by
  use -1
  split_ands
  · exact orderOf_neg_one_eq_two F
  -- Now we show it is the unique element of order two
  intro x hx
  rcases get_entries F x with ⟨α, β, γ, _δ, _x_eq⟩
  simp [propext (orderOf_eq_iff (Nat.le.step Nat.le.refl))] at hx
  obtain ⟨hx₁, hx₂⟩ := hx
  rw [sq, mul_eq_one_iff_eq_inv'] at hx₁
  rw [SpecialLinearGroup.fin_two_ext_iff] at hx₁
  simp [adjugate_fin_two] at hx₁
  obtain ⟨α_eq_δ, β_eq_neg_β, γ_eq_neg_γ, -⟩ := hx₁
  rw [eq_neg_iff_add_eq_zero, ← two_mul] at β_eq_neg_β γ_eq_neg_γ
  have β_eq_zero : x.1 0 1 = 0 := eq_zero_of_ne_zero_of_mul_left_eq_zero two_ne_zero β_eq_neg_β
  have γ_eq_zero : x.1 1 0 = 0 := eq_zero_of_ne_zero_of_mul_left_eq_zero two_ne_zero γ_eq_neg_γ
  have det_x_eq_one : det (x : Matrix (Fin 2) (Fin 2) F) = 1 :=  by simp
  rw [det_fin_two, β_eq_zero, zero_mul, sub_zero, α_eq_δ, mul_self_eq_one_iff] at det_x_eq_one
  rcases det_x_eq_one with (δ_eq_one | δ_eq_neg_one )
  have α_eq_δ := α_eq_δ
  · rw [δ_eq_one] at α_eq_δ
    have x_eq_one : x = 1 := by ext <;> simp [α_eq_δ, β_eq_zero, γ_eq_zero, δ_eq_one]
    specialize hx₂ 1 (by norm_num) (by norm_num)
    rw [pow_one] at hx₂
    contradiction
  · rw [δ_eq_neg_one] at α_eq_δ
    ext <;> simp [α_eq_δ, β_eq_zero, γ_eq_zero, δ_eq_neg_one]

lemma Z_IsCyclic : IsCyclic (Z F) := by
  apply isCyclic_iff_exists_ofOrder_eq_natCard.mpr ?_
  by_cases h : NeZero (2 : F)
  · rw [card_Z_eq_two_of_two_ne_zero]
    use ⟨-1, neg_one_mem_Z F⟩
    simp
    exact orderOf_neg_one_eq_two F
  · have two_eq_zero : (2 : F) = 0 := by exact not_neZero.mp h
    rw [card_Z_eq_one_of_two_eq_zero F two_eq_zero]
    simp only [orderOf_eq_one_iff, exists_eq]



end Center

end SpecialSubgroups
