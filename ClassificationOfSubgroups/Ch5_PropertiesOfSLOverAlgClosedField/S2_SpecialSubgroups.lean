import ClassificationOfSubgroups.Ch5_PropertiesOfSLOverAlgClosedField.S1_SpecialMatrices
import Mathlib.Algebra.Category.Grp.Images
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.Order.CompletePartialOrder
import Mathlib.GroupTheory.Sylow


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



end Diagonal

section Shear

/- Lemma 1.2.1.2 -/
def T (F : Type*) [Field F] : Subgroup SL(2,F) where
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

end Shear



lemma D_meet_T_eq_bot {F : Type*} [Field F] : D F ⊓ T F = ⊥ := by
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
lemma T_normal_subgroupOf_H {F : Type*} [Field F] : ((T F).subgroupOf (H F)).Normal := by
  rw [← normalizer_eq_top_iff]
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


lemma Odd.neg_one_zpow {α : Type*} [Group α] [HasDistribNeg α] {n : ℤ} (h : Odd n) : (-1 : α) ^ n = -1 := by
  rw [← neg_eq_iff_eq_neg, ← neg_one_mul, Commute.neg_one_left, mul_zpow_self]
  exact Even.neg_one_zpow <| Odd.add_one h

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
      rw [Int.not_even_iff_odd, ] at hk
      exact Odd.neg_one_zpow hk
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
  simp [← SetLike.coe_sort_coe]
  exact Finite.Set.finite_insert 1 {-1}

lemma center_SL2_F_eq_Z (R : Type*)  [CommRing R] [NoZeroDivisors R]: center SL(2,R) = Z R := by
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
  rw [center_SL2_F_eq_Z F]
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

lemma IsCyclic_Z : IsCyclic (Z F) := by
  apply isCyclic_iff_exists_orderOf_eq_natCard.mpr ?_
  by_cases h : NeZero (2 : F)
  · rw [card_Z_eq_two_of_two_ne_zero]
    use ⟨-1, neg_one_mem_Z F⟩
    simp
    exact orderOf_neg_one_eq_two F
  · have two_eq_zero : (2 : F) = 0 := by exact not_neZero.mp h
    rw [card_Z_eq_one_of_two_eq_zero F two_eq_zero]
    simp only [orderOf_eq_one_iff, exists_eq]


namespace IsPGroup


/- Lemma 2.1. If G is a finite group of order pm where p is prime and m > 0,
then p divides |Z(G)|.-/
lemma p_dvd_card_center {H : Type*} {p : ℕ} (hp:  Nat.Prime p) [Group H] [Finite H] [Nontrivial H]
  (hH : IsPGroup p H) : p ∣ Nat.card (center H) := by
  let inst : Fact (Nat.Prime p) := by exact { out := hp }
  have card_H_eq_pow_prime : ∃ n > 0, Nat.card H = p ^ n := by rwa [← hH.nontrivial_iff_card]
  suffices ∃ k > 0, Nat.card (center H) = p ^ k by
    obtain ⟨k, kpos, hk⟩ := this
    use p^(k-1)
    rw [hk, ← Nat.pow_add_one', Nat.sub_add_cancel]
    linarith
  obtain ⟨n, npos, hn⟩ := card_H_eq_pow_prime
  exact IsPGroup.card_center_eq_prime_pow hn npos

end IsPGroup


end Center



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









section CommutativeSubgroups

lemma IsCommutative_iff {G : Type*} [Group G] (H : Subgroup G) :
  IsCommutative H ↔ ∀ x y : H, x * y = y * x := by
  constructor
  · intro h x y
    have := @mul_comm_of_mem_isCommutative G _ H h x y (by simp) (by simp)
    exact SetLike.coe_eq_coe.mp this
  · intro h
    rw [← le_centralizer_iff_isCommutative]
    intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    simp at hx
    specialize h ⟨x, hx⟩ ⟨y, hy⟩
    simp only [MulMemClass.mk_mul_mk, Subtype.mk.injEq] at h
    exact h

lemma IsCommutative_D : IsCommutative (D F) := by
  rw [IsCommutative_iff]
  rintro ⟨x, ⟨δ₁, hδ₁⟩⟩ ⟨y, ⟨δ₂, hδ₂⟩⟩
  simp [@Subtype.ext_val_iff]
  rw [← hδ₁, ← hδ₂]
  simp [mul_comm]


lemma IsCommutative_T : IsCommutative (T F) := by
  rw [IsCommutative_iff]
  rintro ⟨x, ⟨τ₁, hτ₁⟩⟩ ⟨y, ⟨τ₂, hτ₂⟩⟩
  simp [@Subtype.ext_val_iff]
  rw [← hτ₁, ← hτ₂]
  simp [add_comm]

lemma IsCommutative_TZ : IsCommutative (TZ F) := by
  refine le_centralizer_iff_isCommutative.mp ?_
  rintro x (⟨τ₁, rfl⟩ | ⟨τ₁, rfl⟩)
  repeat
  rw [mem_centralizer_iff]
  rintro y (⟨τ₂, rfl⟩ | ⟨τ₂, rfl⟩)
  repeat' simp [add_comm]

end CommutativeSubgroups

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

end SpecialSubgroups

#min_imports
