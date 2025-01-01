import Mathlib

universe u

open Matrix MatrixGroups Subgroup Pointwise


variable
  (F : Type u) [Field F]
  (n : Type u) [Fintype n]
  (R : Type u) [CommRing R]
  (G : Type u) [Group G]

@[ext]
lemma Matrix.fin_two_ext { R: Type*} [CommSemiring R] {M N : Matrix (Fin 2) (Fin 2) R}
  (h₀₀ : M 0 0 = N 0 0)(h₀₁ : M 0 1 = N 0 1)(h₁₀ : M 1 0 = N 1 0)(h₁₁ : M 1 1 = N 1 1) : M = N := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

@[ext]
lemma SpecialLinearGroup.fin_two_ext (A B : SL(2,F))
    (h₀₀ : A.1 0 0 = B.1 0 0) (h₀₁ : A.1 0 1 = B.1 0 1) (h₁₀ : A.1 1 0 = B.1 1 0)
    (h₁₁ : A.1 1 1 = B.1 1 1) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

namespace SpecialMatrices

def t {F : Type*} [Field F] (τ : F): SL(2,F) :=
  ⟨!![1, 0; τ, 1], by simp⟩

@[simp]
lemma t_zero_eq_one : t (0 : F) = 1 := by ext <;> rfl

@[simp]
lemma t_inv (τ : F) : (t τ)⁻¹ = t (-τ) := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl, t]; rfl

@[simp]
lemma inv_neg_t_eq (τ : F) : (- t τ)⁻¹ = - t (-τ) := by
  simp [Matrix.SpecialLinearGroup.SL2_inv_expl]
  ext <;> simp [t]

@[simp]
lemma t_mul_t_eq_t_add (τ μ : F) : t τ * t μ = t (τ + μ) := by ext <;> simp [t]

end SpecialMatrices

open SpecialMatrices

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

def Z : Subgroup SL(2,F) := closure {(-1 : SL(2,F))}

def ZT : Subgroup SL(2,F) where
  carrier := { t τ | τ : F } ∪ { - t τ | τ : F }
  mul_mem' := by
    rintro x y (⟨τ₁, rfl⟩ | ⟨τ₁, rfl⟩) (⟨τ₂, rfl⟩ | ⟨τ₂, rfl⟩)
    repeat' simp
  one_mem' := by
    rw [← t_zero_eq_one]; left; use 0
  inv_mem' :=  by
    rintro x (⟨τ, rfl⟩ | ⟨τ, rfl⟩)
    repeat' simp


lemma closure_neg_one_eq : (closure {(-1 : SL(2,F))} : Set SL(2,F)) = {1, -1} := by
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
      -- instead of
      --
      sorry
  · intro hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with (rfl | rfl)
    · rw [SetLike.mem_coe, mem_closure_singleton]
      use 2
      apply Even.neg_one_zpow (by norm_num)
    · rw [SetLike.mem_coe]
      exact mem_closure_singleton_self (-1)

lemma Z_mul_T_subset_ZT :
  ((Z F) : Set SL(2,F)) * ((T F) : Set SL(2,F)) ⊆ ((ZT F) : Set SL(2,F)) := by
  rintro x ⟨z, hz, t', ht', hτ, h⟩
  obtain ⟨τ, rfl⟩ := ht'
  dsimp [Z] at hz
  dsimp
  rw [closure_neg_one_eq] at hz
  simp [ZT]
  rw [@Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with (rfl | rfl)
  left
  use τ
  rw [one_mul]
  right
  use τ
  rw [neg_mul, one_mul]

-- Given Z and T are normal subgroups with intersection Z ∩ T = {1}
-- ideally I would do
-- lemma Z_meet_T_eq_ZT' : (Z F ⊓ T F) = (Z F) * (T F) := by sorry


lemma Z_meet_T_eq_ZT : Z F ⊔ T F = ZT F := by
  ext x
  constructor
  · intro hx
    rw [@sup_eq_closure_mul] at hx
    rw [@mem_closure] at hx
    exact hx (ZT F) (Z_mul_T_subset_ZT F)
  · rintro (⟨τ, rfl⟩ | ⟨τ, rfl⟩) <;> rw [@sup_eq_closure_mul]
    · have mem_Z_mul_T : t τ ∈ ((Z F) : Set SL(2,F)) * (T F) := by
        rw [Set.mem_mul]
        use 1
        split_ands
        simp [Z, closure_neg_one_eq]
        use t τ
        split_ands <;> simp [T]
      apply Subgroup.subset_closure mem_Z_mul_T
    · have mem_Z_mul_T : -t τ ∈ ((Z F) : Set SL(2,F)) * (T F) := by
        rw [Set.mem_mul]
        use -1
        split_ands
        simp [Z, closure_neg_one_eq]
        use t τ
        split_ands <;> simp [T]
      apply Subgroup.subset_closure mem_Z_mul_T
