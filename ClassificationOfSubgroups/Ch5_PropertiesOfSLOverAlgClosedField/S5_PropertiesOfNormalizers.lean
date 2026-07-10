import ClassificationOfSubgroups.Ch5_PropertiesOfSLOverAlgClosedField.S3_JordanNormalFormOfSL

set_option autoImplicit false
set_option linter.style.longLine true

open Matrix MatrixGroups Subgroup

open SpecialMatrices SpecialSubgroups MatrixShapes

/-
Proposition 1.6.i
N_{SL(2,F)}(S₀) ⊆ L, where S₀ is any subgroup of S with order greater than 1.
-/
lemma normalizer_subgroup_S_le_L {F : Type*} [Field F] [DecidableEq F] { S₀ : Subgroup (SL(2,F)) }
 (hT₀ : 1 < Nat.card S₀ ) (h : S₀ ≤ S F) : normalizer S₀ ≤ L F := by
  intro x hx
  rw [mem_normalizer_iff] at hx
  by_cases h' : ∃ σ, σ ≠ 0 ∧ s σ ∈ S₀
  · obtain ⟨σ, σ_ne_zero, hσ⟩  := h'
    specialize hx (s σ)
    rw [hx] at hσ
    let α := x.1 0 0
    let β := x.1 0 1
    let γ := x.1 1 0
    let δ := x.1 1 1
    have x_eq : x = !![α, β; γ, δ] := by ext <;> rfl
    have : x * s σ * x⁻¹ ∈ S F := by exact h hσ
    obtain ⟨σ' , hσ'⟩ := this
    rw [SpecialSubgroups.mem_L_iff_lower_triangular]
    rw [lower_triangular_iff]
    have β_eq_zero : s σ' 0 1 = 0 := by simp [s]
    rw [hσ'] at β_eq_zero
    simp [x_eq, s] at β_eq_zero
    ring_nf at β_eq_zero
    rw [neg_eq_zero] at β_eq_zero
    apply eq_zero_of_ne_zero_of_mul_right_eq_zero σ_ne_zero at β_eq_zero
    rw [sq_eq_zero_iff] at β_eq_zero
    simp only [x_eq, EmbeddingLike.apply_eq_iff_eq, vecCons_inj, and_true, exists_and_left,
      ↓existsAndEq, exists_eq_left]
    exact β_eq_zero.symm
  · push_neg at h'
    have S₀_eq_bot : S₀ = ⊥ := by
      rw [eq_bot_iff_forall]
      intro x hx
      obtain ⟨σ, rfl⟩ := h hx
      specialize h' σ
      rw [not_imp_not] at h'
      specialize h' hx
      simp [h']
    have : Nat.card S₀ = 1 := by simp [S₀_eq_bot]
    -- contradiction with the assumption that Nat.card S₀ > 1
    linarith

lemma DW_le_normalizer_subgroup_D {F : Type*} [Field F] { D₀ : Subgroup (SL(2,F)) }
 (D₀_le_D : D₀ ≤ D F) : DW F ≤ normalizer D₀ := by
  intro x hx
  simp only [DW, mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_union,
    Set.mem_setOf_eq] at hx
  rcases hx with (hx | hx)
  · obtain ⟨δ, rfl⟩ := hx
    simp only [mem_normalizer_iff, inv_d_eq_d_inv]
    intro y
    constructor
    · intro y_mem_D₀
      have y_mem_D := D₀_le_D y_mem_D₀
      rw [mem_D_iff] at y_mem_D
      obtain ⟨δ₀, rfl⟩ := y_mem_D
      simpa
    · intro conj_mem_D₀
      obtain ⟨δ₀, hδ₀⟩ := D₀_le_D conj_mem_D₀
      have y_eq_conj : y = d δ * y * d δ⁻¹ := by
        suffices y = d δ₀ by simp [this]
        rw [← mul_left_inj (d δ⁻¹), ← mul_right_inj (d δ)]
        group at hδ₀ ⊢
        rw [← hδ₀]
        simp
      rwa [y_eq_conj]
  · obtain ⟨δ, rfl⟩ := hx
    rw [mem_normalizer_iff]
    intro y
    constructor
    · intro y_mem_D₀
      group
      nth_rewrite 1 [d_eq_inv_d_inv,  ← w_mul_d_eq_d_inv_w]
      rw [_root_.zpow_neg, _root_.zpow_neg, zpow_one, zpow_one,
        inv_w_eq_neg_w, mul_neg, neg_mul, inv_d_eq_d_inv,
        show -(w * d δ⁻¹ * y * w * d δ⁻¹) = -(w * d δ⁻¹ * y * (w * d δ⁻¹)) by group]
      nth_rewrite 2 [w_mul_d_eq_d_inv_w δ⁻¹]
      rw [← d_eq_inv_d_inv]
      obtain ⟨δ₀, rfl⟩ := D₀_le_D y_mem_D₀
      rw [show -(w * d δ⁻¹ * d δ₀ * (d δ * w)) = -(w * ((d δ⁻¹ * d δ₀) * d δ) * w) by group,
        d_mul_d_eq_d_mul, d_mul_d_eq_d_mul, inv_mul_cancel_comm,
        w_mul_d_eq_d_inv_w, inv_d_eq_d_inv]
      rw [show -(d δ₀⁻¹ * w * w) = -(d δ₀⁻¹ * (w * w)) by group, w_mul_w_eq_neg_one,
        mul_neg, mul_one, neg_d_eq_d_neg, neg_d_eq_d_neg, neg_neg, ← inv_d_eq_d_inv]
      exact Subgroup.inv_mem D₀ y_mem_D₀
    · intro conj_mem_D₀
      obtain ⟨δ₀, hδ₀⟩ := D₀_le_D conj_mem_D₀
      rw [eq_mul_inv_iff_mul_eq, ← inv_mul_eq_iff_eq_mul] at hδ₀
      rw [_root_.mul_inv_rev, inv_w_eq_neg_w, inv_d_eq_d_inv, ← mul_assoc (d δ₀),
        d_mul_d_eq_d_mul, mul_assoc, ← mul_assoc (d δ⁻¹), d_mul_d_eq_d_mul, ← mul_assoc δ⁻¹,
        inv_mul_cancel_comm, neg_mul, ← mul_assoc, w_mul_d_eq_d_inv_w, mul_assoc,
        w_mul_w_eq_neg_one, mul_neg_one, neg_neg, inv_d_eq_d_inv] at hδ₀
      rw [← hδ₀] at conj_mem_D₀ ⊢
      rw [mul_assoc, mul_assoc, ← mul_assoc w, w_mul_d_eq_d_inv_w,
        ← d_eq_inv_d_inv, _root_.mul_inv_rev, mul_assoc, ← mul_assoc w,
        mul_inv_cancel, one_mul, inv_d_eq_d_inv, d_mul_d_eq_d_mul,
          d_mul_d_eq_d_mul, ← mul_assoc, mul_inv_cancel_comm] at conj_mem_D₀
      rw [← inv_d_eq_d_inv]
      exact Subgroup.inv_mem D₀ conj_mem_D₀

lemma normalizer_subgroup_D_eq_DW_of_exists_noncentral {F : Type*} [Field F]
  {D₀ : Subgroup (SL(2,F))} (D₀_le_D : D₀ ≤ D F) (hD₀ : ∃ x ∈ D₀, x ∉ Z F) :
    normalizer D₀ ≤ DW F := by
  suffices ∃ δ : Fˣ, δ.val ≠ 1 ∧ δ.val ≠ -1 ∧ d δ ∈ D₀ by
    intro x hx
    rw [mem_normalizer_iff] at hx
    have ⟨δ', h₀, h₁, hδ'⟩ := this
    specialize hx (d δ')
    rw [hx] at hδ'
    have mem_D := D₀_le_D hδ'
    rw [mem_D_iff, ← SpecialLinearGroup.fin_two_diagonal_iff] at mem_D
    rcases get_entries x with ⟨α, β, γ, δ, hα, hβ, hγ, hδ, x_eq⟩
    rcases mem_D with ⟨top_right, bottom_left⟩
    simp [d, x_eq] at top_right bottom_left
    ring_nf at top_right bottom_left
    have top_right_eq :
      -(α * (δ' : F) * β) + α * β * (δ' : F)⁻¹ = α * β * ((↑δ')⁻¹ - ↑δ') := by ring
    have bottom_left_eq :
      (δ' : F) * γ * δ - (δ' : F)⁻¹ * γ * δ  = γ * δ * (↑δ' - (↑δ')⁻¹) := by ring
    replace top_right := top_right_eq ▸ top_right
    replace bottom_left := bottom_left_eq ▸ bottom_left
    have det_eq_one : det (x : Matrix (Fin 2) (Fin 2) F) = 1 := SpecialLinearGroup.det_coe _
    have δ_sub_δ_inv_ne_zero : (δ' : F)⁻¹ - δ' ≠ 0 := by
      intro h
      field_simp at h
      rw [mul_zero, sub_eq_zero] at h
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
    · apply Dw_le_DW
      rw [mem_D_w_iff, ← SpecialLinearGroup.fin_two_antidiagonal_iff]
      simp_rw [← hα, ← hδ, α_eq_zero, δ_eq_zero]
      trivial
    · apply D_le_DW
      rw [mem_D_iff, ← SpecialLinearGroup.fin_two_diagonal_iff]
      simp_rw [← hβ, ← hγ, β_eq_zero, γ_eq_zero]
      trivial
    · have det_eq_zero : det (x : Matrix (Fin 2) (Fin 2) F) = 0 := by
        rw [det_fin_two, ← hβ, ← hδ, β_eq_zero, δ_eq_zero, mul_zero, zero_mul, sub_zero]
      rw [det_eq_zero] at det_eq_one
      absurd zero_ne_one det_eq_one
      trivial
  obtain ⟨x, x_mem_D₀, hx⟩ := hD₀
  obtain ⟨δ, rfl⟩ := D₀_le_D x_mem_D₀
  rw [mem_Z_iff] at hx
  contrapose! hx
  specialize hx δ
  rw [show (δ.val ≠ 1 → δ.val ≠ -1 → d δ ∉ D₀)
    ↔ (δ.val = 1 ∨ δ.val = -1 ) by tauto] at hx
  rcases hx with (δ_eq_one | δ_eq_neg_one)
  · left
    ext <;> simp [d, δ_eq_one]
  · right
    ext <;> simp [d, δ_eq_neg_one]

/-
Proposition 1.7.
(i) N_L (D₀) = ⟨D, W⟩, where D₀ is any subgroup of D with order greater than 2.
-/
lemma normalizer_subgroup_D_eq_DW_of_two_lt_card {F : Type*} [Field F] {D₀ : Subgroup (SL(2,F))}
 (hD₀ : 2 < Nat.card D₀) (D₀_le_D : D₀ ≤ D F) : normalizer D₀ = DW F := by
  refine le_antisymm ?_ ?_
  · suffices ∃ x ∈ D₀, x ∉ Z F by
      apply normalizer_subgroup_D_eq_DW_of_exists_noncentral D₀_le_D this
    have ⟨δ', h₀, h₁, hδ'⟩ := ex_of_card_D_gt_two hD₀ D₀_le_D
    use d δ'
    split_ands
    · grind
    · simp only [mem_Z_iff, not_or]
      by_contra! h
      rw [show (d δ' ≠ 1 → d δ' = -1) ↔ (d δ' = 1 ∨ d δ' = -1) by tauto] at h
      rcases h with (h | h)
      · apply h₀
        simpa [← d_one_eq_one, d_eq_d_iff] using h
      · apply h₁
        rw [← d_neg_one_eq_neg_one, d_eq_d_iff] at h
        rw [h]; simp
  · exact DW_le_normalizer_subgroup_D D₀_le_D

instance {G : Type*} [GroupWithZero G] [hG : Infinite G] : Infinite Gˣ := by
  let units_equiv : (Set.univ : Set Gˣ) ≃ Units.val '' Set.univ :=
    Equiv.Set.image Units.val Set.univ (@Units.val_injective G _)
  have units_ne_zero : Units.val '' Set.univ = Set.univ \ {(0 : G)} := by
    ext x
    constructor
    · grind [Units.ne_zero]
    · intro hx
      exists Units.mk0 x (by simpa using hx.right)
  rw [← Set.infinite_univ_iff, ← Set.infinite_coe_iff,
        Equiv.infinite_iff (units_equiv), Set.infinite_coe_iff,
        units_ne_zero]
  exact Set.Infinite.diff (Set.infinite_univ_iff.mpr hG) (Set.finite_singleton 0)


lemma normalizer_D_eq_DW {F : Type*} [Field F] [IsAlgClosed F] :
    normalizer (D F) = DW F := by
  refine le_antisymm ?_ ?_
  · let infinite_F : Infinite F := IsAlgClosed.instInfinite
    let infinite_F_units : Infinite Fˣ := inferInstance
    let D_infinite : Infinite (D F) := Infinite.of_injective
      (D_mulEquiv_units F).symm.toMonoidHom.toFun
      (by simp [MulEquiv.injective (D_mulEquiv_units F).symm])
    let fintype_Z : Fintype (Z F) := Fintype.ofFinite ↥(Z F)
    obtain ⟨x, hx, hx'⟩ := Set.Infinite.exists_notMem_finset
      (Set.infinite_coe_iff.mp D_infinite) (Z F).carrier.toFinset
    refine normalizer_subgroup_D_eq_DW_of_exists_noncentral (le_refl _) ?_
    use x, hx
    simpa using hx'
  · exact DW_le_normalizer_subgroup_D (le_refl _)
