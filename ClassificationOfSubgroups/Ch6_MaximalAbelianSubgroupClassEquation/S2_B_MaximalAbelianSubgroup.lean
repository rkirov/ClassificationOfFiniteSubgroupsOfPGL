import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_A_MaximalAbelianSubgroup

open MaximalAbelianSubgroup Subgroup MulAction MulAut Pointwise
  Function SpecialSubgroups SpecialMatrices

open scoped MatrixGroups

#check map_normalizer_subgroupOf_eq_normalizer_conj_subgroupOf

#check normalizer_inf_le_eq_normalizer_subgroupOf

-- Restated with the hypothesis that `A'` has index 2 in `N(A') ⊓ G'`, matching the
-- "[N_G(A) : A] = 2" situation of Butler Thm 6.8(iv-b) (tex ~889-891): the original
-- statement (with no index hypothesis at all) is false, since e.g. `A' = G' ⊓ D F = G'`
-- gives `N(A') ⊓ G' = G' = A'`, an empty difference. This lemma is not otherwise used in
-- the file; the main theorem `of_index_normalizer_eq_two` reproves the needed nonemptiness
-- directly via `monoidHom_normalizer_D_quot_D`.
lemma Nonempty_normalizer_A'_inf_G_diff_A' {F : Type*} [Field F] (A' G' : Subgroup SL(2,F))
  (hA' : A' ∈ MaximalAbelianSubgroupsOf G') (A'_le_D : A' ≤ D F)
  (hNA' : relIndex A' ((normalizer ((A') : Set SL(2,F))) ⊓ G') = 2) :
    Set.Nonempty (((normalizer ((A') : Set SL(2,F))) ⊓ G').carrier \ A') := by
  by_contra! h
  rw [Set.diff_eq_empty] at h
  have := relIndex_eq_one.mpr h
  rw [hNA'] at this
  norm_num at this
-- Extracted as a standalone lemma (rather than inlined into `of_index_normalizer_eq_two`) so
-- that the `MulEquiv`/`aesop` bookkeeping below type-checks in a lean local context: inlined
-- into the big theorem (with `f`, `key`, `Injective_f`, etc. all in scope) the final `aesop`
-- call was hitting `isDefEq` heartbeat timeouts purely due to the size of the ambient context,
-- even though the very same proof succeeds instantly in isolation.
lemma bijective_monoidHom_normalizer_D_quot_D {F : Type*} [Field F] [IsAlgClosed F]
    (A' G' : Subgroup SL(2,F)) (A'_le_D : A' ≤ D F) (A'_le_G' : A' ≤ G')
    (two_lt_card_A' : 2 < Nat.card A') (A'_eq_G'_inf_D : A' = G' ⊓ D F)
    (hNA' : Nat.card (normalizer ((A'.subgroupOf G') : Set ↥G')
        ⧸ (A'.subgroupOf G').subgroupOf (normalizer ((A'.subgroupOf G') : Set ↥G'))) = 2) :
    Bijective (monoidHom_normalizer_D_quot_D A' G') := by
  haveI : Finite (↥(normalizer ((D F) : Set SL(2,F)))
      ⧸ (D F).subgroupOf (normalizer ((D F) : Set SL(2,F)))) :=
    Nat.finite_of_card_ne_zero (by rw [card_normalizer_D_quot_D_eq_two]; norm_num)
  -- reconstruct the chain of `MulEquiv`s used to build `f` in
  -- `subgroupOf_normalizer_quot_monoidHom_ZMod_two`, to transport the known
  -- cardinality (`2`) of `f`'s domain across to the domain of
  -- `monoidHom_normalizer_D_quot_D A' G'`.
  let φ1 := normalizer_quot_mulEquiv_quot_of A' G' A'_le_D A'_le_G' two_lt_card_A'
    A'_eq_G'_inf_D
  let φ2 := QuotientGroup.quotientInfEquivProdNormalQuotient
    (H := (((normalizer ((A') : Set SL(2,F))) ⊓ G').subgroupOf
      (normalizer ((D F) : Set SL(2,F)))))
    (N := (D F).subgroupOf (normalizer ((D F) : Set SL(2,F))))
  let φ3eq := (MulEquiv.subgroupCongr
    (G := (normalizer ((D F) : Set SL(2,F))))
    (H := ((normalizer ((A') : Set SL(2,F))) ⊓ G').subgroupOf
      (normalizer ((D F) : Set SL(2,F))) ⊔ (D F).subgroupOf
        (normalizer ((D F) : Set SL(2,F))))
    (K := ((normalizer ((A') : Set SL(2,F))) ⊓ G' ⊔ D F).subgroupOf
      (normalizer ((D F) : Set SL(2,F))))
    (by rw [subgroupOf_sup
    (by rw [normalizer_D_eq_DW, normalizer_subgroup_D_eq_DW_of_two_lt_card two_lt_card_A'
          A'_le_D]
        exact inf_le_left)
    (le_normalizer)])).symm
  let φ3 := QuotientGroup.congr _ _ φ3eq
    (show Subgroup.map φ3eq.toMonoidHom (((D F).subgroupOf
        (normalizer ((D F) : Set SL(2,F)))).subgroupOf
       (((normalizer ((A') : Set SL(2,F))) ⊓ G' ⊔ D F).subgroupOf
         (normalizer ((D F) : Set SL(2,F)))))
    = ((D F).subgroupOf (normalizer ((D F) : Set SL(2,F)))).subgroupOf
        (((normalizer ((A') : Set SL(2,F))) ⊓ G').subgroupOf
          (normalizer ((D F) : Set SL(2,F))) ⊔ (D F).subgroupOf
            (normalizer ((D F) : Set SL(2,F)))) by
    dsimp [φ3eq]
    ext x; constructor
    · intro hx
      rw [mem_map] at hx
      obtain ⟨y, y_mem_subgroupOf, hy⟩ := hx
      rw [← hy]
      rw [mem_subgroupOf, mem_subgroupOf] at y_mem_subgroupOf ⊢
      simp [y_mem_subgroupOf]
    · intro hx
      rw [mem_map]
      use ⟨
        x.val,
        by
        rw [mem_subgroupOf, mem_subgroupOf] at hx
        rw [mem_subgroupOf]
        suffices D F ≤ (normalizer ((A') : Set SL(2,F))) ⊓ G' ⊔ D F by
          apply this hx
        apply le_sup_right
        ⟩
      constructor
      · rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
        simp [hx]
      · aesop)
  let L := φ1.trans (φ2.trans φ3.symm)
  have hcard : Nat.card (((normalizer ((A') : Set SL(2,F))) ⊓ G' ⊔ D F).subgroupOf
      (normalizer ((D F) : Set SL(2,F)))
      ⧸ ((D F).subgroupOf (normalizer ((D F) : Set SL(2,F)))).subgroupOf
        (((normalizer ((A') : Set SL(2,F))) ⊓ G' ⊔ D F).subgroupOf
          (normalizer ((D F) : Set SL(2,F))))) = 2 := by
    rw [← Nat.card_congr L.toEquiv, hNA']
  refine (Nat.bijective_iff_injective_and_card _).mpr ⟨?_, ?_⟩
  · dsimp [monoidHom_normalizer_D_quot_D]
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    obtain ⟨x', hx'⟩ := Quotient.exists_rep x
    simp [MonoidHom.mem_ker, ← hx', QuotientGroup.eq_one_iff] at hx
    simpa [mem_bot, ← hx', mem_subgroupOf]
  · rw [hcard, card_normalizer_D_quot_D_eq_two]

/-
Theorem 2.3 (iv b) Furthermore, if [NG (A) : A] = 2,
then there is an element y of NG (A)\A such that, yxy⁻¹ = x⁻¹  for all x ∈ A.
 -/
theorem of_index_normalizer_eq_two {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  {p : ℕ} [Fact (Nat.Prime p)] [CharP F p] (p_ne_two : p ≠ 2) (A G : Subgroup SL(2,F))
  [Finite G] (hA : A ∈ MaximalAbelianSubgroupsOf G) (center_le_G : center SL(2,F) ≤ G)
  (hA' : Nat.Coprime (Nat.card A) p)
  (hNA : relIndex (A.subgroupOf G) (normalizer ((A.subgroupOf G) : Set ↥G)) = 2) (x : A) :
    ∃ y ∈ ((normalizer ((A) : Set SL(2,F))) ⊓ G).carrier \ A, y * x * y⁻¹ = x⁻¹ := by
  have two_lt_card_A : 2 < Nat.card A := by
    have key := relIndex_eq_one_of_card_le_two p_ne_two A G center_le_G hA
    contrapose! key
    constructor
    · exact key
    · rw [hNA]
      norm_num
  have G_ne_center : G ≠ center SL(2,F) := G_ne_center_of_two_lt_card A G hA two_lt_card_A

  rcases isCyclic_and_card_coprime_charP_or_eq_Q_sup_Z_of_center_ne p G A hA
      center_le_G G_ne_center with (⟨⟨c, A', Finite_A', A'_le_D, A_eq_conj_A'⟩, -⟩ | h)
  · let G' := conj c⁻¹ • G
    have G_eq_conj_G' : G = conj c • G' := by simp [G']
    have hA' : A' ∈ MaximalAbelianSubgroupsOf G' := by
      rw [mem_iff_conj_smul_mem_MaximalAbelianSubgroupsOf_conj_smul A' G' c,
        ← A_eq_conj_A', ← G_eq_conj_G']
      exact hA
    rw [relIndex,
      ← relIndex_MaximalAbelianSubgroupOf_normalizer_eq_relIndex_conj_MaxAbelianSubgroupOf
      A_eq_conj_A' G_eq_conj_G'] at hNA
    have two_lt_card_A' : 2 < Nat.card A' := by rwa [card_conj_eq_card A_eq_conj_A']
    have A'_eq_G'_inf_D : A' = G' ⊓ D F := eq_G_inf_D_of_le_D A' G' A'_le_D hA'

    let f := subgroupOf_normalizer_quot_monoidHom_ZMod_two
      A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D
    have Injective_f : Injective f :=
      injective_subgroupOf_normalizer_quot_monoidHom_ZMod_two
        A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D
    -- let := Equiv.ofInjective
    --   (A_subgroupOf_G_MonoidHom_ZMod_two A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D)
    --   (injective_A_subgroupOf_G_MonoidHom_ZMod_two
    -- A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D)

    have card_multiplicative_ZMod_two_eq_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]; rfl
    -- let := Equiv.mulEquiv (Equiv.ofInjective
    --   (A_subgroupOf_G_MonoidHom_ZMod_two A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D)
    --   (injective_A_subgroupOf_G_MonoidHom_ZMod_two
    -- A' G' A'_le_D hA'.right two_lt_card_A' A'_eq_G'_inf_D))

    rw [index] at hNA
    have key := ((Nat.bijective_iff_injective_and_card f).mpr
      ⟨Injective_f, by rwa [card_multiplicative_ZMod_two_eq_two]⟩).2

    dsimp [f, subgroupOf_normalizer_quot_monoidHom_ZMod_two] at key
    rw [← comp_assoc] at key
    -- want surjectivity of the second map on the left in the composition

    have surjective : Bijective ((monoidHom_normalizer_D_quot_D A' G')) :=
      bijective_monoidHom_normalizer_D_quot_D A' G' A'_le_D hA'.right two_lt_card_A'
        A'_eq_G'_inf_D hNA



    have normalizer_A'_inf_G'_sup_D_eq_normalizer_D :
      ((normalizer ((A') : Set SL(2,F))) ⊓ G' ⊔ D F) = (normalizer ((D F) : Set SL(2,F))) := by
      apply le_antisymm
      · apply sup_le
        · rw [A'_eq_G'_inf_D]

          apply inf_le_of_left_le
          -- for a suitable characteristic this should follow easily,
          -- or should generalise the result for the case when card D₀ ≤ 2
          rw [normalizer_subgroup_D_eq_DW_of_two_lt_card
            (by rw [A'_eq_G'_inf_D] at two_lt_card_A'; exact two_lt_card_A') inf_le_right,
            normalizer_D_eq_DW]
        · exact le_normalizer
      · sorry

    suffices ∃ δ : Fˣ, (d δ * w) ∈ ((normalizer ((A') : Set SL(2,F))) ⊓ G').carrier \ A' by
      obtain ⟨δ, mem_normalizer_A'_inf_G', not_mem_A'⟩ := this
      use conj c • (d δ * w)
      constructor
      · refine ⟨?mem_normalizer_inf_G, ?not_mem_A'⟩
        · rw [normalizer_inf_le_eq_normalizer_subgroupOf hA.right]
          sorry
        · intro contr
          rw [← Set.mem_inv_smul_set_iff, ← map_inv, A_eq_conj_A',
            map_inv, coe_pointwise_smul, inv_smul_smul, SetLike.mem_coe] at contr
          contradiction
      · have conj_x_mem_A' : conj c⁻¹ • x.val ∈ A' := by
          rw [← mem_inv_pointwise_smul_iff, map_inv, inv_inv, ← A_eq_conj_A']
          exact x.prop
        have conj_x_mem_D := A'_le_D conj_x_mem_A'
        obtain ⟨δ', hδ'⟩ := conj_x_mem_D
        symm at hδ'
        rw [smul_eq_iff_eq_inv_smul, map_inv, inv_inv] at hδ'
        simp only [smul_mul', MulAut.smul_def, conj_apply, conj_mul, hδ', mul_inv_rev, inv_inv,
          inv_w_eq_neg_w, inv_d_eq_d_inv, neg_mul, w_mul_d_eq_d_inv_w, neg_d_mul_w,
          InvMemClass.coe_inv]
        group
        simp only [Int.reduceNeg, zpow_neg, zpow_one, mul_left_inj]
        rw [← neg_d_eq_d_neg,
          show (c * d δ * w * d δ') * -d δ * w
            = (c * d δ * w * d δ') * d δ * -w by simp [- neg_d_eq_d_neg],
          ← inv_w_eq_neg_w,
          show c * d δ * w * d δ' * d δ * w⁻¹
            = c * d δ * w * (d δ' * d δ) * w⁻¹ by group, d_mul_d_eq_d_mul,
          show c * d δ * w * d (δ' * δ) * w⁻¹
            = c * d δ * (w * d (δ' * δ) * w⁻¹) by group,
            w_mul_d_mul_inv_w_eq_inv_d,  ← d_mul_d_eq_d_mul,
          show c * d δ * (d δ' * d δ)⁻¹
            = c * (d δ * (d δ' * d δ)⁻¹) by group]
        congr
        simp
    sorry
  sorry

  --   use x
  --   constructor
  --   · constructor
  --     · rw [mem_carrier, ← mem_inv_pointwise_smul_iff,
  --         normalizer_inf_le_eq_normalizer_subgroupOf hA.right,
  --         map_inv, inv_inv, conj_A_subgroupOf_G_eq_A'_subgroupOf_G A_eq_conj_A' G_eq_conj_G',
  --         ← normalizer_inf_le_eq_normalizer_subgroupOf hA'.right]




-- tactic which uses associativity before rewriting






  --       -- rw [pointwise_smul_def, map_map]

  --       -- relationship between conj c • (normalizer ((A) : Set SL(2,F))) vs (normalizer ((conj c • A) : Set SL(2,F)))
  --       sorry
  --     · intro contr
  --       rw [SetLike.mem_coe, ← mem_inv_pointwise_smul_iff,
  --         A_eq_conj_A', smul_smul] at contr

  --       sorry
  --   · sorry

  -- sorry

/-
Theorem 2.3 (v a) Let Q be a Sylow p-subgroup of G.
If Q = { I_G }, then there is a cyclic subgroup K of G such that N_G (Q) = Q K.
-/
theorem exists_IsCyclic_K_normalizer_eq_Q_join_K {F : Type*} [Field F] { p : ℕ }
  (hp : Nat.Prime p)
  (G : Subgroup SL(2,F))
  (Q : Sylow p G)
  (h : Q.toSubgroup ≠ ⊥) :
  ∃ K : Subgroup G, IsCyclic K ∧ normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K := by
  sorry

/-
Theorem 2.3 (v b)If |K| > |Z|, then K ∈ M.
-/
theorem K_mem_MaximalAbelianSubgroups_of_center_lt_card_K {F : Type*} [Field F]
  { p : ℕ } [hp' : Fact (Nat.Prime p)] (G : Subgroup SL(2,F))
  (Q : Sylow p G) (h : Q.toSubgroup ≠ ⊥) (K : Subgroup G)(hK : IsCyclic K)
  (hNG : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K) (h : Nat.card K > Nat.card (center SL(2,F))) :
    map G.subtype K ∈ MaximalAbelianSubgroupsOf G := by
  sorry
