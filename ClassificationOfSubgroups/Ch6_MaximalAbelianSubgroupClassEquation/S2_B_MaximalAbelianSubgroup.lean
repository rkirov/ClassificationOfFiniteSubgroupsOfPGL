import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_A_MaximalAbelianSubgroup
import Mathlib.GroupTheory.SchurZassenhaus

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

-- Extracted key lemma (Butler tex ~891): under the index-2 hypothesis `hNA`, the subgroup
-- `A'.subgroupOf G'` is properly contained in its normalizer inside `G'`, so there is a
-- representative `y` of a nontrivial coset. Since `2 < Nat.card A'`,
-- `normalizer A' = DW F` (Prop 1.7.i); as `y ∈ G'` and `y ∈ D F` would force `y ∈ G' ⊓ D F = A'`
-- (contradicting `y ∉ A'`), `y` must be of the form `d δ * w`. This witness is used both to
-- prove the reverse inclusion in `normalizer_A'_inf_G'_sup_D_eq_normalizer_D` and directly as
-- the witness needed in `of_index_normalizer_eq_two`.
lemma exists_d_mul_w_mem_normalizer_A'_inf_G'_diff_A' {F : Type*} [Field F] [IsAlgClosed F]
    (A' G' : Subgroup SL(2,F)) (A'_le_D : A' ≤ D F) (A'_le_G' : A' ≤ G')
    (two_lt_card_A' : 2 < Nat.card A') (A'_eq_G'_inf_D : A' = G' ⊓ D F)
    (hNA : Nat.card (normalizer ((A'.subgroupOf G') : Set ↥G')
        ⧸ (A'.subgroupOf G').subgroupOf (normalizer ((A'.subgroupOf G') : Set ↥G'))) = 2) :
    ∃ δ : Fˣ, d δ * w ∈ ((normalizer ((A') : Set SL(2,F))) ⊓ G').carrier \ A' := by
  haveI Finite_quot : Finite (↥(normalizer ((A'.subgroupOf G') : Set ↥G'))
      ⧸ (A'.subgroupOf G').subgroupOf (normalizer ((A'.subgroupOf G') : Set ↥G'))) :=
    Nat.finite_of_card_ne_zero (by rw [hNA]; norm_num)
  haveI nontriv : Nontrivial (↥(normalizer ((A'.subgroupOf G') : Set ↥G'))
      ⧸ (A'.subgroupOf G').subgroupOf (normalizer ((A'.subgroupOf G') : Set ↥G'))) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hNA]; norm_num)
  obtain ⟨q, hq⟩ := exists_ne (1 : ↥(normalizer ((A'.subgroupOf G') : Set ↥G'))
      ⧸ (A'.subgroupOf G').subgroupOf (normalizer ((A'.subgroupOf G') : Set ↥G')))
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q
  rw [ne_eq, QuotientGroup.eq_one_iff, mem_subgroupOf, mem_subgroupOf] at hq
  let y' : G' := (y : G')
  let y₀ : SL(2,F) := (y' : SL(2,F))
  have y₀_mem_inf : y₀ ∈ (normalizer ((A') : Set SL(2,F))) ⊓ G' := by
    rw [normalizer_inf_le_eq_normalizer_subgroupOf A'_le_G']
    exact mem_map.mpr ⟨y', y.2, rfl⟩
  have y₀_mem_DW : y₀ ∈ DW F := by
    rw [← normalizer_subgroup_D_eq_DW_of_two_lt_card two_lt_card_A' A'_le_D]
    exact y₀_mem_inf.1
  simp only [DW, mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_union,
    Set.mem_setOf_eq] at y₀_mem_DW
  rcases y₀_mem_DW with (⟨δ, hδ⟩ | ⟨δ, hδ⟩)
  · exfalso
    apply hq
    have mem_inf' : y₀ ∈ G' ⊓ D F := ⟨y₀_mem_inf.2, mem_D_iff.mpr ⟨δ, hδ⟩⟩
    rwa [← A'_eq_G'_inf_D] at mem_inf'
  · exact ⟨δ, hδ ▸ y₀_mem_inf, hδ ▸ hq⟩

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
      · intro x hx
        rw [normalizer_D_eq_DW] at hx
        simp only [DW, mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_union,
          Set.mem_setOf_eq] at hx
        rcases hx with (⟨δ', hδ'⟩ | ⟨δ', hδ'⟩)
        · exact mem_sup_right (mem_D_iff.mpr ⟨δ', hδ'⟩)
        · obtain ⟨δ, key_mem, key_not_mem⟩ :=
            exists_d_mul_w_mem_normalizer_A'_inf_G'_diff_A' A' G' A'_le_D hA'.right
              two_lt_card_A' A'_eq_G'_inf_D hNA
          have hcomp : (d δ * w)⁻¹ * (d δ' * w) = d (δ * δ'⁻¹) := by
            rw [inv_of_d_mul_w, mul_assoc, ← mul_assoc w, w_mul_d_eq_d_inv_w, mul_assoc _ w,
              w_mul_w_eq_neg_one, inv_d_eq_d_inv, ← mul_assoc, d_mul_d_eq_d_mul, mul_neg_one,
              neg_d_eq_d_neg, d_eq_d_iff, neg_mul, neg_neg]
          rw [← hδ', show d δ' * w = (d δ * w) * ((d δ * w)⁻¹ * (d δ' * w)) by group, hcomp]
          exact Subgroup.mul_mem_sup key_mem (mem_D_iff.mpr ⟨δ * δ'⁻¹, rfl⟩)

    suffices ∃ δ : Fˣ, (d δ * w) ∈ ((normalizer ((A') : Set SL(2,F))) ⊓ G').carrier \ A' by
      obtain ⟨δ, mem_normalizer_A'_inf_G', not_mem_A'⟩ := this
      use conj c • (d δ * w)
      constructor
      · refine ⟨?mem_normalizer_inf_G, ?not_mem_A'⟩
        · rw [normalizer_inf_le_eq_normalizer_subgroupOf hA.right]
          have A_eq_conj_A'' : conj c⁻¹ • A = A' := by
            rw [A_eq_conj_A', smul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
          have G_eq_conj_G'' : conj c⁻¹ • G = G' := rfl
          have hkey := mem_normalizer_iff_conj_smul_mem_conj_smul_normalizer' A A' G G' hA hA'
            A_eq_conj_A'' G_eq_conj_G''
          rw [mem_carrier, hkey, show (conj c⁻¹ : MulAut SL(2,F)) = (conj c)⁻¹ from map_inv conj c,
            mem_inv_pointwise_smul_iff, ← mem_carrier,
            normalizer_inf_le_eq_normalizer_subgroupOf hA.right] at mem_normalizer_A'_inf_G'
          exact mem_normalizer_A'_inf_G'
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
    exact exists_d_mul_w_mem_normalizer_A'_inf_G'_diff_A' A' G' A'_le_D hA'.right two_lt_card_A'
      A'_eq_G'_inf_D hNA
  · exfalso
    obtain ⟨Q, Nontrivial_Q, Finite_Q, Q_le_G, A_eq_QZ, elem_ab_Q, S, hS⟩ := h
    have bot_lt_Q : ⊥ < Q := bot_lt_iff_ne_bot.mpr ((Subgroup.nontrivial_iff_ne_bot Q).mp Nontrivial_Q)
    have p_dvd_Q : p ∣ Nat.card Q := elem_ab_Q.dvd_card bot_lt_Q
    have Q_le_A : Q ≤ A := A_eq_QZ ▸ le_sup_left
    have p_dvd_A : p ∣ Nat.card A := p_dvd_Q.trans (Subgroup.card_dvd_of_le Q_le_A)
    rw [Nat.coprime_comm] at hA'
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mp hA' p_dvd_A

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
Restated with the extra hypotheses `[IsAlgClosed F] [DecidableEq F] [CharP F p]`: these are
necessary (and are the standing hypotheses used throughout `S2_A_MaximalAbelianSubgroup.lean`,
e.g. `isCyclic_and_card_coprime_charP_or_eq_Q_sup_Z_of_center_ne`) since Butler's argument for
this theorem (tex ~899-948) takes place inside a fixed algebraically closed field of
characteristic `p`, and genuinely uses both the trigonalisability of unipotent elements
(needs `IsAlgClosed F`) and the fact that `p`-power order elements of `SL(2,F)` are unipotent
(needs `CharP F p`). Neither hypothesis was present on the `sorry`d statement; since this lemma
is used nowhere else in the repository we add them here (and propagate them to the two
downstream theorems in this file that use it).
-/

/-- Every element of the shear subgroup `S F` has order dividing `p`, when `CharP F p`. -/
lemma isPGroup_S {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)] [CharP F p] :
    IsPGroup p (S F) := by
  rintro ⟨x, σ, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  simp [SpecialMatrices.s_pow_eq_s_mul]

/-- An element of `SZ F = S F ⊔ Z F` whose order is a power of `p = char F` must lie in `S F`:
the "extra" factor of `-1` from `Z F` would force an order divisible by `2`, which (since
`char F = p` forces every nonzero shear to have order exactly `p`) cannot itself be a power of
the odd prime `p`, and if `p = 2` then `-1 = 1` so the two cases coincide. -/
lemma mem_S_of_mem_SZ_of_orderOf_eq_prime_pow {F : Type*} [Field F] {p k : ℕ}
    [hp' : Fact (Nat.Prime p)] [hC : CharP F p] {x : SL(2,F)} (hx : x ∈ SZ F)
    (hxk : orderOf x = p ^ k) : x ∈ S F := by
  simp only [SZ, mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_union,
    Set.mem_setOf_eq] at hx
  rcases hx with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
  · exact ⟨σ, rfl⟩
  · by_cases hp2 : p = 2
    · -- in characteristic `2`, `-1 = 1`, so `- s σ = s σ`
      have two_eq_zero : (2 : F) = 0 := by
        haveI : CharP F 2 := hp2 ▸ hC
        exact CharTwo.two_eq_zero
      have neg_one_eq_one : (-1 : SL(2,F)) = 1 :=
        (SpecialLinearGroup.neg_one_eq_one_of_two_eq_zero two_eq_zero).symm
      have : (- s σ : SL(2,F)) = s σ := by
        rw [← neg_one_mul, neg_one_eq_one, one_mul]
      rw [this]
      exact ⟨σ, rfl⟩
    · exfalso
      haveI : NeZero (2 : F) := NeZero_two_of_char_ne_two F hp2
      have hodd : Odd (p ^ k) := (hp'.out.odd_of_ne_two hp2).pow
      have hpow1 : (- s σ) ^ (p ^ k) = 1 := hxk ▸ pow_orderOf_eq_one _
      have hcomm : Commute (-1 : SL(2,F)) (s σ) := by
        have hmem : (-1 : SL(2,F)) ∈ Subgroup.center SL(2,F) := by
          rw [center_SL2_eq_Z]; exact neg_one_mem_Z
        exact (Subgroup.mem_center_iff.mp hmem (s σ)).symm
      have hpow2 : (- s σ) ^ (p ^ k) = (-1 : SL(2,F)) ^ (p ^ k) * (s σ) ^ (p ^ k) := by
        rw [← neg_one_mul (s σ), hcomm.mul_pow]
      rw [hodd.neg_one_pow] at hpow2
      rw [hpow2] at hpow1
      have hneg_one_sq : (-1 : SL(2,F)) * (-1 : SL(2,F)) = 1 := by ext <;> simp
      have hs_pow : (s σ) ^ (p ^ k) = -1 := by
        have h2 := congrArg (fun y => (-1 : SL(2,F)) * y) hpow1
        simp only [← mul_assoc] at h2
        rwa [hneg_one_sq, one_mul, mul_one] at h2
      have hsσ_mem_S : s σ ∈ S F := ⟨σ, rfl⟩
      have mem_inf : (s σ) ^ (p ^ k) ∈ D F ⊓ S F := by
        refine ⟨?_, pow_mem hsσ_mem_S (p ^ k)⟩
        rw [hs_pow]; exact mem_D_iff.mpr ⟨(-1 : Fˣ), d_neg_one_eq_neg_one⟩
      rw [D_meet_S_eq_bot, mem_bot] at mem_inf
      rw [mem_inf] at hs_pow
      exact neg_one_neq_one_of_two_ne_zero hs_pow

/-- A `p`-power order element of `SL(2,F)` (with `char F = p`) cannot be central: the only
central elements are `± 1`, and `-1` has order `2` (or is `1` itself if `p = 2`), neither of
which is a power of `p` unless `p = 2` and the element is trivial. -/
lemma not_mem_center_of_orderOf_eq_prime {F : Type*} [Field F] {p : ℕ} [hp' : Fact (Nat.Prime p)]
    [hC : CharP F p] {x : SL(2,F)} (hx : orderOf x = p) : x ∉ center SL(2,F) := by
  rw [center_SL2_eq_Z, mem_Z_iff]
  rintro (rfl | rfl)
  · simp at hx; exact hp'.out.ne_one hx.symm
  · by_cases hp2 : p = 2
    · have two_eq_zero : (2 : F) = 0 := by
        haveI : CharP F 2 := hp2 ▸ hC
        exact CharTwo.two_eq_zero
      rw [(SpecialLinearGroup.neg_one_eq_one_of_two_eq_zero two_eq_zero).symm] at hx
      simp at hx
      exact hp'.out.ne_one hx.symm
    · haveI : NeZero (2 : F) := NeZero_two_of_char_ne_two F hp2
      rw [orderOf_neg_one_eq_two] at hx
      exact hp2 hx.symm

/-- A `p`-power order element cannot be conjugate to a diagonal matrix `d δ`: transported through
`D_mulEquiv_units`, this would exhibit an element of order `p` inside `Fˣ`, impossible since
`char F = p`. -/
lemma not_isConj_d_of_orderOf_eq_prime {F : Type*} [Field F] {p : ℕ} [hp' : Fact (Nat.Prime p)]
    [hC : CharP F p] {x : SL(2,F)} (hx : orderOf x = p) (δ : Fˣ) : ¬ IsConj (d δ) x := by
  intro hconj
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hstep : (MulAut.conj c).toMonoidHom (d δ) = x := by
    show MulAut.conj c (d δ) = x
    rw [MulAut.conj_apply]; exact hc
  have horder : orderOf (d δ) = p := by
    have h1 := orderOf_injective (MulAut.conj c).toMonoidHom (MulEquiv.injective _) (d δ)
    rw [hstep] at h1
    exact h1.symm.trans hx
  have hDδ : orderOf (⟨d δ, d_mem_D⟩ : D F) = p := by
    have h2 := orderOf_injective (D F).subtype Subtype.coe_injective (⟨d δ, d_mem_D⟩ : D F)
    exact h2.symm.trans horder
  have hunits : orderOf ((D_mulEquiv_units F) (⟨d δ, d_mem_D⟩ : D F)) = p := by
    have h3 := orderOf_injective (D_mulEquiv_units F).toMonoidHom
      (MulEquiv.injective _) (⟨d δ, d_mem_D⟩ : D F)
    exact h3.trans hDδ
  have hδ : (D_mulEquiv_units F) (⟨d δ, d_mem_D⟩ : D F) = δ := by
    apply Units.ext
    simp [D_mulEquiv_units, d]
  rw [hδ] at hunits
  exact order_ne_char F p δ hunits

/-- The `(0,0)` entry of a lower-triangular matrix `x ∈ L F` is a unit (its inverse is the
`(1,1)` entry, since `det x = x 0 0 * x 1 1` when `x 0 1 = 0`). -/
lemma L_00_ne_zero {F : Type*} [Field F] [DecidableEq F] {x : SL(2,F)} (hx : x ∈ L F) :
    (x : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := by
  obtain ⟨δ, σ, rfl⟩ := hx
  simp [d, s]

/-- The projection `L F → Fˣ` sending `d δ * s σ ↦ δ`, realised concretely as the `(0,0)`
matrix entry (well defined since lower-triangular matrices in `L F` have nonzero `(0,0)`
entry). Its kernel is exactly `S F` (Lemma 6.1(ii)/(iii) in Butler's notation). -/
def L_toUnits_hom (F : Type*) [Field F] [DecidableEq F] : (L F) →* Fˣ where
  toFun x := Units.mk0 ((x : SL(2,F)) 0 0) (L_00_ne_zero x.2)
  map_one' := by ext; simp
  map_mul' := by
    intro x y
    apply Units.ext
    obtain ⟨δ, σ, hxeq⟩ := x.2
    have h01 : (d δ * s σ : SL(2,F)) 0 1 = 0 := by simp [d, s]
    have key : ((d δ * s σ * (y : SL(2,F)) : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 0 0
        = (d δ * s σ : SL(2,F)) 0 0 * (y : SL(2,F)) 0 0 := by
      have hcoe : ((d δ * s σ * (y : SL(2,F)) : SL(2,F)) : Matrix (Fin 2) (Fin 2) F)
          = (d δ * s σ : SL(2,F)) * (y : SL(2,F)) := rfl
      rw [hcoe, Matrix.mul_apply, Fin.sum_univ_two, h01, zero_mul, add_zero]
    simp only [Units.val_mul, Units.val_mk0, Subgroup.coe_mul, ← hxeq]
    exact key

lemma L_toUnits_hom_ker {F : Type*} [Field F] [DecidableEq F] :
    (L_toUnits_hom F).ker = (S F).subgroupOf (L F) := by
  ext x
  obtain ⟨δ, σ, hxeq⟩ := x.2
  simp only [MonoidHom.mem_ker, mem_subgroupOf]
  have hδeq : (x : SL(2,F)) 0 0 = δ := by rw [← hxeq]; simp [d, s]
  constructor
  · intro hker
    have hval : (x : SL(2,F)) 0 0 = 1 := by
      have := (Units.ext_iff).mp hker
      simpa [L_toUnits_hom] using this
    have hδ1 : δ = 1 := Units.ext (hδeq.symm.trans hval)
    refine ⟨σ, ?_⟩
    rw [← hxeq, hδ1, d_one_eq_one, one_mul]
  · rintro ⟨τ, hτ⟩
    have hδ1 : δ = 1 := by
      apply Units.ext
      rw [← hδeq, ← hτ]
      simp [s]
    apply Units.ext
    show (x : SL(2,F)) 0 0 = (1 : F)
    rw [hδeq, hδ1]
    rfl

lemma isCyclic_normalizer_subgroupOf_quot_of_ne_bot {F : Type*} [Field F] [IsAlgClosed F]
    [DecidableEq F] {p : ℕ} [hp' : Fact (Nat.Prime p)] [hC : CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G)
    (h : Q.toSubgroup ≠ ⊥) :
    IsCyclic (↥(normalizer (Q.toSubgroup : Set ↥G))
      ⧸ (Q.toSubgroup.subgroupOf (normalizer (Q.toSubgroup : Set ↥G)))) := by
  classical
  set Q' : Subgroup SL(2,F) := Subgroup.map G.subtype Q.toSubgroup with hQ'_def
  have Q'_le_G : Q' ≤ G := Subgroup.map_subtype_le Q.toSubgroup
  have hQ'_subgroupOf : Q'.subgroupOf G = Q.toSubgroup := by
    show (Q.toSubgroup.map G.subtype).comap G.subtype = Q.toSubgroup
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective G) Q.toSubgroup
  -- Step A: find a nonidentity element `z` of `Q.toSubgroup`, central in `Q.toSubgroup`,
  -- of order exactly `p`; its image `y` in `SL(2,F)` is then noncentral (since it has
  -- prime order `p = char F`) but every element of `Q'` commutes with it.
  haveI hQnt : Nontrivial (↥Q.toSubgroup) := (Subgroup.nontrivial_iff_ne_bot _).mpr h
  haveI hQfin : Finite (↥Q.toSubgroup) := Subtype.finite
  haveI := Q.isPGroup'.center_nontrivial
  obtain ⟨z₀, z₀_ne_one⟩ := exists_ne (1 : Subgroup.center (↥Q.toSubgroup))
  have z₀_ne_one' : (z₀ : ↥Q.toSubgroup) ≠ 1 := fun hc => z₀_ne_one (Subtype.ext hc)
  have z_central : ∀ q : ↥Q.toSubgroup, q * (z₀ : ↥Q.toSubgroup) = (z₀ : ↥Q.toSubgroup) * q :=
    fun q => Subgroup.mem_center_iff.mp z₀.2 q
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp Q.isPGroup' (z₀ : ↥Q.toSubgroup)
  have k_pos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · exact absurd (by rw [← orderOf_eq_one_iff, hk, hk0, pow_zero]) z₀_ne_one'
    · exact hk0
  set z : ↥Q.toSubgroup := (z₀ : ↥Q.toSubgroup) ^ (p ^ (k - 1)) with hz_def
  have hksucc : p ^ (k - 1) * p = p ^ k := by rw [← pow_succ]; congr 1; omega
  have z_pow_p : z ^ p = 1 := by
    rw [hz_def, ← pow_mul, hksucc, ← hk, pow_orderOf_eq_one]
  have z_ne_one : z ≠ 1 := by
    intro hz1
    rw [hz_def] at hz1
    have hdvd : orderOf (z₀ : ↥Q.toSubgroup) ∣ p ^ (k - 1) := orderOf_dvd_of_pow_eq_one hz1
    rw [hk] at hdvd
    have hle : p ^ k ≤ p ^ (k - 1) := Nat.le_of_dvd (pow_pos hp'.out.pos (k - 1)) hdvd
    have hlt : p ^ (k - 1) < p ^ k := Nat.pow_lt_pow_right hp'.out.one_lt (by omega)
    omega
  have orderOf_z : orderOf z = p := orderOf_eq_prime z_pow_p z_ne_one
  have z_central' : ∀ q : ↥Q.toSubgroup, q * z = z * q := by
    intro q
    rw [hz_def]
    exact (show Commute q (z₀ : ↥Q.toSubgroup) from z_central q).pow_right (p ^ (k - 1))
  set y : SL(2,F) := ((Q.toSubgroup.subtype z : ↥G) : SL(2,F)) with hy_def
  have y_in_G : y ∈ G.carrier := (Q.toSubgroup.subtype z : ↥G).2
  have hQ'_mem : ∀ q : ↥Q.toSubgroup, ((Q.toSubgroup.subtype q : ↥G) : SL(2,F)) ∈ Q' := by
    intro q
    exact ⟨Q.toSubgroup.subtype q, SetLike.coe_mem q, rfl⟩
  have y_mem_Q' : y ∈ Q' := hQ'_mem z
  have orderOf_y : orderOf y = p := by
    rw [hy_def]
    exact (orderOf_injective G.subtype (Subgroup.subtype_injective G)
      (Q.toSubgroup.subtype z)).trans
      ((orderOf_injective Q.toSubgroup.subtype (Subgroup.subtype_injective Q.toSubgroup)
        z).trans orderOf_z)
  have y_not_mem_center : y ∉ center SL(2,F) := not_mem_center_of_orderOf_eq_prime orderOf_y
  have Q'_le_centralizer_y : Q' ≤ centralizer {y} := by
    rintro q' hq'
    obtain ⟨q, hq_mem, rfl⟩ := hq'
    rw [mem_centralizer_iff]
    rintro w hw
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    have heq : ((Q.toSubgroup.subtype ⟨q, hq_mem⟩ : ↥G) : SL(2,F))
        * ((Q.toSubgroup.subtype z : ↥G) : SL(2,F))
        = ((Q.toSubgroup.subtype z : ↥G) : SL(2,F))
        * ((Q.toSubgroup.subtype ⟨q, hq_mem⟩ : ↥G) : SL(2,F)) := by
      have hc := congrArg (fun t : ↥Q.toSubgroup => ((Q.toSubgroup.subtype t : ↥G) : SL(2,F)))
        (z_central' ⟨q, hq_mem⟩)
      simpa using hc
    simpa [hy_def] using heq.symm
  -- Step B: locate `y` inside a conjugate of `SZ F`.
  have hy_conj_s_or_neg_s : ∃ σ : F, IsConj (s σ) y ∨ IsConj (- s σ) y := by
    rcases SL2_isConj_d_or_isConj_s_or_isConj_neg_s_of_algClosed y with
      (⟨δ, hδ⟩ | ⟨σ, hσ⟩ | ⟨σ, hσ⟩)
    · exact absurd hδ (not_isConj_d_of_orderOf_eq_prime orderOf_y δ)
    · exact ⟨σ, Or.inl hσ⟩
    · exact ⟨σ, Or.inr hσ⟩
  obtain ⟨σ, hy_conj⟩ := hy_conj_s_or_neg_s
  obtain ⟨c, hc⟩ := centralizer_eq_conj_SZ_of_isConj_s_or_isConj_neg_s
    (centralizer {y} ⊓ G) G σ y hy_conj y_in_G y_not_mem_center rfl
  -- Step C: every element of `Q'` lies in `conj c • S F`.
  have Q'_le_conj_SZ : Q' ≤ conj c • SZ F := by
    rw [hc]; exact Q'_le_centralizer_y
  have Q'_le_conj_S : Q' ≤ conj c • S F := by
    intro q' hq'
    rw [mem_pointwise_smul_iff_inv_smul_mem]
    have hq'_mem_SZ : (conj c)⁻¹ • q' ∈ SZ F :=
      (mem_pointwise_smul_iff_inv_smul_mem).mp (Q'_le_conj_SZ hq')
    obtain ⟨q, hq_mem, rfl⟩ := hq'
    set q'' : ↥Q.toSubgroup := ⟨q, hq_mem⟩ with hq''_def
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp Q.isPGroup' q''
    have horder : orderOf ((conj c)⁻¹ • ((Q.toSubgroup.subtype q'' : ↥G) : SL(2,F))) = p ^ j := by
      simp only [MulAut.smul_def]
      exact (orderOf_injective ((MulAut.conj c)⁻¹).toMonoidHom (MulEquiv.injective _) _).trans
        ((orderOf_injective G.subtype (Subgroup.subtype_injective G)
          (Q.toSubgroup.subtype q'')).trans
          ((orderOf_injective Q.toSubgroup.subtype
            (Subgroup.subtype_injective Q.toSubgroup) q'').trans hj))
    exact mem_S_of_mem_SZ_of_orderOf_eq_prime_pow hq'_mem_SZ horder
  -- Step D: by maximality of the Sylow subgroup `Q`, in fact `Q' = (conj c • S F) ⊓ G`.
  set R : Subgroup SL(2,F) := (conj c • S F) ⊓ G with hR_def
  have Q'_le_R : Q' ≤ R := fun x hx => ⟨Q'_le_conj_S hx, Q'_le_G hx⟩
  have isPGroup_conj_S : IsPGroup p (conj c • S F : Subgroup SL(2,F)) := by
    have : (S F).map (MulAut.conj c).toMonoidHom = conj c • S F := by
      rw [pointwise_smul_def]; rfl
    rw [← this]
    exact isPGroup_S.map _
  have isPGroup_R : IsPGroup p R := isPGroup_conj_S.to_le inf_le_left
  have isPGroup_P : IsPGroup p (R.subgroupOf G) := isPGroup_R.comap_subtype
  have Q_le_P : Q.toSubgroup ≤ R.subgroupOf G := by
    rw [← hQ'_subgroupOf]
    intro x hx
    rw [mem_subgroupOf] at hx ⊢
    exact Q'_le_R hx
  have hP_eq : R.subgroupOf G = Q.toSubgroup := Q.is_maximal' isPGroup_P Q_le_P
  have R_le_G : R ≤ G := inf_le_right
  have hQ'_eq_R : Q' = R := by
    have hmap : (R.subgroupOf G).map G.subtype = Q' := by rw [hP_eq]
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr R_le_G] at hmap
    exact hmap.symm
  -- Step E: transport `N_G(Q)/Q` across conjugation to `N_{G'}(S₀)/S₀`, where
  -- `G' := conj c⁻¹ • G` and `S₀ := conj c⁻¹ • Q' = S F ⊓ G'`, then bound the latter
  -- quotient via the projection `L_toUnits_hom`.
  have hconj_inv : (conj c⁻¹ : MulAut SL(2,F)) = (conj c)⁻¹ := map_inv conj c
  set G' : Subgroup SL(2,F) := conj c⁻¹ • G with hG'_def
  set S₀ : Subgroup SL(2,F) := conj c⁻¹ • Q' with hS₀_def
  have A_eq_conj_A' : conj c⁻¹ • Q' = S₀ := hS₀_def.symm
  have G_eq_conj_G' : conj c⁻¹ • G = G' := hG'_def.symm
  have hS₀_eq : S₀ = S F ⊓ G' := by
    rw [hS₀_def, hQ'_eq_R, hR_def, hG'_def, smul_inf, hconj_inv, smul_smul,
      inv_mul_cancel, one_smul]
  have hcard_Q' : 1 < Nat.card Q' := by
    rw [hQ'_def, Subgroup.card_subtype G Q.toSubgroup]
    exact Finite.one_lt_card_iff_nontrivial.mpr hQnt
  have hcard_S₀ : 1 < Nat.card S₀ := by
    rw [hS₀_def, Nat.card_congr (Subgroup.equivSMul (conj c⁻¹) Q').toEquiv.symm]
    exact hcard_Q'
  have hS₀_le_S : S₀ ≤ S F := hS₀_eq ▸ inf_le_left
  have hnormalizer_S₀ : normalizer (S₀ : Set SL(2,F)) ≤ L F :=
    normalizer_subgroup_S_le_L hcard_S₀ hS₀_le_S
  rw [← hQ'_subgroupOf]
  let φ := normalizer_subgroupOf_MulEquiv_normalizer_conj_subgroupOf A_eq_conj_A' G_eq_conj_G'
  have hφmap := map_normalizer_subgroupOf_eq_normalizer_conj_subgroupOf A_eq_conj_A' G_eq_conj_G'
  have hψ : Subgroup.map φ.toMonoidHom ((Q'.subgroupOf G).subgroupOf
      (normalizer (Q'.subgroupOf G : Set ↥G)))
      = (S₀.subgroupOf G').subgroupOf (normalizer (S₀.subgroupOf G' : Set ↥G')) := hφmap
  let ψ := QuotientGroup.congr _ _ φ hψ
  suffices IsCyclic (↥(normalizer (S₀.subgroupOf G' : Set ↥G'))
      ⧸ (S₀.subgroupOf G').subgroupOf (normalizer (S₀.subgroupOf G' : Set ↥G'))) from
    (MulEquiv.isCyclic ψ).mpr this
  -- Build the hom `normalizer (S₀.subgroupOf G') →* Fˣ` with kernel exactly
  -- `S₀.subgroupOf (normalizer (S₀.subgroupOf G'))`, via `L_toUnits_hom`.
  have hnormalizer_le : normalizer (S₀ : Set SL(2,F)) ⊓ G'
      = map G'.subtype (normalizer (S₀.subgroupOf G' : Set ↥G')) :=
    normalizer_inf_le_eq_normalizer_subgroupOf (hS₀_eq ▸ inf_le_right : S₀ ≤ G')
  have hnormalizer_subgroupOf_le : normalizer (S₀.subgroupOf G' : Set ↥G') ≤ (L F).subgroupOf G' := by
    intro x hx
    rw [mem_subgroupOf]
    have hx' : ((G'.subtype x : SL(2,F))) ∈ normalizer (S₀ : Set SL(2,F)) ⊓ G' := by
      rw [hnormalizer_le]; exact ⟨x, hx, rfl⟩
    exact hnormalizer_S₀ hx'.1
  let ι : ↥(normalizer (S₀.subgroupOf G' : Set ↥G')) →* L F :=
    MonoidHom.codRestrict (G'.subtype.comp (normalizer (S₀.subgroupOf G' : Set ↥G')).subtype)
      (L F) (fun x => hnormalizer_subgroupOf_le x.2)
  let f : ↥(normalizer (S₀.subgroupOf G' : Set ↥G')) →* Fˣ := (L_toUnits_hom F).comp ι
  have hxG' : ∀ x : ↥(normalizer (S₀.subgroupOf G' : Set ↥G')), (ι x : SL(2,F)) ∈ G' :=
    fun x => (x : ↥G').2
  have hf_ker : f.ker = (S₀.subgroupOf G').subgroupOf (normalizer (S₀.subgroupOf G' : Set ↥G')) := by
    ext x
    have hιx : (ι x : SL(2,F)) = ((x : ↥G') : SL(2,F)) := rfl
    simp only [f, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      mem_subgroupOf]
    rw [← MonoidHom.mem_ker, L_toUnits_hom_ker, mem_subgroupOf, hιx]
    constructor
    · intro hxS
      have hmem : (((x : ↥G') : SL(2,F))) ∈ S F ⊓ G' := ⟨hxS, hxG' x⟩
      rwa [← hS₀_eq] at hmem
    · intro hxS₀
      have hmem : (((x : ↥G') : SL(2,F))) ∈ S F ⊓ G' := hS₀_eq ▸ hxS₀
      exact hmem.1
  haveI hG'fin : Finite ↥G' := Finite.of_equiv ↥G (Subgroup.equivSMul (conj c⁻¹) G).toEquiv
  have hquot : (↥(normalizer (S₀.subgroupOf G' : Set ↥G'))
      ⧸ (S₀.subgroupOf G').subgroupOf (normalizer (S₀.subgroupOf G' : Set ↥G')))
      ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hf_ker.symm).trans (QuotientGroup.quotientKerEquivRange f)
  haveI : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hf'_inj : Function.Injective ((Units.coeHom F).comp f.range.subtype) :=
    fun a b hab => Subtype.ext (Units.ext hab)
  haveI : IsCyclic f.range :=
    isCyclic_of_injective_ringHom ((Units.coeHom F).comp f.range.subtype) hf'_inj
  exact (MulEquiv.isCyclic hquot).mpr inferInstance

/-
Theorem 2.3 (v a) Let Q be a Sylow p-subgroup of G.
If Q = { I_G }, then there is a cyclic subgroup K of G such that N_G (Q) = Q K.
-/
theorem exists_IsCyclic_K_normalizer_eq_Q_join_K {F : Type*} [Field F] [IsAlgClosed F]
  [DecidableEq F] { p : ℕ } [CharP F p]
  (hp : Nat.Prime p)
  (G : Subgroup SL(2,F)) [Finite G]
  (Q : Sylow p G)
  (h : Q.toSubgroup ≠ ⊥) :
  ∃ K : Subgroup G, IsCyclic K ∧ normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K := by
  haveI hp' : Fact (Nat.Prime p) := ⟨hp⟩
  have hcard_eq : Nat.card (Q.toSubgroup.subgroupOf (normalizer (Q.toSubgroup : Set ↥G)))
      = Nat.card Q.toSubgroup :=
    Nat.card_congr (subgroupOfEquivOfLe (le_normalizer)).toEquiv
  have hindex_dvd : (Q.toSubgroup.subgroupOf (normalizer (Q.toSubgroup : Set ↥G))).index
      ∣ Q.index :=
    relIndex_dvd_index_of_le (le_normalizer)
  have hcop : Nat.Coprime
      (Nat.card (Q.toSubgroup.subgroupOf (normalizer (Q.toSubgroup : Set ↥G))))
      (Q.toSubgroup.subgroupOf (normalizer (Q.toSubgroup : Set ↥G))).index := by
    rw [hcard_eq]
    exact Q.card_coprime_index.of_dvd_right hindex_dvd
  obtain ⟨K', hK'⟩ := Subgroup.exists_left_complement'_of_coprime hcop
  refine ⟨K'.map (normalizer (Q.toSubgroup : Set ↥G)).subtype, ?_, ?_⟩
  · have equivKQuot : (↥(normalizer (Q.toSubgroup : Set ↥G))
        ⧸ (Q.toSubgroup.subgroupOf (normalizer (Q.toSubgroup : Set ↥G)))) ≃* K' :=
      hK'.QuotientMulEquiv
    haveI : IsCyclic K' :=
      (MulEquiv.isCyclic equivKQuot).mp
        (isCyclic_normalizer_subgroupOf_quot_of_ne_bot G Q h)
    exact (MulEquiv.isCyclic
      (K'.equivMapOfInjective (normalizer (Q.toSubgroup : Set ↥G)).subtype
        (Subgroup.subtype_injective _))).mp inferInstance
  · have hsup : K' ⊔ (Q.toSubgroup.subgroupOf (normalizer (Q.toSubgroup : Set ↥G))) = ⊤ :=
      hK'.sup_eq_top
    have hmap := congrArg (Subgroup.map (normalizer (Q.toSubgroup : Set ↥G)).subtype) hsup
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr le_normalizer,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    rw [sup_comm]
    exact hmap.symm

/-
Theorem 2.3 (v b)If |K| > |Z|, then K ∈ M.
-/
-- TODO (Butler tex ~950-975, Thm 6.8 v-b): not attempted beyond the analysis below;
-- `isCyclic_normalizer_subgroupOf_quot_of_ne_bot` (Target 1 of this wave) was the priority
-- and consumed the available effort budget. Algebraic (non-geometric) route, avoiding
-- Butler's projective-line fixed-point argument:
--   (a) [DONE, easy] Since `IsCyclic K` and `Nat.card K > Nat.card (center SL(2,F))`, `K`
--       has a noncentral element `y` (else `map G.subtype K ≤ center SL(2,F)` would force
--       `Nat.card K ≤ Nat.card (center SL(2,F))`, via `Subgroup.card_subtype` +
--       `Nat.card_le_card_of_injective (Subgroup.inclusion ...)`, contradicting the
--       hypothesis).
--   (b) [DONE, existing lemma] `A := centralizer {y} ⊓ G ∈ MaximalAbelianSubgroupsOf G` via
--       `centralizer_inf_mem_maximalAbelianSubgroupsOf_of_noncentral` (needs
--       `[IsAlgClosed F] [DecidableEq F]`, not currently hypotheses of this theorem —
--       would need to be added, as for Target 1).
--   (c) [DONE, easy] `map G.subtype K ≤ A`: `K` is abelian (`IsCyclic.commGroup`) so every
--       element of `K` commutes with `y ∈ K`, hence lies in `centralizer {y}`; and
--       `map G.subtype K ≤ G` trivially.
--   (d) [NOT DONE — the crux] `A ≤ N_G(Q) (= Q.toSubgroup ⊔ K` via `hNG`). Butler proves this
--       via fixed points on the projective line. An algebraic substitute: reuse the
--       `isCyclic_normalizer_subgroupOf_quot_of_ne_bot` machinery above (Steps A-D in that
--       proof) to locate a conjugate `c` with `Subgroup.map G.subtype Q.toSubgroup =
--       (conj c • S F) ⊓ G` and `normalizer (map G.subtype Q.toSubgroup : Set SL(2,F)) ≤
--       conj c • L F`; this `c` is *not* currently exposed as a standalone/reusable fact
--       (it is local to that proof) — extracting it as a helper lemma
--       `exists_conj_eq_S_meet_G_and_normalizer_le` would be the first step. Given that `c`,
--       show `y` itself, being noncentral with order coprime to `p` (would need an added
--       hypothesis `Nat.Coprime (Nat.card K) p`, justified since the `K` arising from
--       `exists_IsCyclic_K_normalizer_eq_Q_join_K`'s Schur–Zassenhaus construction always
--       has this property, cf. the analogous added hypothesis discussion for Target 1), is
--       regular semisimple, i.e. `IsConj (d δ) y` for some `δ ≠ ±1` (ruled out unipotent via
--       an order argument as in `not_isConj_d_of_orderOf_eq_prime`, but the *positive*
--       direction — ruling out the `s σ`/`-s σ` branches instead — needs a fresh order
--       argument, not simply the negation of the existing lemma). Then a new small matrix
--       lemma in the style of `S4_PropertiesOfCentralizers`'s `centralizer_d_eq_D` /
--       `centralizer_s_eq_SZ` — "the centralizer of a lower-triangular matrix with distinct
--       eigenvalues is contained in `L F`" — would give `centralizer {y} ≤ conj c • L F`,
--       hence (intersecting with `G`) `A ≤ (conj c • L F) ⊓ G`, and a further argument
--       (paralleling Step E's `L_toUnits_hom`/kernel-`S F` analysis) would be needed to
--       upgrade this to `A ≤ N_G(Q)` exactly (not just into the ambient `conj c • L F`).
--   (e) Given (d), `A = A ⊓ (Q.toSubgroup ⊔ K) = (A ⊓ Q.toSubgroup) ⊔ K` (modular law, using
--       `K ≤ A`) `= K` provided `A ⊓ Q.toSubgroup = ⊥`: any nontrivial `u ∈ A ⊓ Q.toSubgroup`
--       is a nontrivial unipotent (`Q`'s elements have order `1` or `p`) commuting with the
--       noncentral, coprime-to-`p`-order `y`; the centralizer of a nontrivial unipotent is
--       `± S F`-conjugate (`centralizer_s_eq_SZ` in `S4_PropertiesOfCentralizers`), forcing
--       `y`'s order to divide `2p`, contradicting `Nat.Coprime (Nat.card K) p` together with
--       `y`'s order `> 2` (or a direct `p ∤ Nat.card K` vs. `p ∣ Nat.card (A ⊓ Q.toSubgroup)`
--       cardinality argument). This step reuses the `Commute.orderOf_mul_eq_mul_orderOf_of_coprime`-
--       style argument already developed for `mem_S_of_mem_SZ_of_orderOf_eq_prime_pow` above.
-- None of (d)/(e) is implemented; only (a)-(c) would type-check today (not committed, to
-- avoid an inconsistent partial state) and the sorry below stands for the whole theorem.
theorem K_mem_MaximalAbelianSubgroups_of_center_lt_card_K {F : Type*} [Field F]
  { p : ℕ } [hp' : Fact (Nat.Prime p)] (G : Subgroup SL(2,F))
  (Q : Sylow p G) (h : Q.toSubgroup ≠ ⊥) (K : Subgroup G)(hK : IsCyclic K)
  (hNG : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K) (h : Nat.card K > Nat.card (center SL(2,F))) :
    map G.subtype K ∈ MaximalAbelianSubgroupsOf G := by
  sorry
