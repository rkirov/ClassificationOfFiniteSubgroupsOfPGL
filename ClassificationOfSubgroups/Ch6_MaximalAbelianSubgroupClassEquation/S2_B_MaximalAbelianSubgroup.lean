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

/-
Butler Thm 6.8(iv) at `p = 2`. The informal proof's degenerate case, "if `|A| ≤ 2` then
`A = Z = G`" (tex ~838), is FALSE as an unqualified statement in characteristic `2`: `S2_A`'s
comment above `eq_center_of_card_le_two` records a counterexample subgroup of `GL(2,𝔽₂)` where a
*noncentral* unipotent involution generates an order-`2` abelian subgroup (since `Z = ⊥` in
characteristic `2`, by `card_Z_eq_one_of_two_eq_zero`/Lemma 6.2). But Theorem 6.8(iv) itself only
ever applies this degenerate case under its own standing hypothesis `Nat.Coprime (Nat.card A) p`;
at `p = 2` this forces `Nat.card A` to be *odd*, and combined with `Nat.card A ≤ 2` this forces
`Nat.card A = 1`, i.e. `A = ⊥ = Z`, sidestepping the gap entirely (the counterexample's witness
subgroup has order `2`, which is not coprime to `2`, so it is excluded by the hypothesis).

Grepping `p_ne_two` through `S2_A`/`S2_B` shows this is in fact the *only* place `p ≠ 2` is used
anywhere in the chain leading to Theorem 6.8(iv): `relIndex_normalizer_le_two`
(`S2_A`, the "`≤ 2`" half) and `of_index_normalizer_eq_two` (the inversion-witness half, above)
both use `p_ne_two` exactly once, to rule out `Nat.card A ≤ 2` via
`relIndex_eq_one_of_card_le_two`/`eq_center_of_card_le_two`; every other step (conjugating `A`
into `D`, `N_L(Ã) = ⟨D,w⟩` via `normalizer_subgroup_D_eq_DW_of_two_lt_card`, the second
isomorphism theorem machinery of `subgroupOf_normalizer_quot_monoidHom_ZMod_two`, and the final
`Q ⊔ Z`-branch contradiction via `hA' : Nat.Coprime (Nat.card A) p`) is already characteristic-free
(no `p_ne_two`, no case split on `p`). So Theorem 6.8(iv) is TRUE at `p = 2` under the coprimality
hypothesis, with the same proof, once the degenerate `Nat.card A ≤ 2` case is patched as above.

We give char-`2` analogues of the three `p_ne_two`-carrying declarations here (as `S2_A` is
read-only): `eq_center_of_card_le_two_of_coprime_two`, `relIndex_eq_one_of_card_le_two_of_coprime_two`,
and `of_index_normalizer_eq_two_char_two`, replacing `p_ne_two` with `[CharP F 2]` plus the
coprimality hypothesis Theorem 6.8(iv) already assumes. (`S2_A`'s `relIndex_normalizer_le_two`,
the "`≤ 2`" half, is not restated here since it is out of `of_index_normalizer_eq_two`'s scope and
`S2_A` cannot be edited; the same patch applies to it verbatim, by the argument above.)
-/

/-- Char-`2` analogue of `eq_center_of_card_le_two`: under the coprimality hypothesis Theorem
6.8(iv) already carries, `Nat.card A ≤ 2` forces `Nat.card A ≠ 2` (as `2` is not coprime to
itself), hence `Nat.card A = 1`, i.e. `A = ⊥`; and `center SL(2,F) = ⊥` in characteristic `2`
(`card_Z_eq_one_of_two_eq_zero`), so `A = center SL(2,F)`. This sidesteps the char-`2` gap in
`eq_center_of_card_le_two` (see the comment above `eq_center_of_card_le_two` in `S2_A`, and the
comment above this section): the counterexample there has order `2`, excluded here by
`hA_cop`. -/
lemma eq_center_of_card_le_two_of_coprime_two {F : Type*} [Field F] [CharP F 2]
    (A G : Subgroup SL(2,F)) [hG : Finite G]
    (_center_le_G : center SL(2,F) ≤ G) (hA : A ∈ MaximalAbelianSubgroupsOf G)
    (card_A_le_two : Nat.card A ≤ 2) (hA_cop : Nat.Coprime (Nat.card A) 2) :
    A = center SL(2,F) := by
  let A_finite : Finite (A : Set SL(2,F)) := Finite.Set.subset G hA.right
  have card_A_ne_two : Nat.card A ≠ 2 := by
    intro h
    rw [h, Nat.Coprime, Nat.gcd_self] at hA_cop
    norm_num at hA_cop
  have card_A_pos : 0 < Nat.card A := Nat.card_pos
  have card_A_eq_one : Nat.card A = 1 := by omega
  have A_eq_bot : A = ⊥ := Subgroup.card_eq_one.mp card_A_eq_one
  have Z_eq_bot : center SL(2,F) = ⊥ := by
    rw [center_SL2_eq_Z]
    exact Subgroup.card_eq_one.mp (card_Z_eq_one_of_two_eq_zero CharTwo.two_eq_zero)
  rw [A_eq_bot, Z_eq_bot]

/-- Char-`2` analogue of `relIndex_eq_one_of_card_le_two`. -/
lemma relIndex_eq_one_of_card_le_two_of_coprime_two
    {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F] [CharP F 2]
    (A G : Subgroup SL(2,F)) (center_le_G : center SL(2,F) ≤ G)
    (hA : A ∈ MaximalAbelianSubgroupsOf G) [hG : Finite G]
    (card_A_le_two : Nat.card A ≤ 2) (hA_cop : Nat.Coprime (Nat.card A) 2) :
    relIndex (A.subgroupOf G) (normalizer ((A.subgroupOf G) : Set ↥G)) = 1 := by
  rw [eq_center_of_card_le_two_of_coprime_two A G center_le_G hA card_A_le_two hA_cop]
  have center_is_normal : Normal ((center SL(2,F)).subgroupOf G) := normal_subgroupOf
  rw [relIndex, normalizer_eq_top_iff.mpr center_is_normal, ← comap_subtype, ← subgroupOf_self,
    index_comap, Subgroup.range_subtype, Subgroup.relIndex_subgroupOf (le_refl _)]
  have G_eq_center : G = center SL(2,F) := by
    rw [eq_center_of_card_le_two_of_coprime_two A G center_le_G hA card_A_le_two hA_cop] at hA
    contrapose! hA
    exact center_not_mem_of_center_ne hA.symm
  rw [relIndex_eq_one]
  exact le_of_eq_of_le G_eq_center (le_refl _)

/-- Char-`2` analogue of `of_index_normalizer_eq_two` (Theorem 6.8(iv-b), Butler tex ~889-897),
with `p_ne_two` replaced by `[CharP F 2]` together with the coprimality hypothesis `hA'` that
Theorem 6.8(iv) already assumes. Identical proof to `of_index_normalizer_eq_two` beyond the
derivation of `two_lt_card_A` (see the comment above `eq_center_of_card_le_two_of_coprime_two`
for why the rest of the argument is characteristic-free). -/
theorem of_index_normalizer_eq_two_char_two {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
  [CharP F 2] (A G : Subgroup SL(2,F))
  [Finite G] (hA : A ∈ MaximalAbelianSubgroupsOf G) (center_le_G : center SL(2,F) ≤ G)
  (hA' : Nat.Coprime (Nat.card A) 2)
  (hNA : relIndex (A.subgroupOf G) (normalizer ((A.subgroupOf G) : Set ↥G)) = 2) (x : A) :
    ∃ y ∈ ((normalizer ((A) : Set SL(2,F))) ⊓ G).carrier \ A, y * x * y⁻¹ = x⁻¹ := by
  haveI hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have two_lt_card_A : 2 < Nat.card A := by
    have key : Nat.card A ≤ 2 →
        relIndex (A.subgroupOf G) (normalizer ((A.subgroupOf G) : Set ↥G)) = 1 :=
      fun card_A_le_two =>
        relIndex_eq_one_of_card_le_two_of_coprime_two A G center_le_G hA card_A_le_two hA'
    contrapose! key
    constructor
    · exact key
    · rw [hNA]
      norm_num
  have G_ne_center : G ≠ center SL(2,F) := G_ne_center_of_two_lt_card A G hA two_lt_card_A

  rcases isCyclic_and_card_coprime_charP_or_eq_Q_sup_Z_of_center_ne 2 G A hA
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

    have card_multiplicative_ZMod_two_eq_two : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]; rfl

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
    have p_dvd_Q : 2 ∣ Nat.card Q := elem_ab_Q.dvd_card bot_lt_Q
    have Q_le_A : Q ≤ A := A_eq_QZ ▸ le_sup_left
    have p_dvd_A : 2 ∣ Nat.card A := p_dvd_Q.trans (Subgroup.card_dvd_of_le Q_le_A)
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

-- ===== Helper lemmas for Theorem 2.3 (v b) =====

lemma mem_normalizer_of_conj_mem_of_conj_inv_mem {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hfwd : ∀ n ∈ H, g * n * g⁻¹ ∈ H) (hfwd' : ∀ n ∈ H, g⁻¹ * n * g⁻¹⁻¹ ∈ H) :
    g ∈ normalizer H := by
  rw [mem_normalizer_iff]
  intro n
  refine ⟨hfwd n, ?_⟩
  intro hgn
  have h2 := hfwd' _ hgn
  have heq : g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n := by group
  rwa [heq] at h2

lemma normalizer_conj_smul_eq_conj_smul_normalizer {F : Type*} [Field F] (c : SL(2,F))
    (X : Subgroup SL(2,F)) :
    normalizer ((conj c • X : Subgroup SL(2,F)) : Set SL(2,F))
      = conj c • normalizer (X : Set SL(2,F)) := by
  have h1 : X.map (MulAut.conj c).toMonoidHom = conj c • X := by
    rw [pointwise_smul_def]; rfl
  have h2 : (normalizer (X : Set SL(2,F))).map (MulAut.conj c).toMonoidHom
      = conj c • normalizer (X : Set SL(2,F)) := by
    rw [pointwise_smul_def]; rfl
  rw [← h1, ← h2]
  exact (Subgroup.map_equiv_normalizer_eq X (MulAut.conj c)).symm

/-- `L F` normalizes `S F` (Butler's `d_ω t_λ` conjugation computation): for `l = d δ * s τ ∈ L F`
and `n = s σ ∈ S F`, `l * n * l⁻¹ = s (σ * δ⁻¹ * δ⁻¹) ∈ S F`. -/
lemma L_le_normalizer_S {F : Type*} [Field F] [DecidableEq F] :
    L F ≤ normalizer (S F : Set SL(2,F)) := by
  have hfwd : ∀ l ∈ L F, ∀ n ∈ S F, l * n * l⁻¹ ∈ S F := by
    rintro l ⟨δ, τ, rfl⟩ n ⟨σ, rfl⟩
    refine ⟨σ * (↑δ⁻¹ : F) * (↑δ⁻¹ : F), ?_⟩
    ext <;> simp [d, s] <;> field_simp <;> ring
  intro l hl
  exact mem_normalizer_of_conj_mem_of_conj_inv_mem (hfwd l hl) (hfwd l⁻¹ (inv_mem hl))

/-- `p ∣ orderOf (- s σ)` for `σ ≠ 0` (char `F = p`): if `p = 2` then `-1 = 1` so `-s σ = s σ`
has order `p`; otherwise `-1` and `s σ` commute with coprime orders `2` and `p`, so
`orderOf (-s σ) = orderOf (-1) * orderOf (s σ) = 2p`. -/
lemma orderOf_neg_s_dvd_of_ne_zero {F : Type*} [Field F] {p : ℕ} [hp' : Fact (Nat.Prime p)]
    [hC : CharP F p] {σ : F} (hσ : σ ≠ 0) : p ∣ orderOf (- s σ) := by
  by_cases hp2 : p = 2
  · have two_eq_zero : (2 : F) = 0 := by
      haveI : CharP F 2 := hp2 ▸ hC
      exact CharTwo.two_eq_zero
    have neg_one_eq_one : (-1 : SL(2,F)) = 1 :=
      (SpecialLinearGroup.neg_one_eq_one_of_two_eq_zero two_eq_zero).symm
    have hneg : (- s σ : SL(2,F)) = s σ := by rw [← neg_one_mul, neg_one_eq_one, one_mul]
    rw [hneg, order_s_eq_char σ hσ, hp2]
  · haveI : NeZero (2 : F) := NeZero_two_of_char_ne_two F hp2
    have horder_s : orderOf (s σ) = p := order_s_eq_char σ hσ
    have hcomm : Commute (-1 : SL(2,F)) (s σ) := by
      have hmem : (-1 : SL(2,F)) ∈ Subgroup.center SL(2,F) := by
        rw [center_SL2_eq_Z]; exact neg_one_mem_Z
      exact (Subgroup.mem_center_iff.mp hmem (s σ)).symm
    have hcop : (orderOf (-1 : SL(2,F))).Coprime (orderOf (s σ)) := by
      rw [orderOf_neg_one_eq_two, horder_s]
      exact (Nat.coprime_primes Nat.prime_two hp'.out).mpr (fun heq => hp2 heq.symm)
    have hmuleq := hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop
    rw [neg_one_mul] at hmuleq
    rw [hmuleq, orderOf_neg_one_eq_two, horder_s]
    exact dvd_mul_left p 2

/-- The centralizer of a lower-triangular matrix `x = d δ * s τ ∈ L F` with distinct diagonal
entries is contained in `L F`: for `z` commuting with `x`, comparing the `(0,1)` entries of
`x * z` and `z * x` forces `z 0 1 = 0`. -/
lemma centralizer_le_L_of_lower_triangular_regular {F : Type*} [Field F] [DecidableEq F]
    {x : SL(2,F)} (hx : x ∈ L F)
    (h_reg : (x : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ (x : Matrix (Fin 2) (Fin 2) F) 1 1) :
    centralizer {x} ≤ L F := by
  intro z hz
  rw [mem_centralizer_iff] at hz
  have hxz : x * z = z * x := hz x rfl
  have hx01 : (x : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := mem_L_iff_lower_triangular.mp hx
  have hcoe1 : ((x * z : SL(2,F)) : Matrix (Fin 2) (Fin 2) F)
      = (x : Matrix (Fin 2) (Fin 2) F) * (z : Matrix (Fin 2) (Fin 2) F) := rfl
  have hcoe2 : ((z * x : SL(2,F)) : Matrix (Fin 2) (Fin 2) F)
      = (z : Matrix (Fin 2) (Fin 2) F) * (x : Matrix (Fin 2) (Fin 2) F) := rfl
  have hentry : (x : Matrix (Fin 2) (Fin 2) F) 0 0 * (z : Matrix (Fin 2) (Fin 2) F) 0 1
      = (z : Matrix (Fin 2) (Fin 2) F) 0 1 * (x : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have h01 : ((x * z : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 0 1
        = ((z * x : SL(2,F)) : Matrix (Fin 2) (Fin 2) F) 0 1 := by rw [hxz]
    rw [hcoe1, hcoe2, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_two,
      hx01] at h01
    simpa using h01
  have hz01 : (z : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have hne : (x : Matrix (Fin 2) (Fin 2) F) 1 1 - (x : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm h_reg)
    have heq : (z : Matrix (Fin 2) (Fin 2) F) 0 1
        * ((x : Matrix (Fin 2) (Fin 2) F) 1 1 - (x : Matrix (Fin 2) (Fin 2) F) 0 0) = 0 := by
      rw [mul_sub]
      linear_combination -hentry
    exact (mul_eq_zero.mp heq).resolve_right hne
  rw [mem_L_iff_lower_triangular, MatrixShapes.IsLowerTriangular]
  exact hz01

lemma le_normalizer_inf {G : Type*} [Group G] (H K : Subgroup G) :
    normalizer (H : Set G) ⊓ normalizer (K : Set G) ≤ normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  intro a ha
  rw [mem_inf, mem_normalizer_iff, mem_normalizer_iff] at ha
  rw [mem_normalizer_iff]
  intro n
  simp only [mem_inf]
  exact and_congr (ha.1 n) (ha.2 n)

/-- Conjugate elements have the same order. -/
lemma orderOf_conj {G : Type*} [Group G] (c x : G) : orderOf (c * x * c⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj c).toMonoidHom (MulEquiv.injective _) x
  simpa [MonoidHom.coe_coe, MulAut.conj_apply] using h

/-- Extracted from Steps A-D of `isCyclic_normalizer_subgroupOf_quot_of_ne_bot`: locate a
conjugating element `c` such that the image of a nontrivial Sylow `p`-subgroup `Q` of `G` in
`SL(2,F)` is exactly `(conj c • S F) ⊓ G`, and the normalizer of `Q` (mapped into `SL(2,F)`) lies
inside `(conj c • L F) ⊓ G`. (The latter is obtained via `normalizer_subgroup_S_le_L` transported
by conjugation, rather than the further `L_toUnits_hom`/quotient-cyclic machinery of Step E, which
is not needed here.) -/
lemma exists_conj_Sylow_eq_S_inf_and_normalizer_le_L {F : Type*} [Field F] [IsAlgClosed F]
    [DecidableEq F] {p : ℕ} [hp' : Fact (Nat.Prime p)] [hC : CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G) (h : Q.toSubgroup ≠ ⊥) :
    ∃ c : SL(2,F), map G.subtype Q.toSubgroup = (conj c • S F) ⊓ G ∧
      map G.subtype (normalizer (Q.toSubgroup : Set ↥G)) ≤ (conj c • L F) ⊓ G := by
  classical
  set Q' : Subgroup SL(2,F) := Subgroup.map G.subtype Q.toSubgroup with hQ'_def
  have Q'_le_G : Q' ≤ G := Subgroup.map_subtype_le Q.toSubgroup
  have hQ'_subgroupOf : Q'.subgroupOf G = Q.toSubgroup := by
    show (Q.toSubgroup.map G.subtype).comap G.subtype = Q.toSubgroup
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective G) Q.toSubgroup
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
  have hy_conj_s_or_neg_s : ∃ σ : F, IsConj (s σ) y ∨ IsConj (- s σ) y := by
    rcases SL2_isConj_d_or_isConj_s_or_isConj_neg_s_of_algClosed y with
      (⟨δ, hδ⟩ | ⟨σ, hσ⟩ | ⟨σ, hσ⟩)
    · exact absurd hδ (not_isConj_d_of_orderOf_eq_prime orderOf_y δ)
    · exact ⟨σ, Or.inl hσ⟩
    · exact ⟨σ, Or.inr hσ⟩
  obtain ⟨σ, hy_conj⟩ := hy_conj_s_or_neg_s
  obtain ⟨c, hc⟩ := centralizer_eq_conj_SZ_of_isConj_s_or_isConj_neg_s
    (centralizer {y} ⊓ G) G σ y hy_conj y_in_G y_not_mem_center rfl
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
  refine ⟨c, hQ'_eq_R, ?_⟩
  rw [← hQ'_subgroupOf, ← normalizer_inf_le_eq_normalizer_subgroupOf Q'_le_G]
  apply inf_le_inf_right
  have hconj_inv : (conj c⁻¹ : MulAut SL(2,F)) = (conj c)⁻¹ := map_inv conj c
  set X : Subgroup SL(2,F) := conj c⁻¹ • Q' with hX_def
  have hX_eq : X = S F ⊓ (conj c⁻¹ • G) := by
    rw [hX_def, hQ'_eq_R, hR_def, smul_inf, hconj_inv, smul_smul, inv_mul_cancel, one_smul]
  have hX_le_S : X ≤ S F := hX_eq ▸ inf_le_left
  have hcard_Q' : 1 < Nat.card Q' := by
    rw [hQ'_def, Subgroup.card_subtype G Q.toSubgroup]
    exact Finite.one_lt_card_iff_nontrivial.mpr hQnt
  have hcard_X : 1 < Nat.card X := by
    rw [hX_def, Nat.card_congr (Subgroup.equivSMul (conj c⁻¹) Q').toEquiv.symm]
    exact hcard_Q'
  have hnormalizer_X : normalizer (X : Set SL(2,F)) ≤ L F :=
    normalizer_subgroup_S_le_L hcard_X hX_le_S
  have hQ'_eq_conj_X : Q' = conj c • X := by
    rw [hX_def, smul_smul, hconj_inv, mul_inv_cancel, one_smul]
  have hnormalizer_eq : normalizer (Q' : Set SL(2,F)) = conj c • normalizer (X : Set SL(2,F)) := by
    rw [hQ'_eq_conj_X]
    exact normalizer_conj_smul_eq_conj_smul_normalizer c X
  rw [hnormalizer_eq]
  intro x hx
  rw [mem_pointwise_smul_iff_inv_smul_mem] at hx ⊢
  exact hnormalizer_X hx


/-
Theorem 2.3 (v b)If |K| > |Z|, then K ∈ M.
-/
-- RESTATED+PROVED (Butler tex ~950-975, Thm 6.8 v-b): the algebraic (non-geometric) route
-- sketched previously is carried out in full below, avoiding Butler's projective-line
-- fixed-point argument. Restated with `[IsAlgClosed F] [DecidableEq F] [CharP F p] [Finite G]`
-- (needed for `centralizer_inf_mem_maximalAbelianSubgroupsOf_of_noncentral`,
-- `exists_conj_Sylow_eq_S_inf_and_normalizer_le_L`, and the Sylow-cardinality arguments; none
-- were hypotheses of the original `sorry`d statement) and an added hypothesis
-- `hcop : Nat.Coprime (Nat.card K) p` (justified since the `K` arising from
-- `exists_IsCyclic_K_normalizer_eq_Q_join_K`'s Schur–Zassenhaus construction always has this
-- property; this lemma is used nowhere else in the repository).
-- Proof outline: (a) find a noncentral `y` in the image of `K` (else its cardinality would be
-- bounded by `Nat.card (center SL(2,F))`); (b)-(c) `A := centralizer {y} ⊓ G` is a maximal
-- abelian subgroup containing the image of `K`; (d) using
-- `exists_conj_Sylow_eq_S_inf_and_normalizer_le_L` to locate a conjugating element `c` with
-- `map G.subtype Q.toSubgroup = (conj c • S F) ⊓ G`, together with `L_le_normalizer_S`
-- (transported by `c`) and the regularity of `l0 := c⁻¹ * y * c ∈ L F` (its diagonal entries
-- are distinct, using `hcop` to rule out the unipotent/`±1`-diagonal cases via
-- `orderOf_neg_s_dvd_of_ne_zero`), `centralizer_le_L_of_lower_triangular_regular` gives
-- `A ≤ normalizer (map G.subtype Q.toSubgroup : Set SL(2,F))`, hence
-- `A ≤ map G.subtype Q.toSubgroup ⊔ map G.subtype K`; (e) `A ⊓ map G.subtype Q.toSubgroup = ⊥`
-- (a nontrivial common element would force `l0` into `SZ F`, contradicting its regularity via
-- `centralizer_s_eq_SZ`), and a Dedekind/Frattini argument (via `Subgroup.mul_normal`, using
-- that `Q`'s image is normal in its own join with the image of `K`) concludes
-- `A = map G.subtype K`.
theorem K_mem_MaximalAbelianSubgroups_of_center_lt_card_K {F : Type*} [Field F] [IsAlgClosed F]
  [DecidableEq F] { p : ℕ } [hp' : Fact (Nat.Prime p)] [hC : CharP F p] (G : Subgroup SL(2,F))
  [Finite G] (Q : Sylow p G) (h : Q.toSubgroup ≠ ⊥) (K : Subgroup G) (hK : IsCyclic K)
  (hNG : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K)
  (hKZ : Nat.card K > Nat.card (center SL(2,F)))
  (hcop : Nat.Coprime (Nat.card K) p) :
    map G.subtype K ∈ MaximalAbelianSubgroupsOf G := by
  classical
  have hKimg_le_G : map G.subtype K ≤ G := Subgroup.map_subtype_le K
  -- Step a: find a noncentral element y of the image of K
  have hKnotle : ¬ (map G.subtype K ≤ center SL(2,F)) := by
    intro hle
    have hcardle : Nat.card (map G.subtype K) ≤ Nat.card (center SL(2,F)) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    have hcardeq : Nat.card (map G.subtype K) = Nat.card K :=
      Nat.card_congr (K.equivMapOfInjective G.subtype (Subgroup.subtype_injective G)).toEquiv.symm
    rw [hcardeq] at hcardle
    omega
  rw [SetLike.le_def] at hKnotle
  push_neg at hKnotle
  obtain ⟨y, hy_mem, hy_not_center⟩ := hKnotle
  have hy_in_G : y ∈ G.carrier := hKimg_le_G hy_mem
  -- Step b: A := centralizer{y} ⊓ G ∈ MaximalAbelianSubgroupsOf G
  have hA_mem : centralizer {y} ⊓ G ∈ MaximalAbelianSubgroupsOf G :=
    centralizer_inf_mem_maximalAbelianSubgroupsOf_of_noncentral G y ⟨hy_in_G, hy_not_center⟩
  set A : Subgroup SL(2,F) := centralizer {y} ⊓ G with hA_def
  -- Step c: image of K ≤ A
  have hKimg_le_A : map G.subtype K ≤ A := by
    obtain ⟨k0, hk0_mem, hk0_eq⟩ := hy_mem
    obtain ⟨g, hg⟩ := hK.exists_generator
    rintro _ ⟨k, hk_mem, rfl⟩
    refine ⟨mem_centralizer_iff.mpr fun w hw => ?_, hKimg_le_G ⟨k, hk_mem, rfl⟩⟩
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    rw [← hk0_eq]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg (⟨k, hk_mem⟩ : K))
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (⟨k0, hk0_mem⟩ : K))
    have hcomm : (⟨k, hk_mem⟩ : K) * ⟨k0, hk0_mem⟩ = ⟨k0, hk0_mem⟩ * ⟨k, hk_mem⟩ := by
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    have hc := congrArg (fun t : K => (G.subtype t : SL(2,F))) hcomm
    simpa using hc.symm
  -- Step d: locate the Sylow-conjugation witness and show `A ≤ N_G(Q)`-image
  obtain ⟨c, hQ'_eq, hnormalizer_le⟩ :=
    exists_conj_Sylow_eq_S_inf_and_normalizer_le_L G Q h
  have hQ'_le_G : map G.subtype Q.toSubgroup ≤ G := Subgroup.map_subtype_le Q.toSubgroup
  have hQ'_subgroupOf : (map G.subtype Q.toSubgroup).subgroupOf G = Q.toSubgroup := by
    show (Q.toSubgroup.map G.subtype).comap G.subtype = Q.toSubgroup
    exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective G) Q.toSubgroup
  have hK_le_normalizer : K ≤ normalizer (Q.toSubgroup : Set ↥G) := by
    rw [hNG]; exact le_sup_right
  have hKimg_le_normalizer : map G.subtype K ≤ map G.subtype (normalizer (Q.toSubgroup : Set ↥G)) :=
    Subgroup.map_mono hK_le_normalizer
  have hy_mem_conjL : y ∈ (conj c • L F) ⊓ G := hnormalizer_le (hKimg_le_normalizer hy_mem)
  set l0 : SL(2,F) := c⁻¹ * y * c with hl0_def
  have hy_eq : y = c * l0 * c⁻¹ := by rw [hl0_def]; group
  have hl0_mem_L : l0 ∈ L F := by
    have hy_mem' : y ∈ conj c • L F := hy_mem_conjL.1
    rw [mem_pointwise_smul_iff_inv_smul_mem] at hy_mem'
    rwa [show (conj c)⁻¹ • y = c⁻¹ * y * c from by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]] at hy_mem'
  obtain ⟨δ', σ', hl0_eq⟩ := hl0_mem_L
  -- orderOf y coprime to p
  obtain ⟨k0, hk0_mem, hk0_eq⟩ := hy_mem
  have horder_dvd : orderOf y ∣ Nat.card K := by
    have heq1 : orderOf y = orderOf k0 := by
      rw [← hk0_eq]
      exact orderOf_injective G.subtype (Subgroup.subtype_injective G) k0
    have heq2 : orderOf k0 = orderOf (⟨k0, hk0_mem⟩ : K) :=
      orderOf_injective K.subtype (Subgroup.subtype_injective K) ⟨k0, hk0_mem⟩
    rw [heq1, heq2]
    exact orderOf_dvd_natCard _
  have hcop_y : Nat.Coprime (orderOf y) p := hcop.coprime_dvd_left horder_dvd
  -- regularity of `l0`: δ' ≠ 1 and δ' ≠ -1
  have hδ'_ne_one : δ' ≠ 1 := by
    rintro rfl
    have hl0' : l0 = s σ' := by rw [← hl0_eq, d_one_eq_one, one_mul]
    by_cases hσ' : σ' = 0
    · apply hy_not_center
      rw [hy_eq, hl0', hσ', s_zero_eq_one, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
    · have horderyp : orderOf y = p := by
        rw [hy_eq, hl0', orderOf_conj, order_s_eq_char σ' hσ']
      have hp1 : p = 1 := by
        have h1 := hcop_y.gcd_eq_one
        rw [horderyp] at h1
        rwa [Nat.gcd_self] at h1
      exact hp'.out.ne_one hp1
  have hδ'_ne_neg_one : δ' ≠ -1 := by
    rintro rfl
    have hl0' : l0 = - s σ' := by
      rw [← hl0_eq]
      show d (-1) * s σ' = - s σ'
      rw [← neg_one_mul (s σ'), ← d_neg_one_eq_neg_one]
    by_cases hσ' : σ' = 0
    · apply hy_not_center
      have hmemcenter : (-(1 : SL(2,F))) ∈ center SL(2,F) := by
        rw [center_SL2_eq_Z]; exact neg_one_mem_Z
      have hcomm : c * (-1 : SL(2,F)) = (-1 : SL(2,F)) * c := Subgroup.mem_center_iff.mp hmemcenter c
      have hccc : c * (-1 : SL(2,F)) * c⁻¹ = -1 := by
        rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      rw [hy_eq, hl0', hσ', s_zero_eq_one, hccc]
      exact hmemcenter
    · have hpdvd : p ∣ orderOf y := by
        rw [hy_eq, hl0', orderOf_conj]
        exact orderOf_neg_s_dvd_of_ne_zero hσ'
      have hgcd : p ∣ Nat.gcd (orderOf y) p := Nat.dvd_gcd hpdvd dvd_rfl
      rw [hcop_y] at hgcd
      exact hp'.out.one_lt.ne' (Nat.dvd_one.mp hgcd)
  have hl0_reg : (l0 : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ (l0 : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    rw [← hl0_eq]
    have h00 : (d δ' * s σ' : SL(2,F)) 0 0 = (δ' : F) := by simp [d, s]
    have h11 : (d δ' * s σ' : SL(2,F)) 1 1 = (δ' : F)⁻¹ := by simp [d, s]
    rw [h00, h11]
    intro heq
    rcases (Field.self_eq_inv_iff (δ' : F) (Units.ne_zero δ')).mp heq with h1 | h1
    · exact hδ'_ne_one (Units.ext h1)
    · exact hδ'_ne_neg_one (Units.ext h1)
  have hcentralizer_l0 : centralizer {l0} ≤ L F :=
    centralizer_le_L_of_lower_triangular_regular ⟨δ', σ', hl0_eq⟩ hl0_reg
  -- `A ≤ (conj c • L F) ⊓ G`
  have hA_le_conjL : A ≤ (conj c • L F) ⊓ G := by
    rintro a ⟨ha_cent, ha_G⟩
    refine ⟨?_, ha_G⟩
    show a ∈ (conj c • L F : Subgroup SL(2,F))
    rw [mem_pointwise_smul_iff_inv_smul_mem, show (conj c)⁻¹ • a = c⁻¹ * a * c from by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]]
    apply hcentralizer_l0
    refine mem_centralizer_iff.mpr fun w hw => ?_
    simp only [Set.mem_singleton_iff] at hw
    subst hw
    have hay : a * y = y * a := (mem_centralizer_iff.mp ha_cent y rfl).symm
    have step1 : c⁻¹ * (y * a) * c = l0 * (c⁻¹ * a * c) := by rw [hy_eq]; group
    have step2 : c⁻¹ * (a * y) * c = (c⁻¹ * a * c) * l0 := by rw [hy_eq]; group
    rw [← step1, ← step2, hay]
  -- `L F` normalizes `S F`, transported by `conj c`
  have hL_le_norm_conjS : (conj c • L F) ≤ normalizer ((conj c • S F : Subgroup SL(2,F)) : Set SL(2,F)) := by
    rw [normalizer_conj_smul_eq_conj_smul_normalizer]
    intro x hx
    rw [mem_pointwise_smul_iff_inv_smul_mem] at hx ⊢
    exact L_le_normalizer_S hx
  have hA_le_normQ' : A ≤ normalizer ((map G.subtype Q.toSubgroup : Set SL(2,F))) := by
    have hstep : A ≤ normalizer ((conj c • S F : Subgroup SL(2,F)) : Set SL(2,F)) ⊓ normalizer (G : Set SL(2,F)) := by
      rintro a ha
      obtain ⟨ha1, ha2⟩ := hA_le_conjL ha
      exact ⟨hL_le_norm_conjS ha1, le_normalizer ha2⟩
    refine hstep.trans ?_
    rw [hQ'_eq]
    exact le_normalizer_inf (conj c • S F) G
  -- combine to get `A ≤ (image of Q) ⊔ (image of K)`
  have hA_le_QK : A ≤ map G.subtype Q.toSubgroup ⊔ map G.subtype K := by
    have hstep1 : A ≤ normalizer ((map G.subtype Q.toSubgroup : Set SL(2,F))) ⊓ G :=
      fun a ha => ⟨hA_le_normQ' ha, ha.2⟩
    rw [normalizer_inf_le_eq_normalizer_subgroupOf hQ'_le_G, hQ'_subgroupOf, hNG,
      Subgroup.map_sup] at hstep1
    exact hstep1
  -- Step e: `A ⊓ (image of Q) = ⊥`
  have hA_inf_Q'_eq_bot : A ⊓ map G.subtype Q.toSubgroup = ⊥ := by
    rw [eq_bot_iff_forall]
    intro u hu
    by_contra hune
    obtain ⟨huA, huQ'⟩ := hu
    have huQ'' : u ∈ (conj c • S F : Subgroup SL(2,F)) ⊓ G := hQ'_eq ▸ huQ'
    have hu_conjS : u ∈ conj c • S F := huQ''.1
    rw [mem_pointwise_smul_iff_inv_smul_mem, show (conj c)⁻¹ • u = c⁻¹ * u * c from by
      rw [MulAut.smul_def, MulAut.conj_inv_apply]] at hu_conjS
    obtain ⟨τ, hτ⟩ := hu_conjS
    have hτne : τ ≠ 0 := by
      intro hτ0
      apply hune
      have h1 : c⁻¹ * u * c = 1 := by rw [← hτ, hτ0, s_zero_eq_one]
      calc u = c * (c⁻¹ * u * c) * c⁻¹ := by group
        _ = c * 1 * c⁻¹ := by rw [h1]
        _ = 1 := by group
    have huy : u * y = y * u := ((mem_centralizer_iff.mp huA.1) y rfl).symm
    have hcomm : (s τ) * l0 = l0 * (s τ) := by
      rw [hτ]
      have step1 : c⁻¹ * (u * y) * c = (c⁻¹ * u * c) * l0 := by rw [hy_eq]; group
      have step2 : c⁻¹ * (y * u) * c = l0 * (c⁻¹ * u * c) := by rw [hy_eq]; group
      rw [← step1, ← step2, huy]
    have hl0_mem_centralizer : l0 ∈ centralizer {s τ} := by
      refine mem_centralizer_iff.mpr fun w hw => ?_
      simp only [Set.mem_singleton_iff] at hw
      subst hw
      exact hcomm
    rw [centralizer_s_eq_SZ hτne] at hl0_mem_centralizer
    simp only [SZ, mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_union,
      Set.mem_setOf_eq] at hl0_mem_centralizer
    rw [← hl0_eq] at hl0_mem_centralizer
    rcases hl0_mem_centralizer with ⟨μ, hμ⟩ | ⟨μ, hμ⟩
    · apply hδ'_ne_one
      have h00 := congrArg (fun M : SL(2,F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hμ
      simp [d, s] at h00
      exact Units.ext h00.symm
    · apply hδ'_ne_neg_one
      have h00 := congrArg (fun M : SL(2,F) => (M : Matrix (Fin 2) (Fin 2) F) 0 0) hμ
      simp [d, s] at h00
      exact Units.ext h00.symm
  -- conclude `A = image of K` via the Dedekind/Frattini argument inside `Nsub`
  set Nsub : Subgroup SL(2,F) := map G.subtype Q.toSubgroup ⊔ map G.subtype K with hNsub_def
  have hKimg_le_normalizerQ' : map G.subtype K ≤ normalizer (map G.subtype Q.toSubgroup : Set SL(2,F)) := by
    have heq : map G.subtype (normalizer (Q.toSubgroup : Set ↥G))
        = normalizer (map G.subtype Q.toSubgroup : Set SL(2,F)) ⊓ G := by
      rw [normalizer_inf_le_eq_normalizer_subgroupOf hQ'_le_G, hQ'_subgroupOf]
    exact hKimg_le_normalizer.trans (heq ▸ inf_le_left)
  have hQ'_le_normalizerQ' : map G.subtype Q.toSubgroup ≤ normalizer (map G.subtype Q.toSubgroup : Set SL(2,F)) :=
    le_normalizer
  have hNsub_le_normalizerQ' : Nsub ≤ normalizer (map G.subtype Q.toSubgroup : Set SL(2,F)) :=
    sup_le hQ'_le_normalizerQ' hKimg_le_normalizerQ'
  haveI hQ'_normal : ((map G.subtype Q.toSubgroup).subgroupOf Nsub).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hNsub_le_normalizerQ'
  have hcodisjoint := codisjoint_subgroupOf_sup (map G.subtype Q.toSubgroup) (map G.subtype K)
  rw [← hNsub_def] at hcodisjoint
  rw [codisjoint_iff, sup_comm] at hcodisjoint
  have hmulnormal := Subgroup.mul_normal ((map G.subtype K).subgroupOf Nsub)
    ((map G.subtype Q.toSubgroup).subgroupOf Nsub)
  rw [hcodisjoint] at hmulnormal
  have hA_le_Kimg : A ≤ map G.subtype K := by
    intro a ha
    have haNsub : a ∈ Nsub := hA_le_QK ha
    have hatop : (⟨a, haNsub⟩ : ↥Nsub) ∈ (⊤ : Subgroup ↥Nsub) := mem_top _
    rw [← SetLike.mem_coe, hmulnormal, Set.mem_mul] at hatop
    obtain ⟨k, hk_mem, q, hq_mem, hkq⟩ := hatop
    have hkq' : (k : SL(2,F)) * (q : SL(2,F)) = a := congrArg Subtype.val hkq
    have hk_memKimg : (k : SL(2,F)) ∈ map G.subtype K := hk_mem
    have hq_memQ' : (q : SL(2,F)) ∈ map G.subtype Q.toSubgroup := hq_mem
    have hqA : (q : SL(2,F)) ∈ A := by
      have hkA : (k : SL(2,F)) ∈ A := hKimg_le_A hk_memKimg
      have hqeq : (q : SL(2,F)) = (k : SL(2,F))⁻¹ * a := by rw [← hkq']; group
      rw [hqeq]
      exact A.mul_mem (A.inv_mem hkA) ha
    have hq_bot : (q : SL(2,F)) ∈ A ⊓ map G.subtype Q.toSubgroup := ⟨hqA, hq_memQ'⟩
    rw [hA_inf_Q'_eq_bot, mem_bot] at hq_bot
    rw [← hkq', hq_bot, mul_one]
    exact hk_memKimg
  have hA_eq_Kimg : A = map G.subtype K := le_antisymm hA_le_Kimg hKimg_le_A
  rwa [hA_eq_Kimg] at hA_mem
