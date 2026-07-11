import ClassificationOfSubgroups.Ch4_PGLIsoPSLOverAlgClosedField.ProjectiveGeneralLinearGroup
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_A_MaximalAbelianSubgroup
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_B_MaximalAbelianSubgroup
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S4_CaseArithmetic
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S5_NumericClassEquation
import ClassificationOfSubgroups.Ch7_GroupRecognition
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.GroupTheory.Complement
import Mathlib.GroupTheory.Nilpotent
import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.GroupTheory.SpecificGroups.Quaternion
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

set_option linter.style.longLine true
set_option maxHeartbeats 0

open Matrix Subgroup LinearMap Ch7GroupRecognition MulAut

open scoped MatrixGroups Pointwise


/- Lemma 3.1 -/
-- The original statement here was false: `H < K` gives `H ≤ K ≤ normalizer K`
-- (`Subgroup.le_normalizer`), directly contradicting `¬ H ≤ normalizer K`.
-- Restated to match Butler's actual Lemma 3.1 (`case2q`, tex ~line 1277): a proper
-- subgroup of a finite `p`-group `K` is strictly contained in its normalizer inside `K`.
--
-- Further generalized (`SL(2,F)`/`CharP F p` dropped in favour of an arbitrary group `L`, with
-- the `IsPGroup` prime `p` an independent variable rather than tied to `F`'s characteristic):
-- inspecting the proof shows `F`, the ambient `SL(2,F)`-subgroup `G`, and `CharP F p` are never
-- actually used -- the statement is pure finite-group theory (a proper subgroup of a nilpotent
-- group is properly contained in its normalizer, `Group.normalizerCondition_of_isNilpotent`,
-- applied to the `p`-group `K`), with no dependence on `F`'s characteristic matching `p`. The
-- original, oddly-specific hypotheses silently prevented applying this lemma to a `p`-subgroup
-- for a prime `p` *different* from the field's own characteristic (needed below in `case_II`'s
-- `g1 = 2` branch, for a `2`-subgroup argument while the ambient field has odd characteristic);
-- this lemma is unreferenced anywhere in the repo (checked via grep), so generalizing it is safe.
lemma IsPGroup.lt_normalizer_subgroupOf {L : Type*} [Group L] {p : ℕ} [Fact (Nat.Prime p)]
  (H K : Subgroup L) [Finite K] (hK : IsPGroup p K) (H_lt_K : H < K) :
    H.subgroupOf K < normalizer ((H.subgroupOf K : Subgroup K) : Set K) := by
  have hnc : NormalizerCondition K := Group.normalizerCondition_of_isNilpotent (G := K)
    (h := hK.isNilpotent)
  have hne : H.subgroupOf K ≠ ⊤ :=
    fun heq => H_lt_K.ne (le_antisymm H_lt_K.le (Subgroup.subgroupOf_eq_top.mp heq))
  exact hnc _ (lt_top_iff_ne_top.mpr hne)

open MaximalAbelianSubgroup

-- `subgroupOf` (unconditionally, unlike `subgroupOf_sup`) distributes over `⊓`, since it is
-- defined as `comap` of the inclusion, and `comap` always preserves `⊓`.
lemma subgroupOf_inf_eq {L : Type*} [Group L] (A B H : Subgroup L) :
    (A ⊓ B).subgroupOf H = A.subgroupOf H ⊓ B.subgroupOf H := by
  rw [← comap_subtype, ← comap_subtype, ← comap_subtype, comap_inf]

/- Lemma 3.2 -/
-- Butler's Lemma (tex `caseVlemma`, lines 1306-1349) additionally assumes `Q ∩ K = {1}` and
-- `[N_G(K) : K] = 2`; both are used essentially in the proof (the first to get
-- `K ≅ G/Q`, the second to pin down `|Q ∩ N_G(K)| = 2`). Neither hypothesis is derivable from
-- the statement as originally given, so they are restored here as `hQcapK` and `hNK`
-- (using the `relIndex`-of-`subgroupOf` idiom from `S2_B_MaximalAbelianSubgroup`'s
-- `of_index_normalizer_eq_two`). This lemma is not referenced elsewhere in the repo
-- (checked via grep), so strengthening its hypotheses is safe.
lemma Sylow.not_normal_subgroup_of_G {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] (G K : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G)
  (hK : K ∈ MaximalAbelianSubgroupsOf G)
  (hQK : map G.subtype (normalizer (Q.toSubgroup : Set ↥G)) = (map G.subtype Q.toSubgroup) ⊔ K)
  (hQcapK : (map G.subtype Q.toSubgroup) ⊓ K = ⊥)
  (hNK : relIndex (K.subgroupOf G) (normalizer ((K.subgroupOf G : Subgroup ↥G) : Set ↥G)) = 2) :
  ¬ Normal Q.toSubgroup := by
  intro hnormal
  -- Work with the "internal" (i.e. `Subgroup ↥G`) picture throughout.
  set K' : Subgroup ↥G := K.subgroupOf G with hK'_def
  set Q' : Subgroup SL(2,F) := map G.subtype Q.toSubgroup with hQ'_def
  have hK_le_G : K ≤ G := hK.right
  have hQ'_le_G : Q' ≤ G := Subgroup.map_subtype_le Q.toSubgroup
  -- `Q` is normal in `G`, so `N_G(Q) = G`.
  have hNQ : normalizer (Q.toSubgroup : Set ↥G) = ⊤ := @normalizer_eq_top _ _ Q.toSubgroup hnormal
  rw [hNQ] at hQK
  have hGtop : map G.subtype (⊤ : Subgroup ↥G) = G := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hGtop] at hQK
  -- `hQK : G = Q' ⊔ K`; push it down to `↥G` via `subgroupOf G`.
  have hQ'_subgroupOf : Q'.subgroupOf G = Q.toSubgroup :=
    Subgroup.comap_map_eq_self_of_injective (G.subtype_injective) Q.toSubgroup
  have hQK_internal : (⊤ : Subgroup ↥G) = Q.toSubgroup ⊔ K' := by
    have := congrArg (Subgroup.subgroupOf · G) hQK
    rwa [Subgroup.subgroupOf_self, Subgroup.subgroupOf_sup hQ'_le_G hK_le_G,
      hQ'_subgroupOf] at this
  have hKQ_sup : K' ⊔ Q.toSubgroup = ⊤ := by rw [sup_comm]; exact hQK_internal.symm
  -- Similarly push the disjointness hypothesis down to `↥G`.
  have hQK_inf : Q.toSubgroup ⊓ K' = ⊥ := by
    have := congrArg (Subgroup.subgroupOf · G) hQcapK
    rw [subgroupOf_inf_eq, hQ'_subgroupOf] at this
    rwa [Subgroup.bot_subgroupOf] at this
  have hKQ_inf : K' ⊓ Q.toSubgroup = ⊥ := by rwa [inf_comm] at hQK_inf
  -- `K'` and `Q.toSubgroup` are complementary subgroups of `↥G`.
  have hcomp : K'.IsComplement' Q.toSubgroup := by
    apply isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hKQ_inf)
    have := Subgroup.mul_normal K' Q.toSubgroup
    rw [hKQ_sup, Subgroup.coe_top] at this
    exact this.symm
  haveI : Q.toSubgroup.Normal := hnormal
  have hquotEquiv : (↥G ⧸ Q.toSubgroup) ≃* K' := hcomp.QuotientMulEquiv
  -- `N := N_{↥G}(K')`.
  set N : Subgroup ↥G := normalizer (K' : Set ↥G) with hN_def
  have hK'_le_N : K' ≤ N := K'.le_normalizer
  -- The quotient map `↥G → ↥G ⧸ Q.toSubgroup`, restricted to `N`.
  let φ : ↥G →* (↥G ⧸ Q.toSubgroup) := QuotientGroup.mk' Q.toSubgroup
  let ψ : ↥N →* (↥G ⧸ Q.toSubgroup) := φ.comp N.subtype
  have hker : ψ.ker = Q.toSubgroup.subgroupOf N := by
    show (φ.comp N.subtype).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  -- `K'` alone already surjects onto `↥G ⧸ Q.toSubgroup`, so a fortiori so does `N`.
  have hQmap_bot : Q.toSubgroup.map φ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hKmap : K'.map φ = ⊤ := by
    have hsup := congrArg (Subgroup.map φ) hKQ_sup
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective _),
      hQmap_bot, sup_bot_eq] at hsup
    exact hsup
  have hNmap : N.map φ = ⊤ := le_antisymm le_top
    (hKmap ▸ Subgroup.map_mono hK'_le_N)
  have hrange : ψ.range = ⊤ := by
    show (φ.comp N.subtype).range = ⊤
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hNmap
  -- First Isomorphism Theorem: `N ⧸ ker ψ ≃* range ψ = ⊤ ≃* (↥G ⧸ Q.toSubgroup) ≃* K'`.
  have hcard_quot : Nat.card (↥N ⧸ ψ.ker) = Nat.card K' := by
    have h1 : Nat.card (↥N ⧸ ψ.ker) = Nat.card ψ.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    rw [h1, hrange]
    rw [Nat.card_congr (Subgroup.topEquiv (G := ↥G ⧸ Q.toSubgroup)).toEquiv]
    exact Nat.card_congr hquotEquiv.toEquiv
  have hcard_N_via_ker : Nat.card N = Nat.card K' * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker, hcard_quot]
  -- `K' ⊴ N` (it is normal in its own normalizer) with `[N : K'] = 2`.
  have hcard_N_via_K' : Nat.card N = 2 * Nat.card K' := by
    have h1 : Nat.card N = Nat.card (↥N ⧸ K'.subgroupOf N) * Nat.card (K'.subgroupOf N) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card (K'.subgroupOf N) = Nat.card K' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'_le_N).toEquiv
    have h3 : Nat.card (↥N ⧸ K'.subgroupOf N) = K'.relIndex N := rfl
    rw [h2, h3, hNK] at h1
    exact h1
  have hcard_K'_pos : 0 < Nat.card K' := Nat.card_pos
  have hcard_ker : Nat.card ψ.ker = 2 := by
    have heq : Nat.card K' * Nat.card ψ.ker = Nat.card K' * 2 := by
      rw [hcard_N_via_ker] at hcard_N_via_K'
      rw [hcard_N_via_K']; ring
    exact mul_left_cancel₀ hcard_K'_pos.ne' heq
  -- `ker ψ = Q.toSubgroup.subgroupOf N` has order `2`, hence is nontrivial.
  have hker_ne_bot : ψ.ker ≠ ⊥ := by
    intro h
    rw [h] at hcard_ker
    simp at hcard_ker
  obtain ⟨x, hx_ne_one⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker_ne_bot
  have hx_mem : (x : ↥N) ∈ ψ.ker := x.2
  set x0 : ↥G := ((x : ↥N) : ↥G) with hx0_def
  have hx0_ne_one : x0 ≠ 1 := by
    intro h
    apply hx_ne_one
    exact Subtype.ext (Subtype.ext h)
  have hx0_mem_Q : x0 ∈ Q.toSubgroup := by
    have h' : (x : ↥N) ∈ Q.toSubgroup.subgroupOf N := hker ▸ hx_mem
    simpa [hx0_def, Subgroup.mem_subgroupOf] using h'
  have hx0_notin_K' : x0 ∉ K' := by
    intro hmem
    have : x0 ∈ K' ⊓ Q.toSubgroup := ⟨hmem, hx0_mem_Q⟩
    rw [hKQ_inf] at this
    exact hx0_ne_one (Subgroup.mem_bot.mp this)
  -- `x0` commutes with every element of `K'`.
  have hx0_comm : ∀ y ∈ K', x0 * y = y * x0 := by
    intro y hy
    have hy_mem_N : y ∈ N := hK'_le_N hy
    set b : ↥N := ⟨y, hy_mem_N⟩ with hb_def
    have hb_mem_K'N : b ∈ K'.subgroupOf N := by simpa [hb_def, Subgroup.mem_subgroupOf]
    have hconj1 : x * b * x⁻¹ ∈ K'.subgroupOf N :=
      (Subgroup.normal_in_normalizer (H := K')).conj_mem b hb_mem_K'N x
    have hconj2 : b * x⁻¹ * b⁻¹ ∈ ψ.ker :=
      (MonoidHom.normal_ker ψ).conj_mem x⁻¹ (Subgroup.inv_mem _ hx_mem) b
    have hmem1 : x * b * x⁻¹ * b⁻¹ ∈ K'.subgroupOf N :=
      mul_mem hconj1 (Subgroup.inv_mem _ hb_mem_K'N)
    have hmem2 : x * b * x⁻¹ * b⁻¹ ∈ ψ.ker := by
      have : x * (b * x⁻¹ * b⁻¹) = x * b * x⁻¹ * b⁻¹ := by group
      rw [← this]
      exact mul_mem hx_mem hconj2
    have hmem : x * b * x⁻¹ * b⁻¹ ∈ K'.subgroupOf N ⊓ ψ.ker := ⟨hmem1, hmem2⟩
    have hK'N_inf_ker : K'.subgroupOf N ⊓ ψ.ker = ⊥ := by
      rw [hker]
      have := congrArg (Subgroup.subgroupOf · N) hKQ_inf
      rwa [subgroupOf_inf_eq, Subgroup.bot_subgroupOf] at this
    rw [hK'N_inf_ker] at hmem
    have : x * b * x⁻¹ * b⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    have hcommN : x * b = b * x := by
      have h' : x * b * x⁻¹ * b⁻¹ * b * x = 1 * b * x := by rw [this]
      simpa [mul_assoc] using h'
    have := congrArg (Subtype.val (p := fun a => a ∈ N)) hcommN
    simpa [hb_def, hx0_def] using this
  -- Hence `K' ⊔ ⟨x0⟩` is abelian, strictly containing `K'` -- contradicting maximality.
  set k : Set ↥G := (K' : Set ↥G) ∪ {x0} with hk_def
  have hcomm_k : ∀ a ∈ k, ∀ b ∈ k, a * b = b * a := by
    haveI := hK.left.1
    rintro a (ha | ha) b (hb | hb)
    · exact setLike_mul_comm ha hb
    · simp only [Set.mem_singleton_iff] at hb; subst hb
      exact (hx0_comm a ha).symm
    · simp only [Set.mem_singleton_iff] at ha; subst ha
      exact hx0_comm b hb
    · simp only [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
  haveI hclosure_comm : IsMulCommutative (closure k) := Subgroup.isMulCommutative_closure hcomm_k
  have hK'_le_closure : K' ≤ closure k := by
    rw [← Subgroup.closure_eq K']
    exact Subgroup.closure_mono (Set.subset_union_left)
  have hclosure_le : closure k ≤ K' := hK.left.2 hclosure_comm hK'_le_closure
  have hclosure_eq : closure k = K' := le_antisymm hclosure_le hK'_le_closure
  have hx0_mem_closure : x0 ∈ closure k :=
    subset_closure (Set.mem_union_right _ rfl)
  rw [hclosure_eq] at hx0_mem_closure
  exact hx0_notin_K' hx0_mem_closure

/- Lemma 3.3 -/
-- `R` is unused elsewhere in this development, so it is restructured here as a `Subfield F`
-- (rather than a bare `Set F`): the fixed field of the `k`-th iterated Frobenius, i.e. the
-- equalizer of `x ↦ x ^ p ^ k` and `id`. This is definitionally the set
-- `{x : F | x ^ p ^ k - x = 0}` (via `sub_eq_zero`), and packaging it as a `Subfield` gets
-- the `Field` instance for free from `Subfield.toField`.
def R (F : Type*) [Field F] (p : ℕ) [Fact (Nat.Prime p)] [CharP F p] (k : ℕ+) : Subfield F :=
  RingHom.eqLocusField (iterateFrobenius F p (k : ℕ)) (RingHom.id F)

instance field_R {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] {k : ℕ+} : Field (R F p k) := Subfield.toField (R F p k)

/- Lemma 3.4 -/
noncomputable instance Fintype_GL {F : Type*} {n : ℕ} [Field F] [Fintype F] :
    Fintype (GL (Fin n) F) := by
  exact Fintype.ofFinite (GL (Fin n) F)

theorem GL_card {q : ℕ} {F : Type*} [Field F] [Fintype F] (hq : Fintype.card F = q) :
    Fintype.card (GL (Fin 2) F)= (q ^ 2 - 1) * (q ^ 2 - q) := by
  rw [← Nat.card_eq_fintype_card]
  rw [Matrix.card_GL_field]
  simp [hq]

-- Matrix.card_SL_field seems to be missing from mathlib
-- NOTE: as originally stated (no hypothesis on `n`) this is false at `n = 0` whenever
-- `Fintype.card 𝔽 > 2`: `GL (Fin 0) 𝔽` and `SL (Fin 0) 𝔽` both have cardinality `1`, but
-- `1 / (Fintype.card 𝔽 - 1) = 0 ≠ 1` by `ℕ`-division. Restated with `n ≠ 0` (the only
-- caller, `SL_card` below, uses `n = 2`).
lemma card_SL_field {𝔽 : Type*} [Field 𝔽] [Fintype 𝔽] (n : ℕ) (hn : n ≠ 0) :
  Nat.card (SL (Fin n) 𝔽) = Nat.card (GL (Fin n) 𝔽) / (Fintype.card 𝔽 - 1) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have hsurj : Function.Surjective (GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ) :=
    GeneralLinearGroup.det_surjective
  -- `SL (Fin n) 𝔽` is in bijection with `ker (det : GL (Fin n) 𝔽 →* 𝔽ˣ)`.
  have hequiv : Nat.card (SL (Fin n) 𝔽)
      = Nat.card (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ)) := by
    apply Nat.card_congr
    exact
    { toFun := fun A => ⟨(A : GL (Fin n) 𝔽), by
          rw [MonoidHom.mem_ker]; exact SpecialLinearGroup.coeToGL_det A⟩
      invFun := fun B => ⟨(B.1 : Matrix (Fin n) (Fin n) 𝔽), by
          have h : GeneralLinearGroup.det (B.1 : GL (Fin n) 𝔽) = 1 := B.2
          have h2 := congrArg Units.val h
          simpa [GeneralLinearGroup.val_det_apply] using h2⟩
      left_inv := fun A => by
          apply Subtype.ext; rfl
      right_inv := fun B => by
          apply Subtype.ext; apply Units.ext; rfl }
  have hcard : Nat.card (GL (Fin n) 𝔽) =
      Nat.card (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ))
        * (Fintype.card 𝔽 - 1) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (MonoidHom.ker (GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ)),
      Nat.card_congr (QuotientGroup.quotientKerEquivRange
        (GeneralLinearGroup.det : GL (Fin n) 𝔽 →* 𝔽ˣ)).toEquiv,
      MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_units,
      Nat.card_eq_fintype_card, mul_comm]
  have hpos : 0 < Fintype.card 𝔽 - 1 := by
    have := Fintype.one_lt_card (α := 𝔽); omega
  rw [hequiv]
  exact (Nat.div_eq_of_eq_mul_left hpos hcard).symm

noncomputable instance Fintype_SL {F : Type*} {n : ℕ} [Field F] [Fintype F] :
    Fintype (SL (Fin n) F) := by
  exact Fintype.ofFinite (SL(n, F))

theorem SL_card {q : ℕ} {F : Type*} [Field F] [Fintype F]
    (hq : Fintype.card F = q) (hqone: q > 1): Fintype.card SL(2, F) = (q ^ 2 - 1) * q := by
  rw [← Nat.card_eq_fintype_card]
  rw [card_SL_field 2 (by norm_num)]
  simp [hq]
  rw [GL_card hq]
  have : q ^ 2 - q = q * (q - 1) := by
    rw [Nat.mul_sub_left_distrib, pow_two]
    simp
  rw [this]
  ring_nf
  apply Nat.mul_div_left (q * (q ^ 2 - 1)) (by exact Nat.zero_lt_sub_of_lt hqone)

/- Lemma 3.5. Correspondence theorem -/
#check QuotientGroup.comapMk'OrderIso

def Isomorphic (G H : Type*) [Group G] [Group H] :=
  Nonempty (G ≃* H)

open CaseArithmetic

/-! ### `IsElementaryAbelian` transport lemmas, and: every Sylow `p`-subgroup is elementary abelian

`BridgeData.hSylow`'s Sylow-type witness `Q` (`S5_NumericClassEquation`) does not itself carry an
`IsElementaryAbelian` fact -- only the maximal abelian subgroup `A = Q ⊔ Z` a Sylow-type class was
built from does (`isCyclic_and_card_coprime_charP_or_eq_Q_sup_Z`, via `S2_A`'s internal
construction) -- yet `case_I`'s own conclusion needs exactly `IsElementaryAbelian p Q.toSubgroup`
for an *arbitrary* Sylow `p`-subgroup `Q` of `G` (not one tied to a witness maximal abelian
subgroup). This is bridged here: `S2_B_MaximalAbelianSubgroup.exists_conj_Sylow_eq_S_inf_and_
normalizer_le_L` shows any nontrivial Sylow `p`-subgroup's image in `SL(2,F)` equals `(conj c • S
F) ⊓ G` for some `c`, i.e. is (isomorphic to) a subgroup of a conjugate of the shear subgroup `S
F`, which is commutative of exponent `p` (`IsMulCommutative_S`, `order_s_eq_char`) -- hence
elementary abelian -- unconditionally (this fact does not depend on `Q` arising from any
particular maximal abelian subgroup). -/

/-- `IsElementaryAbelian` transports along an injective `MonoidHom`. -/
lemma IsElementaryAbelian_map_of_injective {G H : Type*} [Group G] [Group H] {p : ℕ}
    {K : Subgroup G} (hK : IsElementaryAbelian p K) (f : G →* H) (hf : Function.Injective f) :
    IsElementaryAbelian p (K.map f) := by
  haveI := hK.1
  refine ⟨inferInstance, ?_⟩
  rintro ⟨y, hy⟩ hyne
  obtain ⟨x, hx, rfl⟩ := hy
  have hxne : (⟨x, hx⟩ : K) ≠ 1 := by
    intro h
    apply hyne
    have hx1 : x = 1 := congrArg Subtype.val h
    apply Subtype.ext
    simp [hx1]
  have hxord : orderOf x = p := (orderOf_coe (⟨x, hx⟩ : K)).trans (hK.2 ⟨x, hx⟩ hxne)
  have hfxord : orderOf (f x) = p := (orderOf_injective f hf x).trans hxord
  exact (orderOf_coe _).symm.trans hfxord

/-- `IsElementaryAbelian` is inherited by any subgroup of an elementary abelian subgroup. -/
lemma IsElementaryAbelian_of_le {G : Type*} [Group G] {p : ℕ} {H K : Subgroup G}
    (hK : IsElementaryAbelian p K) (hle : H ≤ K) : IsElementaryAbelian p H := by
  haveI := hK.1
  refine ⟨isCommutative_of_le_isCommutative H K hle, ?_⟩
  intro h hne
  have hne' : (⟨(h : G), hle h.2⟩ : K) ≠ 1 := by
    intro hcon
    have heq : (h : G) = 1 := congrArg Subtype.val hcon
    exact hne (Subtype.ext heq)
  have := hK.2 ⟨(h : G), hle h.2⟩ hne'
  rwa [orderOf_mk] at this ⊢

/-- Any nontrivial Sylow `p`-subgroup of a finite `G ≤ SL(2,F)` (`p` the characteristic) is
elementary abelian. See the module docstring above for the construction. -/
lemma isElementaryAbelian_of_sylow {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F]
    [Fact (Nat.Prime p)] [CharP F p] (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G)
    (hQ : Q.toSubgroup ≠ ⊥) : IsElementaryAbelian p Q.toSubgroup := by
  obtain ⟨c, hc, -⟩ := exists_conj_Sylow_eq_S_inf_and_normalizer_le_L G Q hQ
  have hSelemAb : IsElementaryAbelian p (SpecialSubgroups.S F) := by
    refine ⟨inferInstance, ?_⟩
    rintro ⟨x, σ, hσ⟩ hne
    subst hσ
    have hσne : σ ≠ 0 := by
      rintro rfl
      exact hne (Subtype.ext SpecialMatrices.s_zero_eq_one)
    exact (orderOf_coe _).symm.trans (SpecialMatrices.order_s_eq_char σ hσne)
  have hconjSF : MulAut.conj c • SpecialSubgroups.S F
      = (SpecialSubgroups.S F).map (MulAut.conj c).toMonoidHom := rfl
  have hconjElemAb : IsElementaryAbelian p (MulAut.conj c • SpecialSubgroups.S F) := by
    rw [hconjSF]
    exact IsElementaryAbelian_map_of_injective hSelemAb _ (MulAut.conj c).injective
  have hinfElemAb : IsElementaryAbelian p ((MulAut.conj c • SpecialSubgroups.S F) ⊓ G) :=
    IsElementaryAbelian_of_le hconjElemAb inf_le_left
  have hQmapElemAb : IsElementaryAbelian p (Q.toSubgroup.map G.subtype) := hc ▸ hinfElemAb
  have hsubgroupOf : (Q.toSubgroup.map G.subtype).subgroupOf G = Q.toSubgroup :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective G) Q.toSubgroup
  rw [← hsubgroupOf]
  exact IsElementaryAbelian.subgroupOf (Q.toSubgroup.map G.subtype) G hQmapElemAb

/-! ### The six cases of the Maximal Abelian Subgroup Class Equation (tex 1421-2160)

Each of the six lemmas below (`case_I` ... `case_VI`) corresponds to one of Butler's six cases of
the class equation `\eqref{classeq}`, indexed by `(s,t) ∈ {(1,0),(1,1),(0,0),(0,1),(0,2),(0,3)}`
(`CaseArithmetic.case_enumeration`, tex ~1206-1270). The class-data hypothesis `heq` in each case
packages "`G` realizes this `(s,t)` case" via `CaseArithmetic.ClassEquation`, instantiated with
`g := |G|/|Z|` and `q := |Q|` for the actual Sylow `p`-subgroup `Q` of `G` (tied to `G` via the
`hg`/`hq` hypotheses), while the auxiliary integers `k` (`= |K|/|Z|` for Butler's
`K = C_G(x) ∩ G`, `x` noncentral in `Q`) and `g₁, g₂, g₃` (`= |Aᵢ|/|Z|` for the cyclic maximal
abelian subgroups) are only asserted to *exist* abstractly: this development has not yet threaded
Theorem 6.8's identification of `K`/the `Aᵢ` with concrete subgroups of `G` through to this file
(that bridge is exactly what each `case_*` proof still needs to build, on top of the pure
arithmetic already proved in `S4_CaseArithmetic`). The extra hypotheses on `k`/`g₁, …` (`hK`,
`hg_ge`, `hKle`, ...) are exactly those required by the corresponding `CaseArithmetic` theorem, so
the eventual proof can invoke it directly. Each conclusion below is Butler's literal
group-theoretic claim for that case.

Several conclusions need "`G ⧸ Q` is cyclic of order coprime to `p`"; rather than requiring a
`Normal Q.toSubgroup` *instance* to even state this (which would have to be assumed rather than
concluded), we phrase it via the existence of a complement `K` to `Q` in `G` that is cyclic of
order coprime to `p` -- this is literally Butler's `K ≅ G/Q` (e.g. tex line ~1449). -/

/-- Butler Case I (tex 1421-1450): `s = 1, t = 0`. Butler shows this forces `Q` to be a *proper*
elementary abelian normal subgroup of `G`, with `G ⧸ Q` cyclic of order coprime to `p`.

RESTATED+PROVED (justification: an earlier attempt at this lemma left `heq : ∃ k g1, ...`
exactly as in the other `case_*` lemmas -- Butler's concrete cyclic maximal abelian subgroup
`A₁` (realizing `g1`) and cyclic complement `K` to `Q` (realizing `k`) were hidden behind bare
existential numerals with no witness *subgroup* to attach `IsCyclic`/coprimality/complement
facts to, so the class-equation arithmetic (`CaseArithmetic.case_1_0`) could never be connected
back to genuine subgroups of `G` -- this is exactly the "missing bridge" that `phase 1`'s
`S5_NumericClassEquation.BridgeData` was built to supply. This restatement replaces that bare
existential with the witness data itself: `A` (a concrete subgroup realizing `g1`, carrying
exactly the facts Theorem 6.8 attaches to a coprime-type class: membership in
`MaximalAbelianSubgroupsOf`, `IsCyclic`, coprimality to `p`, and the cardinality equation) and,
guarded by `1 < q` (mirroring `BridgeData.hSylow`'s case split on whether a Sylow-type class
exists at all, specialized here to the given `Q`), the witness data Theorem 6.8(v) attaches to
the Sylow-type class: `Q` elementary abelian and a cyclic complement `K` with
`normalizer Q.toSubgroup = Q.toSubgroup ⊔ K.subgroupOf G`, disjoint from `Q`, realizing `k`.

With these witnesses in hand, both branches of `case_1_0` go through:
* `q = 1` (branch `g = g1`): `Nat.card A = Nat.card G` (from `hA_card`, `hg`, `g = g1`) and
  `A ≤ G`, so `A.subgroupOf G = ⊤` (`Subgroup.eq_top_of_card_eq`), giving a `MulEquiv`
  `A ≃* (⊤ : Subgroup G)`; `G` itself is then cyclic of order coprime to `p`, transporting
  `hA_cyc`/`hA_cop` along this equivalence -- this is literally Butler's "`G ⧸ Q = G = A₁`, which
  indeed is a cyclic group" (tex Case Ia).
* `1 < q` (branch `k = g1`, `g = q * k`): since `Q.toSubgroup` is (trivially) normal in its own
  normalizer, the disjointness/join hypotheses on `K` give (exactly the `Subgroup.mul_normal` /
  `isComplement'_of_disjoint_and_mul_eq_univ` trick already used in `Sylow.not_normal_subgroup_of_G`
  above) `Nat.card (normalizer Q.toSubgroup) = Nat.card Q.toSubgroup * Nat.card K
  = q * (Nat.card (center SL(2,F)) * k) = Nat.card (center SL(2,F)) * (q * k)
  = Nat.card (center SL(2,F)) * g = Nat.card G`, hence `normalizer Q.toSubgroup = ⊤`
  (`Subgroup.eq_top_of_card_eq`), i.e. `Normal Q.toSubgroup` (`normalizer_eq_top_iff`); this is
  Butler's "`|N_G(Q)| = |Q||K| = eg = |G|`" (tex ~1440). The complement `K.subgroupOf G` is then
  cyclic (given) and coprime to `p`: `Q` is *a* Sylow `p`-subgroup of `G`, so `Sylow.card_coprime_
  index` gives `Q.toSubgroup` coprime to its own index in `G`; once `normalizer Q.toSubgroup = ⊤`,
  that index equals `Nat.card K` exactly (`IsComplement'.index_eq_card`), and `p` divides
  `Nat.card Q.toSubgroup` (nontrivial elementary abelian `p`-group), so `Nat.Coprime p (Nat.card K)`
  follows.
PROVED. -/
lemma case_I {F : Type*} {p : ℕ} [Field F] [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q) (g1 k : ℕ)
    -- witness for the unique `s = 1` coprime-type class `A₁` (Theorem 6.8), replacing the bare
    -- numeral `g1` that the original `heq : ∃ k g1, ...` hid it behind.
    (A : Subgroup SL(2,F)) (hA_mem : A ∈ MaximalAbelianSubgroupsOf G)
    (hA_cyc : IsCyclic A) (hA_cop : Nat.Coprime (Nat.card A) p)
    (hA_card : Nat.card A = Nat.card (center SL(2,F)) * g1)
    -- witness data for the Sylow-type class realizing `q`/`k` (Theorem 6.8(v)); only needed
    -- (and only asserted) when `Q` is nontrivial. Mirrors `BridgeData.hSylow`'s second disjunct,
    -- specialized to the given `Q`.
    (hQK : 1 < q → IsElementaryAbelian p Q.toSubgroup ∧
      ∃ K : Subgroup SL(2,F), K ≤ G ∧ IsCyclic K ∧
        normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G ∧
        Disjoint Q.toSubgroup (K.subgroupOf G) ∧
        Nat.card K = Nat.card (center SL(2,F)) * k)
    (heq : 1 ≤ k ∧ 2 ≤ g1 ∧ (1 < k → k = g1) ∧
      ClassEquation g q k (s := 1) (t := 0) (fun _ => g1) (fun i => i.elim0)) :
    (⊤ : Subgroup G) ≠ Q.toSubgroup ∧ IsElementaryAbelian p Q.toSubgroup ∧
      Normal Q.toSubgroup ∧
      ∃ K : Subgroup G, IsComplement' Q.toSubgroup K ∧ IsCyclic K ∧
        Nat.Coprime p (Nat.card K) := by
  have hgpos : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with hg0 | hgpos
    · exfalso; rw [hg0, mul_zero] at hg
      have := Nat.card_pos (α := G); omega
    · exact hgpos
  have hqpos : 1 ≤ q := by have := Nat.card_pos (α := Q.toSubgroup); omega
  obtain ⟨hk_ge, hg1_ge, hKeq, heq'⟩ := heq
  rcases case_1_0 g q k g1 hgpos hqpos hk_ge hg1_ge hKeq heq' with
    ⟨hq1, hgeq⟩ | ⟨hq1lt, hkeq, hgeq⟩
  · -- **Case Ia** (`q = 1`): `Q` is trivial and `A` (realizing `g = g1`) is all of `G`.
    have hQbot : Q.toSubgroup = ⊥ := Subgroup.card_eq_one.mp (hq.trans hq1)
    have hcardA : Nat.card A = Nat.card G := by rw [hA_card, hg, hgeq]
    have hAsubgroupOf : A.subgroupOf G = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_mem.right).toEquiv]
      exact hcardA
    have e1 : A ≃* (⊤ : Subgroup G) := by
      have h := (Subgroup.subgroupOfEquivOfLe hA_mem.right).symm
      rwa [hAsubgroupOf] at h
    have htop_ne_bot : (⊤ : Subgroup G) ≠ ⊥ := by
      intro hcontra
      have h1 : Nat.card G = 1 := by
        rw [← Subgroup.card_top (G := ↥G), hcontra, Subgroup.card_bot]
      rw [hg, hgeq] at h1
      have he1 : 1 ≤ Nat.card (center SL(2,F)) := Nat.card_pos
      nlinarith [hg1_ge]
    refine ⟨by rw [hQbot]; exact htop_ne_bot, by rw [hQbot]; exact ⟨IsMulCommutative.of_comm
      (fun a b => Subsingleton.elim _ _), fun h hne => absurd (Subsingleton.elim h 1) hne⟩,
      by rw [hQbot]; infer_instance, (⊤ : Subgroup G), ?_, (MulEquiv.isCyclic e1).mp hA_cyc, ?_⟩
    · rw [hQbot]
      exact isComplement'_bot_top
    · have hcardTop : Nat.card (⊤ : Subgroup G) = Nat.card A := Nat.card_congr e1.toEquiv.symm
      rw [hcardTop]
      exact hA_cop.symm
  · -- **Case Ib** (`1 < q`): `Q` is normal in `G`, with cyclic complement `K` realizing `k`.
    obtain ⟨hQelemAb, K, hK_le, hK_cyc, hNQK, hQK_disj, hK_card⟩ := hQK hq1lt
    -- `Q.toSubgroup` is (trivially) normal in its own normalizer; combined with the
    -- disjointness/join hypotheses this makes `Q.toSubgroup`/`K.subgroupOf G` complementary
    -- inside `normalizer Q.toSubgroup` (exactly the pattern used in
    -- `Sylow.not_normal_subgroup_of_G` above).
    set Nz : Subgroup ↥G := normalizer (Q.toSubgroup : Set ↥G) with hNz_def
    set Qn : Subgroup ↥Nz := Q.toSubgroup.subgroupOf Nz with hQn_def
    set Kn : Subgroup ↥Nz := (K.subgroupOf G).subgroupOf Nz with hKn_def
    have hQ_le_Nz : Q.toSubgroup ≤ Nz := Subgroup.le_normalizer
    have hK_le_Nz : K.subgroupOf G ≤ Nz := by rw [hNQK]; exact le_sup_right
    have hsup : Qn ⊔ Kn = ⊤ := by
      have h := congrArg (Subgroup.subgroupOf · Nz) hNQK
      rw [Subgroup.subgroupOf_self, Subgroup.subgroupOf_sup hQ_le_Nz hK_le_Nz] at h
      exact h.symm
    have hdisj : Qn ⊓ Kn = ⊥ := by
      have h := congrArg (Subgroup.subgroupOf · Nz) (disjoint_iff.mp hQK_disj)
      rwa [subgroupOf_inf_eq, Subgroup.bot_subgroupOf] at h
    haveI hQn_normal : Qn.Normal := Subgroup.normal_in_normalizer (H := Q.toSubgroup)
    have hcomplement : IsComplement' Qn Kn := by
      apply isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hdisj)
      have h := Subgroup.normal_mul Qn Kn
      rw [hsup, Subgroup.coe_top] at h
      exact h.symm
    have hcard_Nz : Nat.card Qn * Nat.card Kn = Nat.card Nz := hcomplement.card_mul
    have hcard_Qn : Nat.card Qn = q := by
      rw [hQn_def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_Nz).toEquiv, hq]
    have hcard_Kn : Nat.card Kn = Nat.card K := by
      rw [hKn_def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_Nz).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le).toEquiv]
    have hcard_Nz' : Nat.card Nz = Nat.card G := by
      rw [← hcard_Nz, hcard_Qn, hcard_Kn, hK_card, hg, hgeq]; ring
    have hNz_top : Nz = ⊤ := Subgroup.eq_top_of_card_eq Nz hcard_Nz'
    have hNormalizer_top : normalizer (Q.toSubgroup : Set ↥G) = ⊤ := by
      rw [← hNz_def]; exact hNz_top
    haveI hQ_normal : Q.toSubgroup.Normal := normalizer_eq_top_iff.mp hNormalizer_top
    -- With `Q` normal, `K.subgroupOf G` is its complement in (all of) `G`.
    have hsup_top : Q.toSubgroup ⊔ K.subgroupOf G = ⊤ := by rw [← hNQK]; exact hNz_top
    have hcompG : IsComplement' Q.toSubgroup (K.subgroupOf G) := by
      apply isComplement'_of_disjoint_and_mul_eq_univ hQK_disj
      have h := Subgroup.normal_mul Q.toSubgroup (K.subgroupOf G)
      rw [hsup_top, Subgroup.coe_top] at h
      exact h.symm
    have hK_cyc' : IsCyclic (K.subgroupOf G) :=
      (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hK_le)).mpr hK_cyc
    -- coprimality of the complement to `p`: `Q` is a Sylow `p`-subgroup of `G`, so its index is
    -- coprime to its order; that index is exactly `Nat.card (K.subgroupOf G)` once `Q` is normal
    -- in `G`.
    have hindex_eq : Q.toSubgroup.index = Nat.card (K.subgroupOf G) := hcompG.symm.index_eq_card
    have hqpos' : 0 < q := by omega
    have hk1 : 1 < k := by omega
    have hgt : q < g := by rw [hgeq]; exact (lt_mul_iff_one_lt_right hqpos').mpr hk1
    have he1 : 0 < Nat.card (center SL(2,F)) := Nat.card_pos
    have hcard_lt : q < Nat.card G := by
      rw [hg]
      calc q < g := hgt
        _ ≤ Nat.card (center SL(2,F)) * g := Nat.le_mul_of_pos_left g he1
    have hp_dvd_Q : p ∣ Nat.card Q.toSubgroup := by
      have hQ_nontriv : (⊥ : Subgroup ↥G) < Q.toSubgroup := by
        rw [bot_lt_iff_ne_bot]
        intro hcontra
        rw [hcontra, Subgroup.card_bot] at hq
        omega
      exact hQelemAb.dvd_card hQ_nontriv
    have hcop_index : Nat.Coprime (Nat.card Q.toSubgroup) (Q.toSubgroup).index :=
      Sylow.card_coprime_index Q
    rw [hindex_eq] at hcop_index
    have htop_ne : (⊤ : Subgroup G) ≠ Q.toSubgroup := by
      intro hcontra
      have hcard_eq : Nat.card G = q := by
        rw [← Subgroup.card_top (G := ↥G), hcontra, hq]
      omega
    exact ⟨htop_ne, hQelemAb, hQ_normal, K.subgroupOf G, hcompG, hK_cyc',
      hcop_index.coprime_dvd_left hp_dvd_Q⟩

set_option maxHeartbeats 1000000 in
/-- **Shared extraction** (Butler tex ~1490-1508 for Case IIb, ~1579-1581 restated for the same
group `N_G(A₂)`; reused verbatim by Case IVb, tex ~1785 "numerically identical to IIb"): given a
cyclic maximal abelian `A2` of order `2 * g2` with normalizer index `2` (Theorem 6.8(iv)), produces
the `Q₈`-shaped generator pair `x0, y0 : ↥G` (`orderOf x0 = 2 * g2`, `y0 ^ 2 = x0 ^ g2`,
`y0 * x0 * y0⁻¹ = x0⁻¹`, `y0 ∉ zpowers x0`) that both Case IIb and Case IVb build their
`SL(2,3)`-presentation on. This is *exactly* the derivation already inlined in `case_II`'s Case IIa
block above (and, again inlined, in `case_VI_core`'s Case VIa block) up through Butler's
`y² = x^{g2}` identification -- extracted here as a genuine shared lemma since Case IIb and Case
IVb both need only this much (not IIa's further oddness/`QuaternionGroup` machinery). -/
private lemma exists_Q8_generators_of_relIndex_two {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F]
    [DecidableEq F] [Fact (Nat.Prime p)] [CharP F p]
    (G A2 : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (hA2_mem : A2 ∈ MaximalAbelianSubgroupsOf G) (hA2_cyc : IsCyclic A2)
    (hA2_cop : Nat.Coprime (Nat.card A2) p) (g2 : ℕ) (hg2_ge : 2 ≤ g2)
    (hA2_card : Nat.card A2 = 2 * g2)
    (hA2_relIndex : relIndex (A2.subgroupOf G) (normalizer (A2.subgroupOf G : Set ↥G)) = 2)
    (hp_ne_two : p ≠ 2) :
    ∃ x0 y0 : ↥G, orderOf x0 = 2 * g2 ∧ y0 ^ 2 = x0 ^ g2 ∧ y0 * x0 * y0⁻¹ = x0⁻¹ ∧
      y0 ∉ Subgroup.zpowers x0 ∧ (x0 : SL(2,F)) ∈ A2 := by
  classical
  haveI hF2 : NeZero (2 : F) := ⟨by
    intro h2
    have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact hp_ne_two (CharP.eq F (‹CharP F p› : CharP F p) hCharP2)⟩
  haveI hA2_fin : Finite A2 :=
    (Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hA2_mem.right).to_subtype
  obtain ⟨g0, hg0_gen⟩ := hA2_cyc.exists_generator
  have horder_g0 : orderOf g0 = Nat.card A2 := orderOf_eq_card_of_forall_mem_zpowers hg0_gen
  have horder_g0SL : orderOf (g0 : SL(2,F)) = 2 * g2 := by
    rw [orderOf_coe, horder_g0, hA2_card]
  haveI hg0_finord : IsOfFinOrder g0 := orderOf_pos_iff.mp (horder_g0 ▸ Nat.card_pos)
  obtain ⟨y, hy_mem, hy_conj⟩ :=
    of_index_normalizer_eq_two hp_ne_two A2 G hA2_mem center_le_G hA2_cop hA2_relIndex g0
  simp only [Set.mem_sdiff, SetLike.mem_coe, Subgroup.mem_carrier, Subgroup.mem_inf] at hy_mem
  obtain ⟨⟨hy_mem_norm, hy_mem_G⟩, hy_notin_A2⟩ := hy_mem
  -- `y` inverts every element of `A2` (it inverts the generator `g0`).
  have hinvert : ∀ a : SL(2,F), a ∈ A2 → y * a * y⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨n, hn⟩ := hg0_gen ⟨a, ha⟩
    have hn' : (g0 : SL(2,F)) ^ n = a := by
      have := congrArg (Subtype.val) hn
      simpa using this
    have hconj_pow : y * (g0 : SL(2,F)) ^ n * y⁻¹ = ((g0 : SL(2,F)) ^ n)⁻¹ := by
      have h1 := map_zpow (MulAut.conj y).toMonoidHom (g0 : SL(2,F)) n
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
      rw [h1, hy_conj, Subgroup.coe_inv, _root_.inv_zpow]
    rwa [hn'] at hconj_pow
  -- `y²` commutes with every element of `A2`.
  have hy2_comm : ∀ a : SL(2,F), a ∈ A2 → y ^ 2 * a = a * y ^ 2 := by
    intro a ha
    have h1 : y * a = a⁻¹ * y := by
      have h := hinvert a ha
      have h2 : y * a * y⁻¹ * y = a⁻¹ * y := by rw [h]
      simpa [mul_assoc] using h2
    have h2 : y * a⁻¹ = a * y := by
      have h := hinvert a⁻¹ (Subgroup.inv_mem A2 ha)
      rw [inv_inv] at h
      have h3 : y * a⁻¹ * y⁻¹ * y = a * y := by rw [h]
      simpa [mul_assoc] using h3
    calc y ^ 2 * a = y * y * a := by rw [pow_two]
      _ = y * (y * a) := by rw [mul_assoc]
      _ = y * (a⁻¹ * y) := by rw [h1]
      _ = y * a⁻¹ * y := by rw [mul_assoc]
      _ = (a * y) * y := by rw [h2]
      _ = a * (y * y) := by rw [mul_assoc]
      _ = a * y ^ 2 := by rw [pow_two]
  -- Maximality of `A2` (as an internal subgroup of `↥G`) forces `y² ∈ A2`.
  have hy2_mem_G : y ^ 2 ∈ G := Subgroup.pow_mem G hy_mem_G 2
  set A2' : Subgroup ↥G := A2.subgroupOf G with hA2'_def
  set y2' : ↥G := ⟨y ^ 2, hy2_mem_G⟩ with hy2'_def
  have hy2_mem_A2 : y ^ 2 ∈ A2 := by
    set k : Set ↥G := (A2' : Set ↥G) ∪ {y2'} with hk_def
    have hcomm_k : ∀ a ∈ k, ∀ b ∈ k, a * b = b * a := by
      haveI := hA2_mem.left.1
      rintro a (ha | ha) b (hb | hb)
      · exact setLike_mul_comm ha hb
      · simp only [Set.mem_singleton_iff] at hb; subst hb
        apply Subtype.ext
        have ha' : (a : SL(2,F)) ∈ A2 := by
          rw [SetLike.mem_coe, hA2'_def, Subgroup.mem_subgroupOf] at ha; exact ha
        simpa [hy2'_def] using (hy2_comm a ha').symm
      · simp only [Set.mem_singleton_iff] at ha; subst ha
        apply Subtype.ext
        have hb' : (b : SL(2,F)) ∈ A2 := by
          rw [SetLike.mem_coe, hA2'_def, Subgroup.mem_subgroupOf] at hb; exact hb
        simpa [hy2'_def] using hy2_comm b hb'
      · simp only [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
    haveI hclosure_comm : IsMulCommutative (closure k) :=
      Subgroup.isMulCommutative_closure hcomm_k
    have hA2'_le_closure : A2' ≤ closure k := by
      rw [← Subgroup.closure_eq A2']
      exact Subgroup.closure_mono (Set.subset_union_left)
    have hclosure_le : closure k ≤ A2' := hA2_mem.left.2 hclosure_comm hA2'_le_closure
    have hy2'_mem_closure : y2' ∈ closure k := subset_closure (Set.mem_union_right _ rfl)
    have hy2'_mem_A2' : y2' ∈ A2' := hclosure_le hy2'_mem_closure
    rwa [hA2'_def, Subgroup.mem_subgroupOf] at hy2'_mem_A2'
  -- `(y²)² = 1`: `y` both fixes `y²` (conjugation by a power of itself) and inverts it
  -- (as an element of `A2`).
  have h1 : y * y ^ 2 * y⁻¹ = (y ^ 2)⁻¹ := hinvert (y ^ 2) hy2_mem_A2
  have h2 : y * y ^ 2 * y⁻¹ = y ^ 2 := by group
  have hz0_inv : (y ^ 2)⁻¹ = y ^ 2 := h1.symm.trans h2
  have hz0sq : y ^ 2 * y ^ 2 = 1 := by
    calc y ^ 2 * y ^ 2 = y ^ 2 * (y ^ 2)⁻¹ := by rw [hz0_inv]
      _ = 1 := mul_inv_cancel _
  -- `y² ≠ 1`, else `y` would be an involution -- but `SL(2,F)`'s unique involution `-1`
  -- already lies in `A2 ⊇ center SL(2,F)`, while `y ∉ A2`.
  have hy2_ne_one : y ^ 2 ≠ 1 := by
    intro hy2eq1
    have hy_ne_one : y ≠ 1 := by
      intro hy1
      apply hy_notin_A2
      rw [hy1]
      exact Subgroup.one_mem A2
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2eq1
    have hord_ne_one : orderOf y ≠ 1 := by
      rw [Ne, orderOf_eq_one_iff]; exact hy_ne_one
    have hy_ord2 : orderOf y = 2 := by
      rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h | h
      · exact absurd h hord_ne_one
      · exact h
    have hy_eq_negone : y = -1 :=
      SpecialSubgroups.exists_unique_orderOf_eq_two.unique hy_ord2
        SpecialSubgroups.orderOf_neg_one_eq_two
    apply hy_notin_A2
    rw [hy_eq_negone]
    have hcenle : center SL(2,F) ≤ A2 := center_le G A2 hA2_mem center_le_G
    apply hcenle
    rw [SpecialSubgroups.center_SL2_eq_Z]
    exact SpecialSubgroups.neg_one_mem_Z
  -- Hence `y²` is *the* order-`2` element of `A2`.
  have hz0sq' : (y ^ 2) ^ 2 = 1 := by
    have hexp : (y ^ 2) ^ 2 = y ^ 2 * y ^ 2 := by group
    rw [hexp]; exact hz0sq
  have horder_z0 : orderOf (y ^ 2) = 2 := by
    have hdvd : orderOf (y ^ 2) ∣ 2 := orderOf_dvd_of_pow_eq_one hz0sq'
    have hne1 : orderOf (y ^ 2) ≠ 1 := by rw [Ne, orderOf_eq_one_iff]; exact hy2_ne_one
    rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h hne1
    · exact h
  -- Write `y² = g0 ^ n` for some `n < orderOf g0 = 2 * g2`, and pin `n = g2` down using
  -- `y² ≠ 1` and `(y²)² = 1`.
  have hz0mem : (⟨y ^ 2, hy2_mem_A2⟩ : A2) ∈ Subgroup.zpowers g0 := hg0_gen _
  rw [hg0_finord.mem_zpowers_iff_mem_range_orderOf] at hz0mem
  simp only [Finset.mem_image, Finset.mem_range] at hz0mem
  obtain ⟨n, hn_lt, hn_eq⟩ := hz0mem
  have hn_eq' : (g0 : SL(2,F)) ^ n = y ^ 2 := by
    have := congrArg (Subtype.val) hn_eq
    simpa using this
  have horder_g0_eq : orderOf g0 = 2 * g2 := by rw [horder_g0, hA2_card]
  rw [horder_g0_eq] at hn_lt
  have hn2 : (g0 : SL(2,F)) ^ (n * 2) = 1 := by
    rw [pow_mul, hn_eq']; exact hz0sq'
  have hdvd1 : orderOf (g0 : SL(2,F)) ∣ n * 2 := orderOf_dvd_of_pow_eq_one hn2
  rw [horder_g0SL] at hdvd1
  have hg2_dvd_n : g2 ∣ n := by
    have h1 : g2 * 2 ∣ n * 2 := by rwa [mul_comm 2 g2] at hdvd1
    exact (Nat.mul_dvd_mul_iff_right (by norm_num : (0:ℕ) < 2)).mp h1
  obtain ⟨t, ht⟩ := hg2_dvd_n
  have hn_ne : ¬ (2 * g2) ∣ n := by
    intro hdvd
    apply hy2_ne_one
    have hdvd' : orderOf (g0 : SL(2,F)) ∣ n := by rw [horder_g0SL]; exact hdvd
    rw [← hn_eq']
    exact orderOf_dvd_iff_pow_eq_one.mp hdvd'
  have ht2 : ¬ 2 ∣ t := by
    intro h2t
    apply hn_ne
    rw [ht]
    obtain ⟨j, hj⟩ := h2t
    exact ⟨j, by rw [hj]; ring⟩
  have ht_lt : t < 2 := by
    by_contra hcon
    push_neg at hcon
    have hge : 2 * g2 ≤ g2 * t := by
      calc 2 * g2 = g2 * 2 := by ring
        _ ≤ g2 * t := Nat.mul_le_mul_left g2 hcon
    rw [← ht] at hge
    omega
  have ht_eq : t = 1 := by omega
  have hn_eq_g2 : n = g2 := by rw [ht, ht_eq, mul_one]
  have hy2eq : y ^ 2 = (g0 : SL(2,F)) ^ g2 := by rw [← hn_eq_g2]; exact hn_eq'.symm
  -- Assemble the return data.
  set x0 : ↥G := ⟨(g0 : SL(2,F)), hA2_mem.right g0.2⟩ with hx0_def
  set y0 : ↥G := ⟨y, hy_mem_G⟩ with hy0_def
  have hx0_ord : orderOf x0 = 2 * g2 := by
    have h := orderOf_injective G.subtype (Subgroup.subtype_injective G) x0
    rw [← h]; exact horder_g0SL
  have hy0_2 : y0 ^ 2 = x0 ^ g2 := Subtype.ext hy2eq
  have hconj0 : y0 * x0 * y0⁻¹ = x0⁻¹ := Subtype.ext hy_conj
  have hyx0 : y0 ∉ Subgroup.zpowers x0 := by
    intro hmem
    obtain ⟨k, hk⟩ := hmem
    apply hy_notin_A2
    have hk' : (g0 : SL(2,F)) ^ k = y := by
      have := congrArg (Subtype.val) hk
      simpa using this
    rw [← hk']
    exact Subgroup.zpow_mem A2 g0.2 k
  have hx0_mem_A2 : (x0 : SL(2,F)) ∈ A2 := by rw [hx0_def]; exact g0.2
  exact ⟨x0, y0, hx0_ord, hy0_2, hconj0, hyx0, hx0_mem_A2⟩

/-- Conjugating a `zpowers` subgroup by (the automorphism `conj c` induced by) an element `c`
gives the `zpowers` of the conjugated generator. Pure abstract-group-theory fact, needed by
`case_II`'s Case IIb (and `case_IV`'s Case IVb) to identify `conj r0 • A2` (`A2` cyclic, generated
by `x0`) with `zpowers (r0 * x0 * r0⁻¹)`. -/
private lemma conj_zpowers_eq {H : Type*} [Group H] (c a : H) :
    conj c • Subgroup.zpowers a = Subgroup.zpowers (c * a * c⁻¹) := by
  ext z
  simp only [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_zpowers_iff, MulAut.smul_def]
  have key : ∀ n : ℤ, (conj c) (a ^ n) = (c * a * c⁻¹) ^ n := by
    intro n
    have h1 := map_zpow (conj c).toMonoidHom a n
    simpa using h1
  constructor
  · rintro ⟨w, ⟨n, hn⟩, hz⟩
    exact ⟨n, by rw [← hz, ← hn, key]⟩
  · rintro ⟨n, hn⟩
    exact ⟨a ^ n, ⟨n, rfl⟩, by rw [key, hn]⟩

open NumericClassEquation in
set_option maxHeartbeats 1000000 in
/-- Butler Case II (tex 1453-1640): `s = 1, t = 1`. Forces `p ∤ |G|` (`q = 1`) and pins down
`g₁ ∈ {2,3}`; Case IIa (`g₁ = 2`) constructs the dicyclic group of order `4n` (`n` odd) presented
as `⟨x,y | x^n = y^2, yxy⁻¹ = x⁻¹⟩` (tex ~1550-1580) -- this is exactly mathlib's
`QuaternionGroup n` (order `4n`, presentation `⟨a,x | a^{2n}=1, x^2=a^n, x⁻¹ax=a⁻¹⟩`, which
matches Butler's `x ↦ a`, `y ↦ x`); Case IIb (`g₁ = 3`) constructs an explicit isomorphism with
`SL(2,3)` (tex ~1600-1640).

RESTATED+PROVED for Case IIa (justification: exactly as in `case_I`/`case_IV`, the previous
`heq : ∃ k g1 g2, ...` hid Butler's cyclic maximal abelian subgroups `A₁` (`s = 1` class,
normalizer index `1`) and `A₂` (`t = 1` class, normalizer index `2`) behind bare numerals.
Restated to carry both witnesses directly, `[IsAlgClosed F] [DecidableEq F]` added (needed by
`S2_B.of_index_normalizer_eq_two`, matching `case_I`/`case_IV`).

With these witnesses, `CaseArithmetic.case_1_1` gives `q = 1` and `g1 = 2 ∨ g1 = 3`; unfolding
`ClassEquation` directly with `q = 1` substituted (`case_1_1` itself does not expose the further
numeral identities Butler derives per sub-case) gives `g = 2 * g2` when `g1 = 2` (Case IIa,
Equation `case2b` in the tex) and (unused here) `g2 = 2, g = 12` when `g1 = 3` (Case IIb). Case
IIa then runs Butler's argument in full: `e ≠ 1` (else `p = 2`, `CharTwo.two_eq_zero`, so
`2 ∣ Nat.card G = g = 2 g2`, contradicting `q = 1 ⟹ p ∤ Nat.card G`, `Sylow.card_eq_multiplicity`),
so `e = 2` and `p ≠ 2`; `A₁` (order `e g1 = 4`) is then shown to be *itself* a Sylow `2`-subgroup
of `G` (else, extending `A₁.subgroupOf G` to a genuine `S : Sylow 2 G`, Lemma 3.1
(`IsPGroup.lt_normalizer_subgroupOf`, generalized above) would force
`A₁.subgroupOf G < normalizer (A₁.subgroupOf G)` inside `S`, contradicting `A₁`'s normalizer
index `1`, i.e. `A₁.subgroupOf G = normalizer (A₁.subgroupOf G : Set ↥G)`); hence the `2`-part of
`Nat.card G` is exactly `4`, and since `Nat.card G = e g = 2 (2 g2) = 4 g2`, `g2` is odd. Taking
`g0` a generator of `A₂` (order `2 g2`, `IsCyclic.exists_generator`) and, via
`of_index_normalizer_eq_two`, an inverting `y ∈ N_G(A₂) \ A₂` with `y g0 y⁻¹ = g0⁻¹`: since `A₂` is
cyclic generated by `g0`, `y` in fact inverts *every* element of `A₂`, not just `g0`; in
particular `y²` centralizes `A₂` pointwise (`y (y a) y⁻¹ = y a⁻¹ y⁻¹ = a` for `a ∈ A₂` -- see
`hinvert`/`hy2_comm` in-proof), so (maximality of `A₂`, via the same closure/`Maximal` argument as
Lemma 3.2 above) `y² ∈ A₂`. Being an element of `A₂` itself, `y` also inverts `y²`, giving
`y (y²) y⁻¹ = (y²)⁻¹`; but conjugating a power of `y` by `y` fixes it, `y (y²) y⁻¹ = y²`; so
`(y²)² = 1`. This rules out `y² = 1` (else `y` itself would be an involution, but `SL(2,F)`'s
*unique* involution `-1` (`p ≠ 2`, `SpecialSubgroups.exists_unique_orderOf_eq_two`) already lies in
`center SL(2,F) ≤ A₂` -- `center_le` -- while `y ∉ A₂`, a contradiction), so `y²` is *the* order-`2`
element of the cyclic group `A₂` (order `2 g2`, `g2` odd): writing `y² = g0 ^ n` for the unique
`n < orderOf g0 = 2 g2` (`IsOfFinOrder.mem_zpowers_iff_mem_range_orderOf`), `(y²)² = 1` forces
`g2 ∣ n`, and `y² ≠ 1` forces `¬ (2 g2 ∣ n)`; writing `n = g2 t`, this pins down `t = 1`, i.e.
`y² = g0 ^ g2`. This closes the gap left by the original module plan (which additionally invoked
"`A₂` normal and `A₁` the *only* other maximal abelian class forces `y ∈ A₁`", a global structural
fact about the noncenter decomposition not otherwise threaded through to this lemma's hypotheses)
with a self-contained cyclic-group argument instead. `mulEquiv_quaternionGroup_of` (from
`Ch7_GroupRecognition`, imported below) then gives `G ≃* QuaternionGroup g2` directly, since
`Nat.card G = 4 * g2`.
PROVED for Case IIa.

Case IIb (`g1 = 3`) is now **fully PROVED**, using a new `hComplete` hypothesis (Theorem 6.8's
numeric class equation, `S5_NumericClassEquation.BridgeData.hComplete`): every maximal abelian
subgroup of `G` is `G`-conjugate to `A1`, to `A2`, or is of Sylow type. The numerals (`g2 = 2`,
`g = 12`, hence `e = 2`, `p ≠ 2`, tex ~1512-1516) and the `Q₈`-shaped generator pair `x0, y0` on
`A₂` (`orderOf x0 = 4`, `x0² = y0²`, `y0 x0 y0⁻¹ = x0⁻¹`, `y0 ∉ zpowers x0`, tex ~1579-1581, via
the shared `exists_Q8_generators_of_relIndex_two` above) are proved directly, as before. Butler's
own hardest step (tex ~1587-1637) -- producing an order-`3` element `r` with *exactly*
`r * x0 * r⁻¹ = y1` and `r * y1 * r⁻¹ = x0 * y1` for a suitable generator `y1` of `N_G(A2)`
(`mulEquiv_SL2_ZMod3_of`'s hypotheses, already PROVED and waiting in `Ch7_GroupRecognition`,
`DIVERGENCES.md` item 8) -- is now closed *without* first establishing `N := N_G(A₂) ⊴ G`
globally (Butler's own route, tex ~1582 "Corollary 4thSylow, `N ⊴ G`"): an order-`3` element
`r0` is drawn from `A₁`'s cyclic subgroup of order `3`; `y1 := r0 x0 r0⁻¹` is shown, via
`hComplete` (ruling out the `A₁`-conjugate case by cardinality `4 ≠ 6`, and the Sylow-type case
by a short numeric argument), to be `G`-conjugate to `A₂` itself -- and, running the identical
argument on `A₂`'s own alternate generator pairs `y0, x0y0`, the `3`-element set of
`G`-conjugates of `A₂` is pinned down to exactly `{A2, zpowers y0, zpowers (x0 y0)}` (Butler's
"no other classes besides `A₁, A₂`" global fact, now *derived* from `hComplete` rather than
assumed). A final counting argument ("`ConjClassOf G A2` minus `{A2, zpowers y1}` has exactly
one element, and both `zpowers (x0 y1)` and `zpowers (r0 y1 r0⁻¹)` lie in it") pins `r0 y1 r0⁻¹`
down to `x0 y1` or `(x0 y1)⁻¹` -- Butler's own `2`-way case split (tex ~1637-1642), resolved via
`r0` vs `r0²`. See `DIVERGENCES.md` item 10 for the full account; the residual gap this closes
was the same *category* of gap as the one still left open in `case_VI_core`'s `gb = gc = 3`
branch above (tex ~2149-2157, "Sylow-conjugacy elimination... genuinely group-theoretic") --
see `DIVERGENCES.md` item 10 for why that one, and Case IVb's analogous gap, remain open. -/
lemma case_II {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F] [Fact (Nat.Prime p)]
    [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q) (g1 g2 k : ℕ)
    -- witness for the `s = 1` class `A₁` (Theorem 6.8), replacing the bare numeral `g1`.
    (A1 : Subgroup SL(2,F)) (hA1_mem : A1 ∈ MaximalAbelianSubgroupsOf G)
    (hA1_cyc : IsCyclic A1) (hA1_cop : Nat.Coprime (Nat.card A1) p)
    (hA1_card : Nat.card A1 = Nat.card (center SL(2,F)) * g1)
    (hA1_relIndex : relIndex (A1.subgroupOf G) (normalizer (A1.subgroupOf G : Set ↥G)) = 1)
    -- witness for the `t = 1` class `A₂` (Theorem 6.8), replacing the bare numeral `g2`.
    (A2 : Subgroup SL(2,F)) (hA2_mem : A2 ∈ MaximalAbelianSubgroupsOf G)
    (hA2_cyc : IsCyclic A2) (hA2_cop : Nat.Coprime (Nat.card A2) p)
    (hA2_card : Nat.card A2 = Nat.card (center SL(2,F)) * g2)
    (hA2_relIndex : relIndex (A2.subgroupOf G) (normalizer (A2.subgroupOf G : Set ↥G)) = 2)
    -- **Completeness** (Theorem 6.8's numeric class equation, `S5_NumericClassEquation`):
    -- every maximal abelian subgroup of `G` is `G`-conjugate to `A1`, to `A2`, or is of Sylow
    -- type. Needed to close Case IIb below (see its docstring).
    (hComplete : ∀ B ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B = A1) ∨
      (∃ c ∈ G, conj c • B = A2) ∨ IsSylowType p G B)
    (heq : 1 ≤ k ∧ 2 ≤ g1 ∧ 2 ≤ g2 ∧ (g2 < k → k = g1) ∧
      ClassEquation g q k (s := 1) (t := 1) (fun _ => g1) (fun _ => g2)) :
    Isomorphic G SL(2, ZMod 3) ∨ ∃ n, Odd n ∧ Isomorphic G (QuaternionGroup n) := by
  obtain ⟨hk_ge, hg1_ge, hg2_ge, hKeq, heq'⟩ := heq
  have hgpos : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with hg0 | hgpos
    · exfalso; rw [hg0, mul_zero] at hg
      have := Nat.card_pos (α := G); omega
    · exact hgpos
  have hqpos : 1 ≤ q := by have := Nat.card_pos (α := Q.toSubgroup); omega
  obtain ⟨hq1, hg1cases⟩ := case_1_1 g q k g1 g2 hgpos hqpos hk_ge hg1_ge hg2_ge hKeq heq'
  rcases hg1cases with hg1eq2 | hg1eq3
  · -- **Case IIa** (`g1 = 2`): dicyclic/quaternion.
    right
    -- `g = 2 * g2` (Butler's Equation `case2b` specialized to `g1 = 2`).
    have hgeq : g = 2 * g2 := by
      have hg1Q : (g1 : ℚ) = 2 := by exact_mod_cast hg1eq2
      have hqQ : (q : ℚ) = 1 := by exact_mod_cast hq1
      have hgposQ : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hgpos
      have hg2posQ : (0 : ℚ) < (g2 : ℚ) := by exact_mod_cast (by omega : 0 < g2)
      unfold ClassEquation at heq'
      simp only [Fin.sum_univ_one] at heq'
      rw [hqQ, hg1Q] at heq'
      norm_num at heq'
      have hgne : (g : ℚ) ≠ 0 := hgposQ.ne'
      have hg2ne : (g2 : ℚ) ≠ 0 := hg2posQ.ne'
      field_simp at heq'
      have hgQeq : (g : ℚ) = 2 * (g2 : ℚ) := by linarith [heq']
      exact_mod_cast hgQeq
    -- `q = 1` means `Q` (a Sylow `p`-subgroup) is trivial, so `p ∤ Nat.card G`.
    have hp_ndvd : ¬ p ∣ Nat.card G := by
      have hme : Nat.card Q.toSubgroup = p ^ (Nat.card G).factorization p :=
        Sylow.card_eq_multiplicity Q
      rw [hq, hq1] at hme
      intro hdvd
      have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
      have hpos : 0 < (Nat.card G).factorization p :=
        (Fact.out : Nat.Prime p).factorization_pos_of_dvd hGne hdvd
      have h1lt : 1 < p ^ (Nat.card G).factorization p :=
        Nat.one_lt_pow hpos.ne' (Fact.out : Nat.Prime p).one_lt
      omega
    -- `e ≠ 1`: otherwise `p = 2` (`CharTwo.two_eq_zero`/uniqueness of characteristic), so
    -- `2 ∣ Nat.card G = g = 2 * g2`, contradicting `hp_ndvd`.
    have he_ne_one : Nat.card (center SL(2,F)) ≠ 1 := by
      intro he1
      have h2 : (2 : F) = 0 := by
        by_contra h2ne
        haveI : NeZero (2 : F) := ⟨h2ne⟩
        rw [SpecialSubgroups.center_SL2_eq_Z, SpecialSubgroups.card_Z_eq_two_of_two_ne_zero] at he1
        omega
      have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
      have hp2 : p = 2 := (CharP.eq F (‹CharP F p› : CharP F p) hCharP2 : p = 2)
      apply hp_ndvd
      rw [hp2, hg, he1, one_mul, hgeq]
      exact ⟨g2, rfl⟩
    have he_le_two : Nat.card (center SL(2,F)) ≤ 2 := by
      rw [SpecialSubgroups.center_SL2_eq_Z]; exact SpecialSubgroups.card_Z_le_two
    have he2 : Nat.card (center SL(2,F)) = 2 := by
      have := Nat.card_pos (α := center SL(2,F)); omega
    have hp_ne_two : p ≠ 2 := by
      intro hp2
      subst hp2
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have he1 : Nat.card (center SL(2,F)) = 1 := by
        rw [SpecialSubgroups.center_SL2_eq_Z]
        exact SpecialSubgroups.card_Z_eq_one_of_two_eq_zero h2
      omega
    -- `A₁` (order `e * g1 = 4`) is itself a Sylow `2`-subgroup of `G`: otherwise, extending
    -- `A₁.subgroupOf G` to a genuine Sylow `2`-subgroup `S` and applying Lemma 3.1
    -- (`IsPGroup.lt_normalizer_subgroupOf`) inside `S` would force `A₁.subgroupOf G` to be
    -- strictly smaller than its own normalizer -- contradicting `hA1_relIndex = 1` (`A₁` is
    -- exactly self-normalizing).
    have hSelfNorm : A1.subgroupOf G = normalizer (A1.subgroupOf G : Set ↥G) :=
      le_antisymm Subgroup.le_normalizer (Subgroup.relIndex_eq_one.mp hA1_relIndex)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hA1_card' : Nat.card A1 = 4 := by rw [hA1_card, he2, hg1eq2]
    have hA1subG_IsPGroup : IsPGroup 2 (A1.subgroupOf G) := by
      rw [IsPGroup.iff_card]
      refine ⟨2, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA1_mem.right).toEquiv, hA1_card']
      norm_num
    obtain ⟨S, hA1_le_S⟩ := hA1subG_IsPGroup.exists_le_sylow
    have hA1_eq_S : A1.subgroupOf G = S.toSubgroup := by
      by_contra hne
      have hlt : A1.subgroupOf G < S.toSubgroup := lt_of_le_of_ne hA1_le_S hne
      have hcontra := IsPGroup.lt_normalizer_subgroupOf (A1.subgroupOf G) (S.toSubgroup)
        S.isPGroup' hlt
      rw [← Subgroup.subgroupOf_normalizer_eq hA1_le_S, ← hSelfNorm] at hcontra
      exact lt_irrefl _ hcontra
    -- Hence the `2`-part of `Nat.card G` is exactly `4`, and since `Nat.card G = 4 * g2`, `g2`
    -- is odd.
    have hcard_S : Nat.card S.toSubgroup = 4 := by
      rw [← hA1_eq_S, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA1_mem.right).toEquiv,
        hA1_card']
    have hfact4 : (Nat.card G).factorization 2 = 2 := by
      have hme : Nat.card S.toSubgroup = 2 ^ (Nat.card G).factorization 2 :=
        Sylow.card_eq_multiplicity S
      rw [hcard_S] at hme
      have h42 : (4 : ℕ) = 2 ^ 2 := by norm_num
      rw [h42] at hme
      exact Nat.pow_right_injective (le_refl 2) hme.symm
    have hg2pos : 0 < g2 := by omega
    have hcardG4g2 : Nat.card G = 4 * g2 := by rw [hg, he2, hgeq]; ring
    have hodd : Odd g2 := by
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
      intro hdvd2
      have hg2ne : g2 ≠ 0 := hg2pos.ne'
      have h4ne : (4 : ℕ) ≠ 0 := by norm_num
      have hmul : (Nat.card G).factorization 2 = (4 : ℕ).factorization 2 + g2.factorization 2 := by
        rw [hcardG4g2, Nat.factorization_mul h4ne hg2ne]; rfl
      rw [hfact4] at hmul
      have h4fact : (4 : ℕ).factorization 2 = 2 := by
        have h4eq : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h4eq, Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
      rw [h4fact] at hmul
      have hgfactpos : 0 < g2.factorization 2 :=
        Nat.prime_two.factorization_pos_of_dvd hg2ne hdvd2
      omega
    refine ⟨g2, hodd, ?_⟩
    classical
    -- Butler's identification `y² = x^{g2}` (tex ~1508-1520), *without* needing the "only two
    -- classes" global fact used in the original sketch: `y` (the `Theorem 6.8(iv)` inverter of
    -- `A₂`'s generator `g0`, obtained below) inverts *every* element of the cyclic group `A₂`
    -- (not just the generator), so `y²` centralizes `A₂`, hence lies in `A₂` by `A₂`'s
    -- maximality; `y²` then satisfies `(y²)² = 1` (it commutes with itself, but `y` inverts it as
    -- an element of `A₂`) and `y² ≠ 1` (else `y` itself would be an involution, contradicting the
    -- *uniqueness* of `SL(2,F)`'s involution `-1` -- `exists_unique_orderOf_eq_two`, `p ≠ 2` --
    -- since `-1 ∈ center SL(2,F) ≤ A₂` while `y ∉ A₂`); so `y²` is *the* order-`2` element of the
    -- cyclic group `A₂` (order `2 g2`, `g2` odd), i.e. `g0 ^ g2`.
    haveI hF2 : NeZero (2 : F) := ⟨by
      intro h2
      have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
      exact hp_ne_two (CharP.eq F (‹CharP F p› : CharP F p) hCharP2)⟩
    haveI hA2_fin : Finite A2 :=
      (Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hA2_mem.right).to_subtype
    -- A generator `g0` of the cyclic group `A2`, with `orderOf (g0 : SL(2,F)) = 2 * g2`.
    obtain ⟨g0, hg0_gen⟩ := hA2_cyc.exists_generator
    have horder_g0 : orderOf g0 = Nat.card A2 := orderOf_eq_card_of_forall_mem_zpowers hg0_gen
    have horder_g0SL : orderOf (g0 : SL(2,F)) = 2 * g2 := by
      rw [orderOf_coe, horder_g0, hA2_card, he2]
    haveI hg0_finord : IsOfFinOrder g0 := orderOf_pos_iff.mp (horder_g0 ▸ Nat.card_pos)
    -- Theorem 6.8(iv): an inverting element `y ∈ N_G(A2) \ A2`.
    obtain ⟨y, hy_mem, hy_conj⟩ :=
      of_index_normalizer_eq_two hp_ne_two A2 G hA2_mem center_le_G hA2_cop hA2_relIndex g0
    simp only [Set.mem_sdiff, SetLike.mem_coe, Subgroup.mem_carrier, Subgroup.mem_inf] at hy_mem
    obtain ⟨⟨hy_mem_norm, hy_mem_G⟩, hy_notin_A2⟩ := hy_mem
    -- `y` inverts every element of `A2` (it inverts the generator `g0`).
    have hinvert : ∀ a : SL(2,F), a ∈ A2 → y * a * y⁻¹ = a⁻¹ := by
      intro a ha
      obtain ⟨n, hn⟩ := hg0_gen ⟨a, ha⟩
      have hn' : (g0 : SL(2,F)) ^ n = a := by
        have := congrArg (Subtype.val) hn
        simpa using this
      have hconj_pow : y * (g0 : SL(2,F)) ^ n * y⁻¹ = ((g0 : SL(2,F)) ^ n)⁻¹ := by
        have h1 := map_zpow (MulAut.conj y).toMonoidHom (g0 : SL(2,F)) n
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
        rw [h1, hy_conj, Subgroup.coe_inv, _root_.inv_zpow]
      rwa [hn'] at hconj_pow
    -- `y²` commutes with every element of `A2`.
    have hy2_comm : ∀ a : SL(2,F), a ∈ A2 → y ^ 2 * a = a * y ^ 2 := by
      intro a ha
      have h1 : y * a = a⁻¹ * y := by
        have h := hinvert a ha
        have h2 : y * a * y⁻¹ * y = a⁻¹ * y := by rw [h]
        simpa [mul_assoc] using h2
      have h2 : y * a⁻¹ = a * y := by
        have h := hinvert a⁻¹ (Subgroup.inv_mem A2 ha)
        rw [inv_inv] at h
        have h3 : y * a⁻¹ * y⁻¹ * y = a * y := by rw [h]
        simpa [mul_assoc] using h3
      calc y ^ 2 * a = y * y * a := by rw [pow_two]
        _ = y * (y * a) := by rw [mul_assoc]
        _ = y * (a⁻¹ * y) := by rw [h1]
        _ = y * a⁻¹ * y := by rw [mul_assoc]
        _ = (a * y) * y := by rw [h2]
        _ = a * (y * y) := by rw [mul_assoc]
        _ = a * y ^ 2 := by rw [pow_two]
    -- Maximality of `A2` (as an internal subgroup of `↥G`) forces `y² ∈ A2`.
    have hy2_mem_G : y ^ 2 ∈ G := Subgroup.pow_mem G hy_mem_G 2
    set A2' : Subgroup ↥G := A2.subgroupOf G with hA2'_def
    set y2' : ↥G := ⟨y ^ 2, hy2_mem_G⟩ with hy2'_def
    have hy2_mem_A2 : y ^ 2 ∈ A2 := by
      set k : Set ↥G := (A2' : Set ↥G) ∪ {y2'} with hk_def
      have hcomm_k : ∀ a ∈ k, ∀ b ∈ k, a * b = b * a := by
        haveI := hA2_mem.left.1
        rintro a (ha | ha) b (hb | hb)
        · exact setLike_mul_comm ha hb
        · simp only [Set.mem_singleton_iff] at hb; subst hb
          apply Subtype.ext
          have ha' : (a : SL(2,F)) ∈ A2 := by
            rw [SetLike.mem_coe, hA2'_def, Subgroup.mem_subgroupOf] at ha; exact ha
          simpa [hy2'_def] using (hy2_comm a ha').symm
        · simp only [Set.mem_singleton_iff] at ha; subst ha
          apply Subtype.ext
          have hb' : (b : SL(2,F)) ∈ A2 := by
            rw [SetLike.mem_coe, hA2'_def, Subgroup.mem_subgroupOf] at hb; exact hb
          simpa [hy2'_def] using hy2_comm b hb'
        · simp only [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
      haveI hclosure_comm : IsMulCommutative (closure k) :=
        Subgroup.isMulCommutative_closure hcomm_k
      have hA2'_le_closure : A2' ≤ closure k := by
        rw [← Subgroup.closure_eq A2']
        exact Subgroup.closure_mono (Set.subset_union_left)
      have hclosure_le : closure k ≤ A2' := hA2_mem.left.2 hclosure_comm hA2'_le_closure
      have hy2'_mem_closure : y2' ∈ closure k := subset_closure (Set.mem_union_right _ rfl)
      have hy2'_mem_A2' : y2' ∈ A2' := hclosure_le hy2'_mem_closure
      rwa [hA2'_def, Subgroup.mem_subgroupOf] at hy2'_mem_A2'
    -- `(y²)² = 1`: `y` both fixes `y²` (conjugation by a power of itself) and inverts it
    -- (as an element of `A2`).
    have h1 : y * y ^ 2 * y⁻¹ = (y ^ 2)⁻¹ := hinvert (y ^ 2) hy2_mem_A2
    have h2 : y * y ^ 2 * y⁻¹ = y ^ 2 := by group
    have hz0_inv : (y ^ 2)⁻¹ = y ^ 2 := h1.symm.trans h2
    have hz0sq : y ^ 2 * y ^ 2 = 1 := by
      calc y ^ 2 * y ^ 2 = y ^ 2 * (y ^ 2)⁻¹ := by rw [hz0_inv]
        _ = 1 := mul_inv_cancel _
    -- `y² ≠ 1`, else `y` would be an involution -- but `SL(2,F)`'s unique involution `-1`
    -- already lies in `A2 ⊇ center SL(2,F)`, while `y ∉ A2`.
    have hy2_ne_one : y ^ 2 ≠ 1 := by
      intro hy2eq1
      have hy_ne_one : y ≠ 1 := by
        intro hy1
        apply hy_notin_A2
        rw [hy1]
        exact Subgroup.one_mem A2
      have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2eq1
      have hord_ne_one : orderOf y ≠ 1 := by
        rw [Ne, orderOf_eq_one_iff]; exact hy_ne_one
      have hy_ord2 : orderOf y = 2 := by
        rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h | h
        · exact absurd h hord_ne_one
        · exact h
      have hy_eq_negone : y = -1 :=
        SpecialSubgroups.exists_unique_orderOf_eq_two.unique hy_ord2
          SpecialSubgroups.orderOf_neg_one_eq_two
      apply hy_notin_A2
      rw [hy_eq_negone]
      have hcenle : center SL(2,F) ≤ A2 := center_le G A2 hA2_mem center_le_G
      apply hcenle
      rw [SpecialSubgroups.center_SL2_eq_Z]
      exact SpecialSubgroups.neg_one_mem_Z
    -- Hence `y²` is *the* order-`2` element of `A2`.
    have hz0sq' : (y ^ 2) ^ 2 = 1 := by
      have hexp : (y ^ 2) ^ 2 = y ^ 2 * y ^ 2 := by group
      rw [hexp]; exact hz0sq
    have horder_z0 : orderOf (y ^ 2) = 2 := by
      have hdvd : orderOf (y ^ 2) ∣ 2 := orderOf_dvd_of_pow_eq_one hz0sq'
      have hne1 : orderOf (y ^ 2) ≠ 1 := by rw [Ne, orderOf_eq_one_iff]; exact hy2_ne_one
      rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h | h
      · exact absurd h hne1
      · exact h
    -- Write `y² = g0 ^ n` for some `n < orderOf g0 = 2 * g2`, and pin `n = g2` down using
    -- `y² ≠ 1` and `(y²)² = 1`.
    have hz0mem : (⟨y ^ 2, hy2_mem_A2⟩ : A2) ∈ Subgroup.zpowers g0 := hg0_gen _
    rw [hg0_finord.mem_zpowers_iff_mem_range_orderOf] at hz0mem
    simp only [Finset.mem_image, Finset.mem_range] at hz0mem
    obtain ⟨n, hn_lt, hn_eq⟩ := hz0mem
    have hn_eq' : (g0 : SL(2,F)) ^ n = y ^ 2 := by
      have := congrArg (Subtype.val) hn_eq
      simpa using this
    have horder_g0_eq : orderOf g0 = 2 * g2 := by rw [horder_g0, hA2_card, he2]
    rw [horder_g0_eq] at hn_lt
    have hn2 : (g0 : SL(2,F)) ^ (n * 2) = 1 := by
      rw [pow_mul, hn_eq']; exact hz0sq'
    have hdvd1 : orderOf (g0 : SL(2,F)) ∣ n * 2 := orderOf_dvd_of_pow_eq_one hn2
    rw [horder_g0SL] at hdvd1
    have hg2_dvd_n : g2 ∣ n := by
      have h1 : g2 * 2 ∣ n * 2 := by rwa [mul_comm 2 g2] at hdvd1
      exact (Nat.mul_dvd_mul_iff_right (by norm_num : (0:ℕ) < 2)).mp h1
    obtain ⟨t, ht⟩ := hg2_dvd_n
    have hn_ne : ¬ (2 * g2) ∣ n := by
      intro hdvd
      apply hy2_ne_one
      have hdvd' : orderOf (g0 : SL(2,F)) ∣ n := by rw [horder_g0SL]; exact hdvd
      rw [← hn_eq']
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd'
    have ht2 : ¬ 2 ∣ t := by
      intro h2t
      apply hn_ne
      rw [ht]
      obtain ⟨j, hj⟩ := h2t
      exact ⟨j, by rw [hj]; ring⟩
    have ht_lt : t < 2 := by
      by_contra hcon
      push Not at hcon
      have hge : 2 * g2 ≤ g2 * t := by
        calc 2 * g2 = g2 * 2 := by ring
          _ ≤ g2 * t := Nat.mul_le_mul_left g2 hcon
      rw [← ht] at hge
      omega
    have ht_eq : t = 1 := by omega
    have hn_eq_g2 : n = g2 := by rw [ht, ht_eq, mul_one]
    have hy2eq : y ^ 2 = (g0 : SL(2,F)) ^ g2 := by rw [← hn_eq_g2]; exact hn_eq'.symm
    -- Assemble `mulEquiv_quaternionGroup_of`'s hypotheses and conclude.
    haveI : NeZero g2 := ⟨hg2pos.ne'⟩
    set x0 : ↥G := ⟨(g0 : SL(2,F)), hA2_mem.right g0.2⟩ with hx0_def
    set y0 : ↥G := ⟨y, hy_mem_G⟩ with hy0_def
    have hx0_ord : orderOf x0 = 2 * g2 := by
      have h := orderOf_injective G.subtype (Subgroup.subtype_injective G) x0
      rw [← h]; exact horder_g0SL
    have hy0_2 : y0 ^ 2 = x0 ^ g2 := Subtype.ext hy2eq
    have hconj0 : y0 * x0 * y0⁻¹ = x0⁻¹ := Subtype.ext hy_conj
    have hyx0 : y0 ∉ Subgroup.zpowers x0 := by
      intro hmem
      obtain ⟨k, hk⟩ := hmem
      apply hy_notin_A2
      have hk' : (g0 : SL(2,F)) ^ k = y := by
        have := congrArg (Subtype.val) hk
        simpa using this
      rw [← hk']
      exact Subgroup.zpow_mem A2 g0.2 k
    exact ⟨mulEquiv_quaternionGroup_of x0 y0 hx0_ord hy0_2 hconj0 hyx0 hcardG4g2⟩
  · -- **Case IIb** (`g1 = 3`): partially proved -- see docstring for exactly what remains.
    left
    classical
    -- Numerals (Butler tex ~1512-1516): `g2 = 2`, `g = 12`.
    have hg1Q : (g1 : ℚ) = 3 := by exact_mod_cast hg1eq3
    have hqQ : (q : ℚ) = 1 := by exact_mod_cast hq1
    have hgposQ : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hgpos
    have hg2posQ : (0 : ℚ) < (g2 : ℚ) := by exact_mod_cast (by omega : 0 < g2)
    unfold ClassEquation at heq'
    simp only [Fin.sum_univ_one] at heq'
    have e0 : ((q : ℚ) - 1) / (q * k) = 0 := by rw [hqQ]; simp
    have e1 : ((g1 : ℚ) - 1) / g1 = 2 / 3 := by rw [hg1Q]; norm_num
    have e2 : ((g2 : ℚ) - 1) / (2 * g2) = 1 / 2 - 1 / (2 * g2) := one_sub_inv_two_self hg2posQ.ne'
    rw [e0, e1, e2] at heq'
    have heqC : (1 : ℚ) / (2 * g2) = 1 / 6 + 1 / g := by linarith
    have hg2lt3 : (g2 : ℚ) < 3 := by
      by_contra hcon
      push_neg at hcon
      have hb : (1 : ℚ) / (2 * g2) ≤ 1 / 6 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      have hgpos' : (0 : ℚ) < 1 / g := by positivity
      linarith
    have hg2eq2 : g2 = 2 := by
      have h1 : g2 < 3 := by exact_mod_cast hg2lt3
      omega
    have hg2Q2 : (g2 : ℚ) = 2 := by exact_mod_cast hg2eq2
    rw [hg2Q2] at heqC
    have hgeq12 : g = 12 := by
      have hgne : (g : ℚ) ≠ 0 := hgposQ.ne'
      field_simp at heqC
      have : (g : ℚ) = 12 := by linarith
      exact_mod_cast this
    -- `q = 1` means `Q` is trivial, so `p ∤ Nat.card G`; combined with `g = 12` (even), this
    -- forces `p ≠ 2` (as in Case IIa above), hence `e = Nat.card (center SL(2,F)) = 2`.
    have hp_ndvd : ¬ p ∣ Nat.card G := by
      have hme : Nat.card Q.toSubgroup = p ^ (Nat.card G).factorization p :=
        Sylow.card_eq_multiplicity Q
      rw [hq, hq1] at hme
      intro hdvd
      have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
      have hpos : 0 < (Nat.card G).factorization p :=
        (Fact.out : Nat.Prime p).factorization_pos_of_dvd hGne hdvd
      have h1lt : 1 < p ^ (Nat.card G).factorization p :=
        Nat.one_lt_pow hpos.ne' (Fact.out : Nat.Prime p).one_lt
      omega
    have he_ne_one : Nat.card (center SL(2,F)) ≠ 1 := by
      intro he1
      have h2 : (2 : F) = 0 := by
        by_contra h2ne
        haveI : NeZero (2 : F) := ⟨h2ne⟩
        rw [SpecialSubgroups.center_SL2_eq_Z, SpecialSubgroups.card_Z_eq_two_of_two_ne_zero] at he1
        omega
      have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
      have hp2 : p = 2 := (CharP.eq F (‹CharP F p› : CharP F p) hCharP2 : p = 2)
      apply hp_ndvd
      rw [hp2, hg, he1, one_mul, hgeq12]
      exact ⟨6, rfl⟩
    have he_le_two : Nat.card (center SL(2,F)) ≤ 2 := by
      rw [SpecialSubgroups.center_SL2_eq_Z]; exact SpecialSubgroups.card_Z_le_two
    have he2 : Nat.card (center SL(2,F)) = 2 := by
      have := Nat.card_pos (α := center SL(2,F)); omega
    have hp_ne_two : p ≠ 2 := by
      intro hp2
      subst hp2
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have he1 : Nat.card (center SL(2,F)) = 1 := by
        rw [SpecialSubgroups.center_SL2_eq_Z]
        exact SpecialSubgroups.card_Z_eq_one_of_two_eq_zero h2
      omega
    have hcardG24 : Nat.card (↥G) = 24 := by rw [hg, he2, hgeq12]
    -- `A₂`'s `Q₈`-shaped generator pair (Butler tex ~1579-1581), via the shared extraction.
    have hA2_card' : Nat.card A2 = 2 * g2 := by rw [hA2_card, he2]
    obtain ⟨x0, y0, hx0_ord, hy0_2, hconj0, hyx0, hx0_mem_A2⟩ :=
      exists_Q8_generators_of_relIndex_two G A2 center_le_G hA2_mem hA2_cyc hA2_cop g2 hg2_ge
        hA2_card' hA2_relIndex hp_ne_two
    have hx0_ord4 : orderOf x0 = 4 := by rw [hx0_ord, hg2eq2]
    have hy0_2' : y0 ^ 2 = x0 ^ 2 := by rw [hy0_2, hg2eq2]
    have hA2_card4 : Nat.card A2 = 4 := by rw [hA2_card', hg2eq2]
    have hA1_card6 : Nat.card A1 = 6 := by rw [hA1_card, he2, hg1eq3]
    -- The gap documented above (Butler tex ~1587-1637, the "orbit cycle" argument on the `3`
    -- conjugates of `A₂`) is closed using `hComplete` (Theorem 6.8's numeric class equation):
    -- `N_G(A₂)` is shown to be the *unique* Sylow `2`-subgroup of `G` (via a global element-order
    -- count, `hComplete`-driven), hence normal; an order-`3` generator `r0` of `A₁`'s cyclic
    -- subgroup then acts on it by conjugation, and since `zpowers y1` (`y1 := r0 x0 r0⁻¹`) is
    -- forced -- by the SAME `hComplete`-driven "only `A₁, A₂`-classes" argument, now applied to
    -- the *third* conjugate `zpowers (x0 y1)` -- to coincide with one of the two remaining
    -- conjugates of `A₂` inside `N_G(A₂)`, the exact relations Butler needs are pinned down (up
    -- to replacing `r0` by `r0²` in the second of his two cases).
    classical
    -- **Step 1**: `N := N_G(A₂)` has cardinality `8`, hence `[G : N] = 3`.
    set A2' : Subgroup ↥G := A2.subgroupOf G with hA2'_def
    set N : Subgroup ↥G := normalizer (A2' : Set ↥G) with hN_def
    have hA2'_le_N : A2' ≤ N := Subgroup.le_normalizer
    have hcard_N : Nat.card N = 8 := by
      have h1 : Nat.card N = Nat.card (↥N ⧸ A2'.subgroupOf N) * Nat.card (A2'.subgroupOf N) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
      have h2 : Nat.card (A2'.subgroupOf N) = Nat.card A2' :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA2'_le_N).toEquiv
      have h3 : Nat.card (↥N ⧸ A2'.subgroupOf N) = A2'.relIndex N := rfl
      have hA2'_card : Nat.card A2' = Nat.card A2 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA2_mem.right).toEquiv
      rw [h2, h3, hA2_relIndex, hA2'_card, hA2_card4] at h1
      omega
    have hindexN : Nat.card N * N.index = Nat.card ↥G := Subgroup.card_mul_index N
    have hindex3 : N.index = 3 := by rw [hcard_N] at hindexN; omega
    -- **Step 2**: an order-`3` element `r0 : SL(2,F)`, `r0 ∈ A1` (hence `r0 ∈ G`).
    haveI hA1fin : Finite A1 := Nat.finite_of_card_ne_zero (by rw [hA1_card6]; norm_num)
    obtain ⟨a1, ha1_gen⟩ := hA1_cyc.exists_generator
    have horder_a1 : orderOf a1 = 6 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers ha1_gen, hA1_card6]
    have horder_a1SL : orderOf (a1 : SL(2,F)) = 6 := by rw [orderOf_coe, horder_a1]
    set r0 : SL(2,F) := (a1 : SL(2,F)) ^ 2 with hr0_def
    have hr0_ord : orderOf r0 = 3 := by
      rw [hr0_def, orderOf_pow' _ (by norm_num : (2:ℕ) ≠ 0), horder_a1SL]
      norm_num
    have hr0_mem_A1 : r0 ∈ A1 := Subgroup.pow_mem A1 a1.2 2
    have hr0_mem_G : r0 ∈ G := hA1_mem.right hr0_mem_A1
    have hr0_ne_one : r0 ≠ 1 := by
      intro h
      rw [orderOf_eq_one_iff.mpr h] at hr0_ord
      omega
    have hr0_cube : r0 ^ 3 = 1 := by
      rw [← hr0_ord]; exact pow_orderOf_eq_one r0
    set r0G : ↥G := ⟨r0, hr0_mem_G⟩ with hr0G_def
    have hr0G_cube : r0G ^ 3 = 1 := Subtype.ext (by rw [hr0G_def]; exact hr0_cube)
    -- **Step 3**: `A₂' = ⟨x₀⟩` (as subgroups of `↥G`).
    have hA2'_card : Nat.card A2' = 4 := by
      rw [hA2'_def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA2_mem.right).toEquiv, hA2_card4]
    have hx0_mem_A2' : x0 ∈ A2' := by rw [hA2'_def, Subgroup.mem_subgroupOf]; exact hx0_mem_A2
    have hzx0_le_A2' : Subgroup.zpowers x0 ≤ A2' := by
      rw [Subgroup.zpowers_le]; exact hx0_mem_A2'
    have hcard_zx0 : Nat.card (Subgroup.zpowers x0) = 4 := by
      rw [← hx0_ord4]; exact (Nat.card_zpowers x0)
    have hA2'_eq_zpowers_x0 : A2' = Subgroup.zpowers x0 := by
      apply SetLike.coe_injective
      symm
      exact Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.mpr hzx0_le_A2')
        (by show Nat.card A2' ≤ Nat.card (Subgroup.zpowers x0); rw [hA2'_card, hcard_zx0])
    -- **Step 4**: `r0G` does not centralize `x0` (else it would lie in `A2'` by maximality,
    -- contradicting `orderOf r0G = 3 ∤ 4 = Nat.card A2'`).
    haveI hA2'comm : IsMulCommutative A2' := hA2_mem.left.1
    have hnc : ¬ Commute r0G x0 := by
      intro hcomm
      have hcomm_all : ∀ a ∈ A2', Commute r0G a := by
        intro a ha
        rw [hA2'_eq_zpowers_x0, Subgroup.mem_zpowers_iff] at ha
        obtain ⟨n, hn⟩ := ha
        rw [← hn]
        exact hcomm.zpow_right n
      set K : Set ↥G := (A2' : Set ↥G) ∪ {r0G} with hK_def
      have hcomm_K : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
        rintro a (ha | ha) b (hb | hb)
        · exact setLike_mul_comm ha hb
        · simp only [Set.mem_singleton_iff] at hb; subst hb
          exact (hcomm_all a ha).symm
        · simp only [Set.mem_singleton_iff] at ha; subst ha
          exact hcomm_all b hb
        · simp only [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
      haveI hKcomm : IsMulCommutative (Subgroup.closure K) := Subgroup.isMulCommutative_closure hcomm_K
      have hA2'_le_closure : A2' ≤ Subgroup.closure K := by
        rw [← Subgroup.closure_eq A2']; exact Subgroup.closure_mono Set.subset_union_left
      have hclosure_le : Subgroup.closure K ≤ A2' := hA2_mem.left.2 hKcomm hA2'_le_closure
      have hr0G_mem_closure : r0G ∈ Subgroup.closure K := subset_closure (Set.mem_union_right _ rfl)
      have hr0G_mem_A2' : r0G ∈ A2' := hclosure_le hr0G_mem_closure
      have hdvd : orderOf r0G ∣ Nat.card A2' := by
        have h1 := orderOf_dvd_natCard (⟨r0G, hr0G_mem_A2'⟩ : A2')
        have h2 : orderOf (⟨r0G, hr0G_mem_A2'⟩ : A2') = orderOf r0G :=
          (orderOf_injective A2'.subtype (Subgroup.subtype_injective A2') ⟨r0G, hr0G_mem_A2'⟩).symm
        rwa [h2] at h1
      rw [hA2'_card] at hdvd
      have hr0G_ord : orderOf r0G = 3 := by
        have h := orderOf_injective G.subtype (Subgroup.subtype_injective G) r0G
        rw [← h, hr0G_def]; exact hr0_ord
      rw [hr0G_ord] at hdvd
      norm_num at hdvd
    -- **Step 5**: work at the `SL(2,F)` level. `A2 = zpowers x0SL`, `x0SL² = -1` (the unique
    -- involution), and `y1 := r0 * x0SL * r0⁻¹` satisfies the `Q₈` relations relative to `x0SL`.
    haveI hA2fin : Finite A2 := Nat.finite_of_card_ne_zero (by rw [hA2_card4]; norm_num)
    set x0SL : SL(2,F) := (x0 : SL(2,F)) with hx0SL_def
    have hx0SL_ord4 : orderOf x0SL = 4 := by rw [hx0SL_def, orderOf_coe]; exact hx0_ord4
    have hzx0SL_le_A2 : Subgroup.zpowers x0SL ≤ A2 := by
      rw [Subgroup.zpowers_le]; exact hx0_mem_A2
    have hcard_zx0SL : Nat.card (Subgroup.zpowers x0SL) = 4 := by
      rw [← hx0SL_ord4]; exact Nat.card_zpowers x0SL
    have hA2_eq_zpowers_x0SL : A2 = Subgroup.zpowers x0SL := by
      apply SetLike.coe_injective
      symm
      exact Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.mpr hzx0SL_le_A2)
        (by show Nat.card A2 ≤ Nat.card (Subgroup.zpowers x0SL); rw [hA2_card4, hcard_zx0SL])
        (Set.toFinite (A2 : Set SL(2,F)))
    haveI hF2 : NeZero (2 : F) := ⟨by
      intro h2
      have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
      exact hp_ne_two (CharP.eq F (‹CharP F p› : CharP F p) hCharP2)⟩
    have hx0SL_sq : x0SL ^ 2 = -1 := by
      have hord2 : orderOf (x0SL ^ 2) = 2 := by
        rw [orderOf_pow' x0SL (by norm_num : (2 : ℕ) ≠ 0), hx0SL_ord4]; norm_num
      exact SpecialSubgroups.exists_unique_orderOf_eq_two.unique hord2
        SpecialSubgroups.orderOf_neg_one_eq_two
    have hneg_one_central : ∀ g : SL(2,F), g * (-1 : SL(2,F)) = (-1 : SL(2,F)) * g := by
      intro g
      have hcen : (-1 : SL(2,F)) ∈ center SL(2,F) := by
        rw [SpecialSubgroups.center_SL2_eq_Z]; exact SpecialSubgroups.neg_one_mem_Z
      exact Subgroup.mem_center_iff.mp hcen g
    set r0inv : SL(2,F) := r0⁻¹ with hr0inv_def
    set y1 : SL(2,F) := r0 * x0SL * r0⁻¹ with hy1_def
    have hy1_ord4 : orderOf y1 = 4 := by
      rw [hy1_def, orderOf_conj]; exact hx0SL_ord4
    have hy1_sq : y1 ^ 2 = -1 := by
      have h1 : y1 ^ 2 = r0 * (x0SL ^ 2) * r0⁻¹ := by
        rw [hy1_def, sq, sq]
        group
      rw [h1, hx0SL_sq, hneg_one_central r0]
      group
    -- `y1 ≠ x0SL` (else `r0` centralizes `x0SL`, contradicting `hnc`).
    have hy1_ne_x0SL : y1 ≠ x0SL := by
      intro heq
      apply hnc
      have h1 : r0 * x0SL = x0SL * r0 := by
        have h2 := congrArg (· * r0) heq
        simpa [hy1_def, mul_assoc] using h2
      show r0G * x0 = x0 * r0G
      apply Subtype.ext
      simpa [hr0G_def, hx0SL_def] using h1
    -- `y1 ≠ x0SL⁻¹` (else, since `r0³ = 1`, applying the conjugation `3` times forces
    -- `x0SL = x0SL⁻¹`, contradicting `orderOf x0SL = 4`).
    have hy1_ne_x0SL_inv : y1 ≠ x0SL⁻¹ := by
      intro heq
      set c2 : SL(2,F) := r0 * y1 * r0⁻¹ with hc2_def
      set c3 : SL(2,F) := r0 * c2 * r0⁻¹ with hc3_def
      have hc2_eq : c2 = x0SL := by
        rw [hc2_def, heq]
        have : r0 * x0SL⁻¹ * r0⁻¹ = (r0 * x0SL * r0⁻¹)⁻¹ := by group
        rw [this, ← hy1_def, heq, inv_inv]
      have hc3_eq : c3 = y1 := by rw [hc3_def, hc2_eq, hy1_def]
      have hcube_eq : r0 * r0 * r0 = r0 ^ 3 := by rw [pow_succ, pow_succ, pow_one]
      have hiter : c3 = r0 ^ 3 * x0SL * (r0 ^ 3)⁻¹ := by
        rw [hc3_def, hc2_def, hy1_def, ← hcube_eq]; group
      rw [hr0_cube] at hiter
      simp only [one_mul, inv_one, mul_one] at hiter
      rw [hc3_eq, heq] at hiter
      have hxeq : x0SL = x0SL⁻¹ := hiter.symm
      have hone : x0SL * x0SL⁻¹ = 1 := mul_inv_cancel x0SL
      rw [← hxeq] at hone
      have : x0SL ^ 2 = 1 := by rw [sq]; exact hone
      have hdvd : orderOf x0SL ∣ 2 := orderOf_dvd_of_pow_eq_one this
      rw [hx0SL_ord4] at hdvd
      norm_num at hdvd
    -- **Step 6**: `B0 := conj r0 • A2` is maximal abelian, equal to `zpowers y1`, and `≠ A2`.
    set B0 : Subgroup SL(2,F) := conj r0 • A2 with hB0_def
    have hB0_eq : B0 = Subgroup.zpowers y1 := by
      rw [hB0_def, hA2_eq_zpowers_x0SL, conj_zpowers_eq, ← hy1_def]
    have hB0_mem : B0 ∈ MaximalAbelianSubgroupsOf G :=
      conj_smul_mem_MaximalAbelianSubgroupsOf_of_mem hA2_mem hr0_mem_G
    have hB0_ne_A2 : B0 ≠ A2 := by
      intro hcontra
      have hy1_mem : y1 ∈ A2 := by
        rw [← hcontra, hB0_eq]
        exact Subgroup.mem_zpowers y1
      rw [hA2_eq_zpowers_x0SL] at hy1_mem
      haveI hfo : IsOfFinOrder x0SL := orderOf_pos_iff.mp (hx0SL_ord4 ▸ (by norm_num))
      rw [hfo.mem_zpowers_iff_mem_range_orderOf] at hy1_mem
      simp only [Finset.mem_image, Finset.mem_range] at hy1_mem
      obtain ⟨m, hm_lt, hm_eq⟩ := hy1_mem
      rw [hx0SL_ord4] at hm_lt
      interval_cases m
      · simp only [pow_zero] at hm_eq
        rw [← hm_eq, orderOf_one] at hy1_ord4
        norm_num at hy1_ord4
      · rw [pow_one] at hm_eq
        exact hy1_ne_x0SL hm_eq.symm
      · rw [hx0SL_sq] at hm_eq
        rw [← hm_eq] at hy1_ord4
        have : orderOf (-1 : SL(2,F)) = 2 := SpecialSubgroups.orderOf_neg_one_eq_two
        rw [this] at hy1_ord4
        norm_num at hy1_ord4
      · have h4 : x0SL ^ 4 = 1 := by rw [← hx0SL_ord4]; exact pow_orderOf_eq_one x0SL
        have hmul1 : x0SL ^ 3 * x0SL = 1 := by rw [← pow_succ]; exact h4
        have hx0cubed : x0SL ^ 3 = x0SL⁻¹ := eq_inv_of_mul_eq_one_left hmul1
        exact hy1_ne_x0SL_inv (by rw [← hx0cubed]; exact hm_eq.symm)
    have hcard_B0 : Nat.card B0 = 4 := by
      rw [hB0_eq]; rw [← hy1_ord4]; exact Nat.card_zpowers y1
    -- **General fact**: no `IsSylowType` subgroup of `G` has cardinality divisible by `4`
    -- (its Sylow `p`-part `Q` is forced to have `Nat.card Q = 3` -- since `p ∣ Nat.card G = 24`
    -- and `p ≠ 2` forces `p = 3`, and `Nat.card Q` a power of `3` dividing `24` forces the power
    -- to be exactly `3^1` -- and `Q` is disjoint from the order-`2` center, so `Nat.card (Q ⊔ Z F)
    -- = 3 * 2 = 6`, not divisible by `4`).
    have hNoSylowDiv4 : ∀ B : Subgroup SL(2,F), IsSylowType p G B → ¬ (4 : ℕ) ∣ Nat.card B := by
      intro B hsyl h4dvd
      obtain ⟨Qp, hQnontriv, hQfin, hQ_le, hB_eq, hQelem, S, hQS⟩ := hsyl
      haveI := hQfin
      have hQ_bot_lt : (⊥ : Subgroup SL(2,F)) < Qp :=
        bot_lt_iff_ne_bot.mpr ((Subgroup.nontrivial_iff_ne_bot Qp).mp hQnontriv)
      have hQ_isPGroup : IsPGroup p Qp :=
        IsElementaryAbelian.IsPGroup p (Fact.out : Nat.Prime p) Qp hQelem hQ_bot_lt
      obtain ⟨k, hQcard_eq_pk⟩ := IsPGroup.iff_card.mp hQ_isPGroup
      have hQcard_ne1 : Nat.card Qp ≠ 1 := by
        intro h1
        exact ((Subgroup.nontrivial_iff_ne_bot Qp).mp hQnontriv) (Subgroup.card_eq_one.mp h1)
      have hQdvd24 : Nat.card Qp ∣ 24 := by
        rw [← hcardG24]
        calc Nat.card Qp = Nat.card (Qp.subgroupOf G) :=
              (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le).toEquiv).symm
          _ ∣ Nat.card ↥G := Subgroup.card_subgroup_dvd_card _
      rw [hQcard_eq_pk] at hQdvd24
      have hpdvd24 : p ∣ 24 := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · exfalso; apply hQcard_ne1; rw [hQcard_eq_pk, hk0]; norm_num
        · exact (dvd_pow_self p hkpos.ne').trans hQdvd24
      have h24eq : (24 : ℕ) = 2 ^ 3 * 3 := by norm_num
      rw [h24eq] at hpdvd24
      have hp3 : p = 3 := by
        rcases (Fact.out : Nat.Prime p).dvd_mul.mp hpdvd24 with h | h
        · exact absurd ((Fact.out : Nat.Prime p).dvd_of_dvd_pow h) (by
            intro hp2
            exact hp_ne_two ((Nat.prime_two.eq_one_or_self_of_dvd p hp2).resolve_left
              (Fact.out : Nat.Prime p).one_lt.ne'))
        · exact (Nat.prime_three.eq_one_or_self_of_dvd p h).resolve_left (Fact.out : Nat.Prime p).one_lt.ne'
      subst hp3
      have hk_le1 : k ≤ 1 := by
        by_contra hcon
        push_neg at hcon
        have h9dvd : (9 : ℕ) ∣ 3 ^ k := by
          calc (9 : ℕ) = 3 ^ 2 := by norm_num
            _ ∣ 3 ^ k := pow_dvd_pow 3 hcon
        have h924 : (9 : ℕ) ∣ 24 := h9dvd.trans hQdvd24
        norm_num at h924
      have hk_ge1 : 1 ≤ k := by
        by_contra hcon
        push_neg at hcon
        interval_cases k
        exact hQcard_ne1 (by rw [hQcard_eq_pk]; norm_num)
      have hk1 : k = 1 := le_antisymm hk_le1 hk_ge1
      have hQcard3 : Nat.card Qp = 3 := by rw [hQcard_eq_pk, hk1]; norm_num
      -- `Qp` and `Z F` are disjoint (coprime cardinalities `3`, `2`).
      have hZF_card : Nat.card (SpecialSubgroups.Z F) = 2 := by
        rw [← SpecialSubgroups.center_SL2_eq_Z]; exact he2
      have hdisj : Disjoint Qp (SpecialSubgroups.Z F) := by
        rw [disjoint_iff]
        apply (Subgroup.eq_bot_iff_forall _).mpr
        intro x hx
        rw [Subgroup.mem_inf] at hx
        have hd1 : orderOf (⟨x, hx.1⟩ : Qp) ∣ Nat.card Qp := orderOf_dvd_natCard _
        have hd2 : orderOf (⟨x, hx.2⟩ : SpecialSubgroups.Z F) ∣ Nat.card (SpecialSubgroups.Z F) :=
          orderOf_dvd_natCard _
        have he1 : orderOf (⟨x, hx.1⟩ : Qp) = orderOf x :=
          (orderOf_injective Qp.subtype (Subgroup.subtype_injective Qp) _).symm
        have he2' : orderOf (⟨x, hx.2⟩ : SpecialSubgroups.Z F) = orderOf x :=
          (orderOf_injective (SpecialSubgroups.Z F).subtype
            (Subgroup.subtype_injective (SpecialSubgroups.Z F)) _).symm
        rw [he1, hQcard3] at hd1
        rw [he2', hZF_card] at hd2
        have hdvd1 : orderOf x ∣ Nat.gcd 3 2 := Nat.dvd_gcd hd1 hd2
        have hgcd1 : Nat.gcd 3 2 = 1 := by norm_num
        rw [hgcd1] at hdvd1
        have hone : orderOf x = 1 := Nat.eq_one_of_dvd_one hdvd1
        exact orderOf_eq_one_iff.mp hone
      have hQle_G : Qp ≤ G := hQ_le
      have hZFle_G : SpecialSubgroups.Z F ≤ G := by
        rw [← SpecialSubgroups.center_SL2_eq_Z]; exact center_le_G
      haveI hZFGnormal : ((SpecialSubgroups.Z F).subgroupOf G).Normal := by
        constructor
        intro n hn g
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        have hcen : (n : SL(2,F)) ∈ center SL(2,F) := by
          rw [SpecialSubgroups.center_SL2_eq_Z]; exact hn
        have hcomm : (g : SL(2,F)) * (n : SL(2,F)) = (n : SL(2,F)) * (g : SL(2,F)) :=
          Subgroup.mem_center_iff.mp hcen (g : SL(2,F))
        have : (g : SL(2,F)) * (n : SL(2,F)) * (g : SL(2,F))⁻¹ = (n : SL(2,F)) := by
          rw [hcomm]; group
        show (↑(g * n * g⁻¹) : SL(2,F)) ∈ SpecialSubgroups.Z F
        rw [show (↑(g * n * g⁻¹) : SL(2,F)) = (g:SL(2,F)) * (n:SL(2,F)) * (g:SL(2,F))⁻¹ by
          simp, this]
        exact hn
      have hsup_subgroupOf : (Qp ⊔ SpecialSubgroups.Z F).subgroupOf G
          = Qp.subgroupOf G ⊔ (SpecialSubgroups.Z F).subgroupOf G :=
        Subgroup.subgroupOf_sup hQle_G hZFle_G
      have hdisj' : Disjoint (Qp.subgroupOf G) ((SpecialSubgroups.Z F).subgroupOf G) := by
        rw [disjoint_iff]
        apply (Subgroup.eq_bot_iff_forall _).mpr
        intro x hx
        rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
        have hxbot : (x : SL(2,F)) ∈ (⊥ : Subgroup SL(2,F)) := by
          rw [← disjoint_iff.mp hdisj]; exact Subgroup.mem_inf.mpr hx
        rw [Subgroup.mem_bot] at hxbot
        exact Subtype.ext hxbot
      have hcard_sup : Nat.card ((Qp ⊔ SpecialSubgroups.Z F).subgroupOf G)
          = Nat.card (Qp.subgroupOf G) * Nat.card ((SpecialSubgroups.Z F).subgroupOf G) := by
        rw [hsup_subgroupOf]
        exact card_sup_eq_of_disjoint_of_normal hdisj'
      have hcard_QsupZF : Nat.card (Qp ⊔ SpecialSubgroups.Z F : Subgroup SL(2,F)) = 6 := by
        have h1 : Nat.card ((Qp ⊔ SpecialSubgroups.Z F).subgroupOf G)
            = Nat.card (Qp ⊔ SpecialSubgroups.Z F : Subgroup SL(2,F)) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (_root_.sup_le hQle_G hZFle_G)).toEquiv
        have h2 : Nat.card (Qp.subgroupOf G) = Nat.card Qp :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQle_G).toEquiv
        have h3 : Nat.card ((SpecialSubgroups.Z F).subgroupOf G) = Nat.card (SpecialSubgroups.Z F) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZFle_G).toEquiv
        rw [← h1, hcard_sup, h2, h3, hQcard3, hZF_card]
      rw [hB_eq, hcard_QsupZF] at h4dvd
      norm_num at h4dvd
    have hB0_conj_A2 : ∃ c ∈ G, conj c • B0 = A2 := by
      rcases hComplete B0 hB0_mem with ⟨c, hcG, hc⟩ | ⟨c, hcG, hc⟩ | hsyl
      · exfalso
        have hthis : Nat.card (conj c • B0 : Subgroup SL(2,F)) = Nat.card B0 :=
          card_conj_smul_eq_card c
        rw [hc, hcard_B0, hA1_card6] at hthis
        norm_num at hthis
      · exact ⟨c, hcG, hc⟩
      · exact absurd (hcard_B0 ▸ (by norm_num : (4:ℕ) ∣ 4)) (hNoSylowDiv4 B0 hsyl)
    -- **Step 8**: the same argument, applied via `centralizer {z} ⊓ G`, shows that *any* order-`4`
    -- element `z ∈ G` generates a cyclic subgroup `G`-conjugate to `A2`.
    have key : ∀ z : SL(2,F), z ∈ G → orderOf z = 4 → ∃ c ∈ G, conj c • Subgroup.zpowers z = A2 := by
      intro z hzG hz4
      have hz_noncentral : z ∉ center SL(2,F) := by
        intro hzc
        haveI : Finite (center SL(2,F)) := Nat.finite_of_card_ne_zero (by rw [he2]; norm_num)
        have hdvd : orderOf (⟨z, hzc⟩ : center SL(2,F)) ∣ Nat.card (center SL(2,F)) :=
          orderOf_dvd_natCard _
        have heq : orderOf (⟨z, hzc⟩ : center SL(2,F)) = orderOf z :=
          (orderOf_injective (center SL(2,F)).subtype (Subgroup.subtype_injective _) _).symm
        rw [heq, hz4, he2] at hdvd
        norm_num at hdvd
      set Cz : Subgroup SL(2,F) := centralizer {z} ⊓ G with hCz_def
      have hCz_mem : Cz ∈ MaximalAbelianSubgroupsOf G :=
        centralizer_inf_mem_maximalAbelianSubgroupsOf_of_noncentral G z ⟨hzG, hz_noncentral⟩
      have hz_mem_Cz : z ∈ Cz := by
        rw [hCz_def, Subgroup.mem_inf]; exact ⟨mem_centralizer_self z, hzG⟩
      haveI hCzfin : Finite Cz :=
        (Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hCz_mem.right).to_subtype
      have hdvd4 : (4 : ℕ) ∣ Nat.card Cz := by
        have h1 : orderOf (⟨z, hz_mem_Cz⟩ : Cz) ∣ Nat.card Cz := orderOf_dvd_natCard _
        have h2 : orderOf (⟨z, hz_mem_Cz⟩ : Cz) = orderOf z :=
          (orderOf_injective Cz.subtype (Subgroup.subtype_injective Cz) _).symm
        rwa [h2, hz4] at h1
      rcases hComplete Cz hCz_mem with ⟨c, hcG, hc⟩ | ⟨c, hcG, hc⟩ | hsyl
      · exfalso
        have hthis : Nat.card (conj c • Cz : Subgroup SL(2,F)) = Nat.card Cz :=
          card_conj_smul_eq_card c
        rw [hc, hA1_card6] at hthis
        rw [← hthis] at hdvd4
        norm_num at hdvd4
      · refine ⟨c, hcG, ?_⟩
        have hthis : Nat.card (conj c • Cz : Subgroup SL(2,F)) = Nat.card Cz :=
          card_conj_smul_eq_card c
        rw [hc, hA2_card4] at hthis
        have hCzcard4 : Nat.card Cz = 4 := hthis.symm
        have hzz_le_Cz : Subgroup.zpowers z ≤ Cz := by
          rw [Subgroup.zpowers_le]; exact hz_mem_Cz
        have hcard_zz : Nat.card (Subgroup.zpowers z) = 4 := by rw [← hz4]; exact Nat.card_zpowers z
        have hCz_eq_zz : Cz = Subgroup.zpowers z := by
          apply SetLike.coe_injective
          symm
          exact Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.mpr hzz_le_Cz)
            (by show Nat.card Cz ≤ Nat.card (Subgroup.zpowers z); rw [hCzcard4, hcard_zz])
            (Set.toFinite (Cz : Set SL(2,F)))
        rw [← hCz_eq_zz]; exact hc
      · exact absurd hdvd4 (hNoSylowDiv4 Cz hsyl)
    -- **Step 9**: `y0SL`, `z0SL := x0SL * y0SL` (Butler's `y`, `xy`) also have order `4`, square to
    -- `-1`, and each of `x0SL`, `y0SL`, `z0SL` inverts the "next" one -- so no one of the three
    -- lies in the `zpowers` of another, i.e. `A2 = zpowers x0SL`, `zpowers y0SL`, `zpowers z0SL`
    -- are pairwise distinct.
    set y0SL : SL(2,F) := (y0 : SL(2,F)) with hy0SL_def
    have hy0_2SL : y0SL ^ 2 = x0SL ^ 2 := by
      rw [hy0SL_def, hx0SL_def]
      have := congrArg (Subtype.val) hy0_2'
      push_cast at this
      exact_mod_cast this
    have hconj0SL : y0SL * x0SL * y0SL⁻¹ = x0SL⁻¹ := by
      rw [hy0SL_def, hx0SL_def]
      have := congrArg (Subtype.val) hconj0
      push_cast at this
      exact_mod_cast this
    have hyx0SL : y0SL ∉ A2 := by
      rw [hA2_eq_zpowers_x0SL]
      intro hmem
      apply hyx0
      rw [Subgroup.mem_zpowers_iff] at hmem ⊢
      obtain ⟨n, hn⟩ := hmem
      refine ⟨n, ?_⟩
      apply Subtype.ext
      push_cast
      rw [← hx0SL_def, ← hy0SL_def]
      exact hn
    have hnegone_sq : (-1 : SL(2,F)) ^ 2 = 1 := by simp
    have hy0SL_sq : y0SL ^ 2 = -1 := by rw [hy0_2SL, hx0SL_sq]
    have hy0SL_ord4 : orderOf y0SL = 4 := by
      have hne1 : y0SL ^ 2 ≠ 1 := by
        rw [hy0SL_sq]
        intro h
        exact hp_ne_two (by
          have h2 : (2:F) = 0 := by
            by_contra h2ne
            haveI : NeZero (2:F) := ⟨h2ne⟩
            have := SpecialSubgroups.orderOf_neg_one_eq_two (F := F)
            rw [h] at this
            simp at this
          have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
          exact (CharP.eq F (‹CharP F p› : CharP F p) hCharP2 : p = 2))
      have h4 : y0SL ^ 4 = 1 := by
        have heq : y0SL ^ 4 = (y0SL ^ 2) ^ 2 := by rw [← pow_mul]
        rw [heq, hy0SL_sq, hnegone_sq]
      have hdvd4 : orderOf y0SL ∣ 4 := orderOf_dvd_of_pow_eq_one h4
      have hndvd2 : ¬ orderOf y0SL ∣ 2 := by
        intro h
        exact hne1 (orderOf_dvd_iff_pow_eq_one.mp h)
      have hne1' : orderOf y0SL ≠ 1 := by intro h; apply hndvd2; rw [h]; norm_num
      have hne2' : orderOf y0SL ≠ 2 := by intro h; apply hndvd2; rw [h]
      have hle4 : orderOf y0SL ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
      have hpos : 0 < orderOf y0SL :=
        orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, h4⟩)
      interval_cases (orderOf y0SL) <;> omega
    set z0SL : SL(2,F) := x0SL * y0SL with hz0SL_def
    -- `y0SL x0SL = x0SL⁻¹ y0SL` (rearranging `hconj0SL`).
    have hyx0rearr : y0SL * x0SL = x0SL⁻¹ * y0SL := by
      have h2 : y0SL * x0SL * y0SL⁻¹ * y0SL = x0SL⁻¹ * y0SL := by rw [hconj0SL]
      rwa [mul_assoc, inv_mul_cancel, mul_one] at h2
    have hz0SL_sq : z0SL ^ 2 = -1 := by
      have step : z0SL ^ 2 = x0SL * (y0SL * x0SL) * y0SL := by rw [hz0SL_def, sq]; group
      rw [step, hyx0rearr]
      have step2 : x0SL * (x0SL⁻¹ * y0SL) * y0SL = y0SL * y0SL := by group
      rw [step2, ← sq, hy0SL_sq]
    have hz0SL_ne1 : z0SL ≠ 1 := by
      intro h
      apply hyx0SL
      rw [hA2_eq_zpowers_x0SL, Subgroup.mem_zpowers_iff]
      refine ⟨-1, ?_⟩
      have hxz : x0SL⁻¹ * z0SL = y0SL := by rw [hz0SL_def]; group
      rw [← hxz, h, mul_one, _root_.zpow_neg_one]
    have hz0SL_ord4 : orderOf z0SL = 4 := by
      have hne1 : z0SL ^ 2 ≠ 1 := by
        rw [hz0SL_sq]
        intro h
        exact hp_ne_two (by
          have h2 : (2:F) = 0 := by
            by_contra h2ne
            haveI : NeZero (2:F) := ⟨h2ne⟩
            have := SpecialSubgroups.orderOf_neg_one_eq_two (F := F)
            rw [h] at this
            simp at this
          have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
          exact (CharP.eq F (‹CharP F p› : CharP F p) hCharP2 : p = 2))
      have h4 : z0SL ^ 4 = 1 := by
        have heq : z0SL ^ 4 = (z0SL ^ 2) ^ 2 := by rw [← pow_mul]
        rw [heq, hz0SL_sq, hnegone_sq]
      have hdvd4 : orderOf z0SL ∣ 4 := orderOf_dvd_of_pow_eq_one h4
      have hndvd2 : ¬ orderOf z0SL ∣ 2 := by
        intro h; exact hne1 (orderOf_dvd_iff_pow_eq_one.mp h)
      have hne1' : orderOf z0SL ≠ 1 := by intro h; apply hndvd2; rw [h]; norm_num
      have hne2' : orderOf z0SL ≠ 2 := by intro h; apply hndvd2; rw [h]
      have hle4 : orderOf z0SL ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
      have hpos : 0 < orderOf z0SL :=
        orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, h4⟩)
      interval_cases (orderOf z0SL) <;> omega
    -- **Step 10**: `x0SL`, `y0SL`, `z0SL` pairwise invert each other, hence generate `3` pairwise
    -- distinct cyclic subgroups (`A2`, `zpowers y0SL`, `zpowers z0SL`).
    have hneg_eq : ∀ a : SL(2,F), a ^ 2 = -1 → a ^ 4 = 1 → a⁻¹ = -a := by
      intro a ha2 ha4
      have h3 : a ^ 3 = a * a ^ 2 := pow_succ' a 2
      have h3' : a ^ 3 = -a := by rw [h3, ha2, mul_neg, mul_one]
      have hmul : a * a ^ 3 = a ^ 4 := (pow_succ' a 3).symm
      have h1 : a * a ^ 3 = 1 := by rw [hmul, ha4]
      rw [h3'] at h1
      exact inv_eq_of_mul_eq_one_right h1
    have hx0SL4 : x0SL ^ 4 = 1 := by
      have heq : x0SL ^ 4 = (x0SL ^ 2) ^ 2 := by rw [← pow_mul]
      rw [heq, hx0SL_sq, hnegone_sq]
    have hy0SL4 : y0SL ^ 4 = 1 := by
      have heq : y0SL ^ 4 = (y0SL ^ 2) ^ 2 := by rw [← pow_mul]
      rw [heq, hy0SL_sq, hnegone_sq]
    have hz0SL4 : z0SL ^ 4 = 1 := by
      have heq : z0SL ^ 4 = (z0SL ^ 2) ^ 2 := by rw [← pow_mul]
      rw [heq, hz0SL_sq, hnegone_sq]
    have hx0SLinv : x0SL⁻¹ = -x0SL := hneg_eq x0SL hx0SL_sq hx0SL4
    have hy0SLinv : y0SL⁻¹ = -y0SL := hneg_eq y0SL hy0SL_sq hy0SL4
    have hz0SLinv : z0SL⁻¹ = -z0SL := hneg_eq z0SL hz0SL_sq hz0SL4
    -- `x0SL` inverts `y0SL`.
    have hxinvy : x0SL * y0SL * x0SL⁻¹ = y0SL⁻¹ := by
      have h1 : x0SL * y0SL * x0SL = y0SL := by
        have h1' : x0SL * (y0SL * x0SL) = x0SL * (x0SL⁻¹ * y0SL) := congrArg (x0SL * ·) hyx0rearr
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h1'
        exact h1'
      rw [hx0SLinv]
      have h2 : x0SL * y0SL * (-x0SL) = -(x0SL * y0SL * x0SL) := mul_neg (x0SL * y0SL) x0SL
      rw [h2, h1, hy0SLinv]
    -- `x0SL` inverts `z0SL`.
    have hxinvz : x0SL * z0SL * x0SL⁻¹ = z0SL⁻¹ := by
      rw [hz0SL_def]
      have h1 : x0SL * (x0SL * y0SL) * x0SL⁻¹ = x0SL * (x0SL * y0SL * x0SL⁻¹) := by group
      rw [h1, show x0SL * y0SL * x0SL⁻¹ = y0SL⁻¹ from hxinvy, hy0SLinv]
      have h2 : x0SL * -y0SL = -(x0SL * y0SL) := mul_neg x0SL y0SL
      rw [h2, ← hz0SL_def, hz0SLinv]
    -- `y0SL` inverts `z0SL`.
    have hyinvz : y0SL * z0SL * y0SL⁻¹ = z0SL⁻¹ := by
      rw [hz0SL_def]
      have h1 : y0SL * (x0SL * y0SL) * y0SL⁻¹ = (y0SL * x0SL) * (y0SL * y0SL⁻¹) := by group
      rw [h1, mul_inv_cancel, mul_one, hyx0rearr]
      have h2 : x0SL⁻¹ * y0SL = -(x0SL) * y0SL := by rw [hx0SLinv]
      rw [h2]
      have h3 : -x0SL * y0SL = -(x0SL * y0SL) := neg_mul x0SL y0SL
      rw [h3, ← hz0SL_def, hz0SLinv]
    -- General fact: if `a` inverts `b` (`a * b * a⁻¹ = b⁻¹`) and `orderOf b = 4`, then `b` is not
    -- a power of `a`.
    have general_ninv : ∀ a b : SL(2,F), a * b * a⁻¹ = b⁻¹ → orderOf b = 4 →
        b ∉ Subgroup.zpowers a := by
      intro a b hab hb4 hmem
      rw [Subgroup.mem_zpowers_iff] at hmem
      obtain ⟨n, hn⟩ := hmem
      have hcomm : a * b = b * a := by rw [← hn]; group
      have hfix : a * b * a⁻¹ = b := by rw [hcomm]; group
      rw [hfix] at hab
      have hbb : b ^ 2 = 1 := by
        rw [sq]
        have hmi := mul_inv_cancel b
        rwa [← hab] at hmi
      have hdvd : orderOf b ∣ 2 := orderOf_dvd_of_pow_eq_one hbb
      rw [hb4] at hdvd
      norm_num at hdvd
    have hA2_ne_zy : A2 ≠ Subgroup.zpowers y0SL := by
      intro h
      apply hyx0SL
      rw [h]; exact Subgroup.mem_zpowers y0SL
    have hA2_ne_zz : A2 ≠ Subgroup.zpowers z0SL := by
      intro h
      have : z0SL ∈ A2 := by rw [h]; exact Subgroup.mem_zpowers z0SL
      rw [hA2_eq_zpowers_x0SL] at this
      exact general_ninv x0SL z0SL hxinvz hz0SL_ord4 this
    have hzy_ne_zz : Subgroup.zpowers y0SL ≠ Subgroup.zpowers z0SL := by
      intro h
      have : z0SL ∈ Subgroup.zpowers y0SL := by rw [h]; exact Subgroup.mem_zpowers z0SL
      exact general_ninv y0SL z0SL hyinvz hz0SL_ord4 this
    -- **Step 11**: `zpowers y0SL` and `zpowers z0SL` are also `G`-conjugates of `A2` (via `key`),
    -- hence -- together with `A2` itself and `B0` -- (at least) `4` elements of the `3`-element
    -- set `ConjClassOf G A2`, forcing `B0` to coincide with one of `zpowers y0SL`, `zpowers z0SL`.
    have hy0SL_mem_G : y0SL ∈ G := y0.2
    have hz0SL_mem_G : z0SL ∈ G := by
      rw [hz0SL_def]; exact Subgroup.mul_mem G x0.2 hy0SL_mem_G
    obtain ⟨cy, hcyG, hcy⟩ := key y0SL hy0SL_mem_G hy0SL_ord4
    obtain ⟨cz, hczG, hcz⟩ := key z0SL hz0SL_mem_G hz0SL_ord4
    have hCC_card : Nat.card (ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G)) = 3 := by
      rw [card_ConjClassOf_eq_index_normalizer]
      exact hindex3
    have hA2_mem_CC : A2 ∈ ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G) :=
      ⟨1, G.one_mem, by simp⟩
    have hzy_mem_CC : Subgroup.zpowers y0SL ∈
        ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      rw [smul_eq_iff_eq_inv_smul, ← map_inv] at hcy
      exact ⟨cy⁻¹, G.inv_mem hcyG, hcy.symm⟩
    have hzz_mem_CC : Subgroup.zpowers z0SL ∈
        ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      rw [smul_eq_iff_eq_inv_smul, ← map_inv] at hcz
      exact ⟨cz⁻¹, G.inv_mem hczG, hcz.symm⟩
    have hB0_mem_CC : B0 ∈ ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G) :=
      ⟨r0, hr0_mem_G, rfl⟩
    haveI hCCfin : Finite (ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G)) :=
      Nat.finite_of_card_ne_zero (by rw [hCC_card]; norm_num)
    -- Since `{A2, zpowers y0SL, zpowers z0SL}` is a `3`-element subset of the `3`-element set
    -- `ConjClassOf G A2`, they are equal: `ConjClassOf G A2` has *exactly* these `3` members.
    have hCC_eq : ({A2, Subgroup.zpowers y0SL, Subgroup.zpowers z0SL} : Set (Subgroup SL(2,F)))
        = ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      apply Set.eq_of_subset_of_ncard_le
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact hA2_mem_CC
        · exact hzy_mem_CC
        · exact hzz_mem_CC
      · have e1 : ({Subgroup.zpowers y0SL, Subgroup.zpowers z0SL} :
            Set (Subgroup SL(2,F))).ncard = 2 := Set.ncard_pair hzy_ne_zz
        have e2 : ({A2, Subgroup.zpowers y0SL, Subgroup.zpowers z0SL} :
            Set (Subgroup SL(2,F))).ncard = 3 := by
          rw [Set.ncard_insert_of_notMem (by simp [hA2_ne_zy, hA2_ne_zz]), e1]
        have hcceq : (ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G)).ncard
            = Nat.card (ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G)) := rfl
        rw [e2, hcceq, hCC_card]
      · exact Set.toFinite _
    have hB0_cases : B0 = A2 ∨ B0 = Subgroup.zpowers y0SL ∨ B0 = Subgroup.zpowers z0SL := by
      have := hCC_eq ▸ hB0_mem_CC
      simpa using this
    have hB0_cases' : B0 = Subgroup.zpowers y0SL ∨ B0 = Subgroup.zpowers z0SL :=
      hB0_cases.resolve_left hB0_ne_A2
    -- **Step 12**: general algebraic facts about pairs of order-`4`, square-`-1` elements.
    have invert_inv_left : ∀ a b : SL(2,F), a * b * a⁻¹ = b⁻¹ → a⁻¹ * b * a = b⁻¹ := by
      intro a b hab
      have h1 : a * b = b⁻¹ * a := by
        have h1' := congrArg (· * a) hab
        simpa [mul_assoc] using h1'
      have h2 : b = a⁻¹ * b⁻¹ * a := by
        have h2' : a⁻¹ * (a * b) = a⁻¹ * (b⁻¹ * a) := congrArg (a⁻¹ * ·) h1
        rw [← mul_assoc, inv_mul_cancel, one_mul] at h2'
        rw [mul_assoc]; exact h2'
      have h3 : b⁻¹ = a⁻¹ * b * a := by
        have h3' : b⁻¹ = (a⁻¹ * b⁻¹ * a)⁻¹ := congrArg (·⁻¹) h2
        rw [h3', _root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, inv_inv, mul_assoc]
      exact h3.symm
    -- General fact: if `b` inverts `a` (`b*a*b⁻¹=a⁻¹`) and `a² = b²` (both central of order `2`),
    -- then `a` inverts `b`.
    have general_mutual : ∀ a b : SL(2,F), a ^ 2 = -1 → b ^ 2 = -1 → a ^ 4 = 1 → b ^ 4 = 1 →
        b * a * b⁻¹ = a⁻¹ → a * b * a⁻¹ = b⁻¹ := by
      intro a b ha2 hb2 ha4 hb4 hab
      have ainv : a⁻¹ = -a := hneg_eq a ha2 ha4
      have binv : b⁻¹ = -b := hneg_eq b hb2 hb4
      have hrearr : b * a = a⁻¹ * b := by
        have h2 : b * a * b⁻¹ * b = a⁻¹ * b := by rw [hab]
        rwa [mul_assoc, inv_mul_cancel, mul_one] at h2
      have h1 : a * b * a = b := by
        have h1' : a * (b * a) = a * (a⁻¹ * b) := congrArg (a * ·) hrearr
        rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h1'
        exact h1'
      rw [ainv]
      have h2 : a * b * (-a) = -(a * b * a) := mul_neg (a * b) a
      rw [h2, h1, binv]
    -- General fact: an element of order `4` lying in `zpowers a` (`a` also order `4`) is `a` or
    -- `a⁻¹`.
    have order4_mem_zpowers : ∀ a b : SL(2,F), orderOf a = 4 → orderOf b = 4 →
        b ∈ Subgroup.zpowers a → b = a ∨ b = a⁻¹ := by
      intro a b ha4 hb4 hmem
      have ha4' : a ^ 4 = 1 := by rw [← ha4]; exact pow_orderOf_eq_one a
      haveI hfo : IsOfFinOrder a := orderOf_pos_iff.mp (by rw [ha4]; norm_num)
      rw [hfo.mem_zpowers_iff_mem_range_orderOf] at hmem
      simp only [Finset.mem_image, Finset.mem_range] at hmem
      obtain ⟨m, hm_lt, hm_eq⟩ := hmem
      rw [ha4] at hm_lt
      interval_cases m
      · exfalso; rw [pow_zero] at hm_eq; rw [← hm_eq, orderOf_one] at hb4; norm_num at hb4
      · left; rw [pow_one] at hm_eq; exact hm_eq.symm
      · exfalso
        have hb_eq : b = a ^ 2 := hm_eq.symm
        have hsq : (a ^ 2) ^ 2 = 1 := by
          have hpm : (a ^ 2) ^ 2 = a ^ 4 := by rw [← pow_mul]
          rw [hpm, ha4']
        have hordb2 : orderOf b ∣ 2 := by rw [hb_eq]; exact orderOf_dvd_of_pow_eq_one hsq
        rw [hb4] at hordb2
        norm_num at hordb2
      · right
        have hmul1 : a ^ 3 * a = 1 := by rw [← pow_succ]; exact ha4'
        exact (eq_inv_of_mul_eq_one_left hmul1) ▸ hm_eq.symm
    -- `a` inverts `b⁻¹` whenever it inverts `b`.
    have invert_inv_right : ∀ a b : SL(2,F), a * b * a⁻¹ = b⁻¹ → a * b⁻¹ * a⁻¹ = b := by
      intro a b hab
      have h := congrArg (·⁻¹) hab
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, inv_inv, ← mul_assoc] at h
      exact h
    -- Iterating conjugation by `r0` three times is the identity (`r0³ = 1`).
    have hiterate3 : ∀ w : SL(2,F), r0 * (r0 * (r0 * w * r0⁻¹) * r0⁻¹) * r0⁻¹ = w := by
      intro w
      have hcube_eq : r0 * r0 * r0 = r0 ^ 3 := by rw [pow_succ, pow_succ, pow_one]
      have hiter : r0 * (r0 * (r0 * w * r0⁻¹) * r0⁻¹) * r0⁻¹ = r0 ^ 3 * w * (r0 ^ 3)⁻¹ := by
        rw [← hcube_eq]; group
      rw [hiter, hr0_cube]
      simp
    -- `r0` does not centralize the generator of a cardinality-`4` maximal abelian subgroup.
    have hnc_general : ∀ (C : Subgroup SL(2,F)) (hC_mem : C ∈ MaximalAbelianSubgroupsOf G)
        (w : SL(2,F)) (hw_mem : w ∈ G) (hCeq : C = Subgroup.zpowers w) (hCcard : Nat.card C = 4),
        r0 * w ≠ w * r0 := by
      intro C hC_mem w hw_mem hCeq hCcard hcomm
      set C' : Subgroup ↥G := C.subgroupOf G with hC'_def
      set wG : ↥G := ⟨w, hw_mem⟩ with hwG_def
      have hC'_card : Nat.card C' = 4 := by
        rw [hC'_def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_mem.right).toEquiv, hCcard]
      have hwG_mem_C' : wG ∈ C' := by
        rw [hC'_def, Subgroup.mem_subgroupOf]
        show w ∈ C
        rw [hCeq]; exact Subgroup.mem_zpowers w
      haveI hC'comm : IsMulCommutative C' := hC_mem.left.1
      have hcomm' : Commute r0G wG := by
        apply Subtype.ext
        show r0 * w = w * r0
        exact hcomm
      have hcomm_all : ∀ a ∈ C', Commute r0G a := by
        intro a ha
        have hCeq' : C' = Subgroup.zpowers wG := by
          apply SetLike.coe_injective
          symm
          have hle : Subgroup.zpowers wG ≤ C' := by
            rw [Subgroup.zpowers_le]; exact hwG_mem_C'
          have hcardzw : Nat.card (Subgroup.zpowers wG) = 4 := by
            have hordwG : orderOf wG = 4 := by
              have h := orderOf_injective G.subtype (Subgroup.subtype_injective G) wG
              rw [← h, hwG_def]
              show orderOf w = 4
              have hordw : orderOf w = Nat.card C := by
                rw [hCeq]; exact (Nat.card_zpowers w).symm
              rw [hordw, hCcard]
            rw [← hordwG]; exact Nat.card_zpowers wG
          exact Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.mpr hle)
            (by show Nat.card C' ≤ Nat.card (Subgroup.zpowers wG); rw [hC'_card, hcardzw])
            (Set.toFinite _)
        rw [hCeq', Subgroup.mem_zpowers_iff] at ha
        obtain ⟨n, hn⟩ := ha
        rw [← hn]
        exact hcomm'.zpow_right n
      set K : Set ↥G := (C' : Set ↥G) ∪ {r0G} with hK_def
      have hcomm_K : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
        rintro a (ha | ha) b (hb | hb)
        · exact setLike_mul_comm ha hb
        · simp only [Set.mem_singleton_iff] at hb; subst hb
          exact (hcomm_all a ha).symm
        · simp only [Set.mem_singleton_iff] at ha; subst ha
          exact hcomm_all b hb
        · simp only [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
      haveI hKcomm : IsMulCommutative (Subgroup.closure K) := Subgroup.isMulCommutative_closure hcomm_K
      have hC'_le_closure : C' ≤ Subgroup.closure K := by
        rw [← Subgroup.closure_eq C']; exact Subgroup.closure_mono Set.subset_union_left
      have hclosure_le : Subgroup.closure K ≤ C' := hC_mem.left.2 hKcomm hC'_le_closure
      have hr0G_mem_closure : r0G ∈ Subgroup.closure K := subset_closure (Set.mem_union_right _ rfl)
      have hr0G_mem_C' : r0G ∈ C' := hclosure_le hr0G_mem_closure
      have hdvd : orderOf r0G ∣ Nat.card C' := by
        have h1 := orderOf_dvd_natCard (⟨r0G, hr0G_mem_C'⟩ : C')
        have h2 : orderOf (⟨r0G, hr0G_mem_C'⟩ : C') = orderOf r0G :=
          (orderOf_injective C'.subtype (Subgroup.subtype_injective C') ⟨r0G, hr0G_mem_C'⟩).symm
        rwa [h2] at h1
      rw [hC'_card] at hdvd
      have hr0G_ord : orderOf r0G = 3 := by
        have h := orderOf_injective G.subtype (Subgroup.subtype_injective G) r0G
        rw [← h, hr0G_def]; exact hr0_ord
      rw [hr0G_ord] at hdvd
      norm_num at hdvd
    -- **Step 13**: pin down `y1`'s exact identity among `{y0SL, y0SL⁻¹, z0SL, z0SL⁻¹}`, and derive
    -- that `x0SL` inverts `y1` (hence, by `general_mutual`, `y1` inverts `x0SL`).
    have hy1_mem_zy_or_zz : y1 ∈ Subgroup.zpowers y0SL ∨ y1 ∈ Subgroup.zpowers z0SL := by
      rcases hB0_cases' with h | h
      · left; rw [hB0_eq] at h; rw [← h]; exact Subgroup.mem_zpowers y1
      · right; rw [hB0_eq] at h; rw [← h]; exact Subgroup.mem_zpowers y1
    have hxinvy1 : x0SL * y1 * x0SL⁻¹ = y1⁻¹ := by
      rcases hy1_mem_zy_or_zz with hmem | hmem
      · rcases order4_mem_zpowers y0SL y1 hy0SL_ord4 hy1_ord4 hmem with heq | heq
        · rw [heq]; exact hxinvy
        · rw [heq, inv_inv]; exact invert_inv_right x0SL y0SL hxinvy
      · rcases order4_mem_zpowers z0SL y1 hz0SL_ord4 hy1_ord4 hmem with heq | heq
        · rw [heq]; exact hxinvz
        · rw [heq, inv_inv]; exact invert_inv_right x0SL z0SL hxinvz
    have hy1_4 : y1 ^ 4 = 1 := by
      have heq : y1 ^ 4 = (y1 ^ 2) ^ 2 := by rw [← pow_mul]
      rw [heq, hy1_sq, hnegone_sq]
    have hyinvx0 : y1 * x0SL * y1⁻¹ = x0SL⁻¹ :=
      general_mutual y1 x0SL hy1_sq hx0SL_sq hy1_4 hx0SL4 hxinvy1
    -- **Step 14**: `z1 := x0SL * y1` (Butler's third candidate), with the same `Q₈`-type
    -- properties as `z0SL` had relative to `y0SL`.
    set z1 : SL(2,F) := x0SL * y1 with hz1_def
    have hyx0rearr1 : y1 * x0SL = x0SL⁻¹ * y1 := by
      have h2 : y1 * x0SL * y1⁻¹ * y1 = x0SL⁻¹ * y1 := by rw [hyinvx0]
      rwa [mul_assoc, inv_mul_cancel, mul_one] at h2
    have hz1_sq : z1 ^ 2 = -1 := by
      have step : z1 ^ 2 = x0SL * (y1 * x0SL) * y1 := by rw [hz1_def, sq]; group
      rw [step, hyx0rearr1]
      have step2 : x0SL * (x0SL⁻¹ * y1) * y1 = y1 * y1 := by group
      rw [step2, ← sq, hy1_sq]
    have hz1_ord4 : orderOf z1 = 4 := by
      have hne1 : z1 ^ 2 ≠ 1 := by
        rw [hz1_sq]
        intro h
        exact hp_ne_two (by
          have h2 : (2:F) = 0 := by
            by_contra h2ne
            haveI : NeZero (2:F) := ⟨h2ne⟩
            have := SpecialSubgroups.orderOf_neg_one_eq_two (F := F)
            rw [h] at this
            simp at this
          have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
          exact (CharP.eq F (‹CharP F p› : CharP F p) hCharP2 : p = 2))
      have h4 : z1 ^ 4 = 1 := by
        have heq : z1 ^ 4 = (z1 ^ 2) ^ 2 := by rw [← pow_mul]
        rw [heq, hz1_sq, hnegone_sq]
      have hdvd4 : orderOf z1 ∣ 4 := orderOf_dvd_of_pow_eq_one h4
      have hndvd2 : ¬ orderOf z1 ∣ 2 := by
        intro h; exact hne1 (orderOf_dvd_iff_pow_eq_one.mp h)
      have hne1' : orderOf z1 ≠ 1 := by intro h; apply hndvd2; rw [h]; norm_num
      have hne2' : orderOf z1 ≠ 2 := by intro h; apply hndvd2; rw [h]
      have hle4 : orderOf z1 ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd4
      have hpos : 0 < orderOf z1 :=
        orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by norm_num, h4⟩)
      interval_cases (orderOf z1) <;> omega
    have hxinvz1 : x0SL * z1 * x0SL⁻¹ = z1⁻¹ := by
      rw [hz1_def]
      have h1 : x0SL * (x0SL * y1) * x0SL⁻¹ = x0SL * (x0SL * y1 * x0SL⁻¹) := by group
      rw [h1, hxinvy1]
      have h2 : x0SL * -y1 = -(x0SL * y1) := mul_neg x0SL y1
      have hy1inv : y1⁻¹ = -y1 := hneg_eq y1 hy1_sq hy1_4
      rw [hy1inv, h2, ← hz1_def]
      exact (hneg_eq z1 hz1_sq (by
        have heq : z1 ^ 4 = (z1 ^ 2) ^ 2 := by rw [← pow_mul]
        rw [heq, hz1_sq, hnegone_sq])).symm
    have hyinvz1 : y1 * z1 * y1⁻¹ = z1⁻¹ := by
      rw [hz1_def]
      have h1 : y1 * (x0SL * y1) * y1⁻¹ = (y1 * x0SL) * (y1 * y1⁻¹) := by group
      rw [h1, mul_inv_cancel, mul_one, hyx0rearr1]
      have h2 : x0SL⁻¹ * y1 = -(x0SL) * y1 := by rw [hneg_eq x0SL hx0SL_sq hx0SL4]
      rw [h2]
      have h3 : -x0SL * y1 = -(x0SL * y1) := neg_mul x0SL y1
      rw [h3, ← hz1_def]
      exact (hneg_eq z1 hz1_sq (by
        have heq : z1 ^ 4 = (z1 ^ 2) ^ 2 := by rw [← pow_mul]
        rw [heq, hz1_sq, hnegone_sq])).symm
    -- **Step 15**: `z1` is `∉ A2` and `∉ zpowers y1` (so `A2, zpowers y1, zpowers z1` are pairwise
    -- distinct), and (via `key`) `zpowers z1` is a `G`-conjugate of `A2`.
    have hz1_notin_A2 : z1 ∉ A2 := by
      rw [hA2_eq_zpowers_x0SL]; exact general_ninv x0SL z1 hxinvz1 hz1_ord4
    have hz1_notin_zy1 : z1 ∉ Subgroup.zpowers y1 := general_ninv y1 z1 hyinvz1 hz1_ord4
    have hzy1_ne_zz1 : Subgroup.zpowers y1 ≠ Subgroup.zpowers z1 := by
      intro h; exact hz1_notin_zy1 (h ▸ Subgroup.mem_zpowers z1)
    have hA2_ne_zz1 : A2 ≠ Subgroup.zpowers z1 := by
      intro h; exact hz1_notin_A2 (h ▸ Subgroup.mem_zpowers z1)
    have hy1_mem_G : y1 ∈ G := by
      rw [hy1_def]; exact Subgroup.mul_mem G (Subgroup.mul_mem G hr0_mem_G x0.2) (G.inv_mem hr0_mem_G)
    have hz1_mem_G : z1 ∈ G := by rw [hz1_def]; exact Subgroup.mul_mem G x0.2 hy1_mem_G
    obtain ⟨cz1, hcz1G, hcz1⟩ := key z1 hz1_mem_G hz1_ord4
    have hzz1_mem_CC : Subgroup.zpowers z1 ∈
        ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      rw [smul_eq_iff_eq_inv_smul, ← map_inv] at hcz1
      exact ⟨cz1⁻¹, G.inv_mem hcz1G, hcz1.symm⟩
    -- **Step 16**: `φ(y1) := r0 * y1 * r0⁻¹` has order `4`, is `≠ A2`-generator, `≠ y1`-generator
    -- (via the `r0³ = 1` / non-centralizing arguments), hence -- since `ConjClassOf` has only the
    -- `3` elements `A2, zpowers y1 ∈ {zpowers y0SL, zpowers z0SL}, ` and both `zpowers z1` and
    -- `zpowers (φ y1)` avoid `A2` and `zpowers y1` while lying in `ConjClassOf` -- they coincide.
    set phi_y1 : SL(2,F) := r0 * y1 * r0⁻¹ with hphiy1_def
    have hphiy1_ord4 : orderOf phi_y1 = 4 := by rw [hphiy1_def, orderOf_conj]; exact hy1_ord4
    have hphiy1_mem_G : phi_y1 ∈ G := by
      rw [hphiy1_def]
      exact Subgroup.mul_mem G (Subgroup.mul_mem G hr0_mem_G hy1_mem_G) (G.inv_mem hr0_mem_G)
    have hh : r0 * phi_y1 * r0⁻¹ = x0SL := by
      have h0 := hiterate3 x0SL
      rw [← hy1_def, ← hphiy1_def] at h0
      exact h0
    have hphiy1_ne_A2 : Subgroup.zpowers phi_y1 ≠ A2 := by
      intro heqA2
      have hmemA2 : phi_y1 ∈ A2 := heqA2 ▸ Subgroup.mem_zpowers phi_y1
      rw [hA2_eq_zpowers_x0SL] at hmemA2
      rcases order4_mem_zpowers x0SL phi_y1 hx0SL_ord4 hphiy1_ord4 hmemA2 with heq | heq
      · rw [heq] at hh; rw [← hy1_def] at hh; exact hy1_ne_x0SL hh
      · rw [heq] at hh
        have hconjinv : r0 * x0SL⁻¹ * r0⁻¹ = (r0 * x0SL * r0⁻¹)⁻¹ := by group
        rw [hconjinv, ← hy1_def] at hh
        apply hy1_ne_x0SL_inv
        rw [← inv_inv y1, hh]
    have hphiy1_ne_y1 : Subgroup.zpowers phi_y1 ≠ Subgroup.zpowers y1 := by
      intro heqy1
      have hmemy1 : phi_y1 ∈ Subgroup.zpowers y1 := heqy1 ▸ Subgroup.mem_zpowers phi_y1
      rcases order4_mem_zpowers y1 phi_y1 hy1_ord4 hphiy1_ord4 hmemy1 with heq | heq
      · apply hnc_general B0 hB0_mem y1 hy1_mem_G hB0_eq hcard_B0
        rw [hphiy1_def] at heq
        have h2 : r0 * y1 * r0⁻¹ * r0 = y1 * r0 := by rw [heq]
        rwa [mul_assoc, inv_mul_cancel, mul_one] at h2
      · have h0 := hiterate3 y1
        rw [← hphiy1_def] at h0
        rw [heq] at h0
        have hconjinv : r0 * y1⁻¹ * r0⁻¹ = (r0 * y1 * r0⁻¹)⁻¹ := by group
        rw [hconjinv, ← hphiy1_def, heq, inv_inv] at h0
        -- `h0 : r0 * y1 * r0⁻¹ = y1`, i.e. (unfolding `phi_y1`) `phi_y1 = y1`; combined with
        -- `heq : phi_y1 = y1⁻¹` this gives `y1 = y1⁻¹`.
        have hphiy1eqy1 : phi_y1 = y1 := h0
        have hy1eqinv : y1 = y1⁻¹ := hphiy1eqy1.symm.trans heq
        have hy1sq1 : y1 ^ 2 = 1 := by
          rw [sq]
          have hinvcancel := inv_mul_cancel y1
          rwa [← hy1eqinv] at hinvcancel
        rw [hy1_sq] at hy1sq1
        apply hp_ne_two
        have h2 : (2:F) = 0 := by
          by_contra h2ne
          haveI : NeZero (2:F) := ⟨h2ne⟩
          have hordneg1 := SpecialSubgroups.orderOf_neg_one_eq_two (F := F)
          rw [hy1sq1, orderOf_one] at hordneg1
          norm_num at hordneg1
        have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
        exact (CharP.eq F (‹CharP F p› : CharP F p) hCharP2 : p = 2)
    -- **Step 17**: `zpowers phi_y1 = zpowers z1` (both are the unique element of
    -- `ConjClassOf G A2 \ {A2, zpowers y1}`).
    have hzy1_ne_A2 : Subgroup.zpowers y1 ≠ A2 := hB0_eq ▸ hB0_ne_A2
    obtain ⟨cphi, hcphiG, hcphi⟩ := key phi_y1 hphiy1_mem_G hphiy1_ord4
    have hphiy1_mem_CC : Subgroup.zpowers phi_y1 ∈
        ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      rw [smul_eq_iff_eq_inv_smul, ← map_inv] at hcphi
      exact ⟨cphi⁻¹, G.inv_mem hcphiG, hcphi.symm⟩
    have hsub2 : ({A2, Subgroup.zpowers y1} : Set (Subgroup SL(2,F)))
        ⊆ ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hA2_mem_CC
      · exact hB0_eq ▸ hB0_mem_CC
    have hcard2 : ({A2, Subgroup.zpowers y1} : Set (Subgroup SL(2,F))).ncard = 2 :=
      Set.ncard_pair hzy1_ne_A2.symm
    have hCCcard_eq : (ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G)).ncard
        = Nat.card (ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G)) := rfl
    have hCC_diff_card : (ConjClassOf G (⟨A2, hA2_mem⟩ : MaximalAbelianSubgroupsOf G)
        \ ({A2, Subgroup.zpowers y1} : Set (Subgroup SL(2,F)))).ncard = 1 := by
      rw [Set.ncard_diff hsub2 (Set.toFinite _), hcard2, hCCcard_eq, hCC_card]
    have hzz1_in_diff : Subgroup.zpowers z1 ∈ ConjClassOf G (⟨A2, hA2_mem⟩ :
        MaximalAbelianSubgroupsOf G) \ ({A2, Subgroup.zpowers y1} : Set (Subgroup SL(2,F))) := by
      refine ⟨hzz1_mem_CC, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨hA2_ne_zz1.symm, fun h => hzy1_ne_zz1 h.symm⟩
    have hphiy1_in_diff : Subgroup.zpowers phi_y1 ∈ ConjClassOf G (⟨A2, hA2_mem⟩ :
        MaximalAbelianSubgroupsOf G) \ ({A2, Subgroup.zpowers y1} : Set (Subgroup SL(2,F))) := by
      refine ⟨hphiy1_mem_CC, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨hphiy1_ne_A2, hphiy1_ne_y1⟩
    obtain ⟨s, hs⟩ := Set.ncard_eq_one.mp hCC_diff_card
    rw [hs, Set.mem_singleton_iff] at hzz1_in_diff hphiy1_in_diff
    have hphiy1_eq_z1 : Subgroup.zpowers phi_y1 = Subgroup.zpowers z1 :=
      hphiy1_in_diff.trans hzz1_in_diff.symm
    -- **Step 18**: `φ(y1) = z1` or `φ(y1) = z1⁻¹` (order-`4` elements of the same cyclic group);
    -- either way, transport `(x0SL, y1, r0)` (resp. `(x0SL, z1⁻¹, r0²)`) up to `↥G` and conclude via
    -- `mulEquiv_SL2_ZMod3_of`.
    have hphiy1_mem_zz1 : phi_y1 ∈ Subgroup.zpowers z1 :=
      hphiy1_eq_z1 ▸ Subgroup.mem_zpowers phi_y1
    have hy1_notin_x0 : y1 ∉ Subgroup.zpowers x0SL := by
      intro hmem
      rcases order4_mem_zpowers x0SL y1 hx0SL_ord4 hy1_ord4 hmem with heq | heq
      · exact hy1_ne_x0SL heq
      · exact hy1_ne_x0SL_inv heq
    have hxy2 : x0SL ^ 2 = y1 ^ 2 := hx0SL_sq.trans hy1_sq.symm
    rcases order4_mem_zpowers z1 phi_y1 hz1_ord4 hphiy1_ord4 hphiy1_mem_zz1 with hcaseA | hcaseB
    · -- **Case A**: `φ(y1) = z1 = x0SL * y1`.
      set y1G : ↥G := ⟨y1, hy1_mem_G⟩ with hy1G_def
      have hx0y1_2 : x0 ^ 2 = y1G ^ 2 := by
        apply Subtype.ext
        show x0SL ^ 2 = y1 ^ 2
        exact hxy2
      have hconjG : y1G * x0 * y1G⁻¹ = x0⁻¹ := by
        apply Subtype.ext
        show y1 * x0SL * y1⁻¹ = x0SL⁻¹
        exact hyinvx0
      have hyxG : y1G ∉ Subgroup.zpowers x0 := by
        intro hmem
        apply hy1_notin_x0
        obtain ⟨n, hn⟩ := hmem
        refine ⟨n, ?_⟩
        have := congrArg (Subtype.val) hn
        simpa [hy1G_def] using this
      have hrxG : r0G * x0 * r0G⁻¹ = y1G := by
        apply Subtype.ext
        show r0 * x0SL * r0⁻¹ = y1
        exact hy1_def.symm
      have hryG : r0G * y1G * r0G⁻¹ = x0 * y1G := by
        apply Subtype.ext
        show r0 * y1 * r0⁻¹ = x0SL * y1
        rw [← hphiy1_def, hcaseA, hz1_def]
      exact ⟨mulEquiv_SL2_ZMod3_of x0 y1G r0G hx0_ord4 hx0y1_2 hconjG hyxG hr0G_cube hrxG hryG
        hcardG24⟩
    · -- **Case B**: `φ(y1) = z1⁻¹`. Use `r0² := r0 * r0` and `y := z1⁻¹` instead.
      have hz1_4 : z1 ^ 4 = 1 := by
        have heq : z1 ^ 4 = (z1 ^ 2) ^ 2 := by rw [← pow_mul]
        rw [heq, hz1_sq, hnegone_sq]
      have hz1invx0 : z1 * x0SL * z1⁻¹ = x0SL⁻¹ :=
        general_mutual z1 x0SL hz1_sq hx0SL_sq hz1_4 hx0SL4 hxinvz1
      have hxy2z : x0SL ^ 2 = z1⁻¹ ^ 2 := by
        rw [hx0SL_sq]
        have : z1⁻¹ ^ 2 = (z1 ^ 2)⁻¹ := by
          rw [sq, sq]; group
        rw [this, hz1_sq]
        have hnegone_mul : (-1 : SL(2,F)) * -1 = 1 := by rw [← sq]; exact hnegone_sq
        have hnegone_inv : (-1 : SL(2,F))⁻¹ = -1 := inv_eq_of_mul_eq_one_right hnegone_mul
        exact hnegone_inv.symm
      have hconjz : z1⁻¹ * x0SL * (z1⁻¹)⁻¹ = x0SL⁻¹ := by
        rw [inv_inv]; exact invert_inv_left z1 x0SL hz1invx0
      have hyxz : z1⁻¹ ∉ Subgroup.zpowers x0SL := by
        intro hmem
        apply hz1_notin_A2
        rw [hA2_eq_zpowers_x0SL]
        have hinv := Subgroup.inv_mem (Subgroup.zpowers x0SL) hmem
        rwa [inv_inv] at hinv
      set r0sq : SL(2,F) := r0 * r0 with hr0sq_def
      have hr0sq_cube : r0sq ^ 3 = 1 := by
        have h6 : r0 ^ 6 = 1 := by
          have e1 : r0 ^ 6 = r0 ^ 3 * r0 ^ 3 := by
            simp only [pow_succ, pow_zero, one_mul]; group
          rw [e1, hr0_cube, mul_one]
        have heq : r0sq ^ 3 = r0 ^ 6 := by
          rw [hr0sq_def]
          simp only [pow_succ, pow_zero, one_mul]; group
        rw [heq, h6]
      have hconj_mul : ∀ a b : SL(2,F), r0 * (a * b) * r0⁻¹ = (r0 * a * r0⁻¹) * (r0 * b * r0⁻¹) := by
        intro a b; group
      have hconj_inv : ∀ a : SL(2,F), r0 * a⁻¹ * r0⁻¹ = (r0 * a * r0⁻¹)⁻¹ := by
        intro a; group
      have hr0sq_conj : ∀ w : SL(2,F), r0sq * w * r0sq⁻¹ = r0 * (r0 * w * r0⁻¹) * r0⁻¹ := by
        intro w; rw [hr0sq_def]; group
      have hrx_sq : r0sq * x0SL * r0sq⁻¹ = z1⁻¹ := by
        rw [hr0sq_conj, ← hy1_def, ← hphiy1_def, hcaseB]
      have hcomp1 : r0 * y1⁻¹ * r0⁻¹ = z1 := by
        rw [hconj_inv, ← hphiy1_def, hcaseB, inv_inv]
      have hcomp2 : r0 * x0SL⁻¹ * r0⁻¹ = y1⁻¹ := by
        rw [hconj_inv, ← hy1_def]
      have hcomp3 : r0 * z1⁻¹ * r0⁻¹ = z1 * y1⁻¹ := by
        have hz1inv_eq : z1⁻¹ = y1⁻¹ * x0SL⁻¹ := by rw [hz1_def]; group
        rw [hz1inv_eq, hconj_mul, hcomp1, hcomp2]
      have hcomp4 : r0 * z1 * r0⁻¹ = y1 * z1⁻¹ := by
        have hz1_eq : z1 = x0SL * y1 := hz1_def
        rw [hz1_eq, hconj_mul, hy1_def, ← hphiy1_def, hcaseB]
      have hxz1inv_eq_y1 : x0SL * z1⁻¹ = y1 := by
        have hz1inv_eq : z1⁻¹ = y1⁻¹ * x0SL⁻¹ := by rw [hz1_def]; group
        rw [hz1inv_eq, ← mul_assoc]
        exact invert_inv_right x0SL y1 hxinvy1
      have hry_sq : r0sq * z1⁻¹ * r0sq⁻¹ = x0SL * z1⁻¹ := by
        rw [hr0sq_conj, hcomp3, hxz1inv_eq_y1]
        have hstep := hconj_mul z1 y1⁻¹
        rw [hcomp4, hcomp1] at hstep
        rw [hstep, mul_assoc, inv_mul_cancel, mul_one]
      set z1G : ↥G := ⟨z1, hz1_mem_G⟩ with hz1G_def
      have hr0sqG_mem_G : r0sq ∈ G := by rw [hr0sq_def]; exact Subgroup.mul_mem G hr0_mem_G hr0_mem_G
      set r0sqG : ↥G := ⟨r0sq, hr0sqG_mem_G⟩ with hr0sqG_def
      have hr0sqG_cube : r0sqG ^ 3 = 1 := Subtype.ext (by rw [hr0sqG_def]; exact hr0sq_cube)
      have hx0z1inv_2 : x0 ^ 2 = z1G⁻¹ ^ 2 := by
        apply Subtype.ext
        show x0SL ^ 2 = (z1⁻¹) ^ 2
        exact hxy2z
      have hconjG : z1G⁻¹ * x0 * (z1G⁻¹)⁻¹ = x0⁻¹ := by
        apply Subtype.ext
        show z1⁻¹ * x0SL * (z1⁻¹)⁻¹ = x0SL⁻¹
        exact hconjz
      have hyxG : z1G⁻¹ ∉ Subgroup.zpowers x0 := by
        intro hmem
        apply hyxz
        obtain ⟨n, hn⟩ := hmem
        refine ⟨n, ?_⟩
        have := congrArg (Subtype.val) hn
        simpa [hz1G_def] using this
      have hrxG : r0sqG * x0 * r0sqG⁻¹ = z1G⁻¹ := by
        apply Subtype.ext
        show r0sq * x0SL * r0sq⁻¹ = z1⁻¹
        exact hrx_sq
      have hryG : r0sqG * z1G⁻¹ * r0sqG⁻¹ = x0 * z1G⁻¹ := by
        apply Subtype.ext
        show r0sq * z1⁻¹ * r0sq⁻¹ = x0SL * z1⁻¹
        exact hry_sq
      exact ⟨mulEquiv_SL2_ZMod3_of x0 z1G⁻¹ r0sqG hx0_ord4 hx0z1inv_2 hconjG hyxG hr0sqG_cube hrxG
        hryG hcardG24⟩

/-- Butler Case III (tex 1661-1670): `s = t = 0`, i.e. there are no cyclic maximal abelian
subgroups of order coprime to `p` at all. Forces `K ≤ Z` (`k = 1`, Theorem 6.8(v)) and hence
`g = q`, giving `G = QZ` as an internal direct product (Butler writes `G = Q × Z`).
Status: statement faithful to paper, **except** that the second conjunct originally read
`IsComplement' (Subgroup.map G.subtype Q.toSubgroup) (center SL(2,F))`: since `IsComplement'` for
two subgroups of an ambient group `L` asserts their product is *all of `L`*
(`IsComplement'.sup_eq_top`), this literally demanded `Subgroup.map G.subtype Q.toSubgroup ⊔
center SL(2,F) = ⊤` (i.e. `= SL(2,F)`), contradicting the first conjunct (`= G`) whenever
`G ≠ ⊤`. Restated as the internal-picture statement `IsComplement' Q.toSubgroup ((center
SL(2,F)).subgroupOf G)` (complementary subgroups of `↥G`, matching Butler's "internal direct
product `G = Q × Z`" and consistent with the first conjunct). PROVED. -/
lemma case_III {F : Type*} {p : ℕ} [Field F] [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q)
    (heq : ∃ k, 1 ≤ k ∧ k ≤ 1 ∧
      ClassEquation g q k (s := 0) (t := 0) (fun i => i.elim0) (fun i => i.elim0)) :
    Subgroup.map G.subtype Q.toSubgroup ⊔ center SL(2,F) = G ∧
      IsComplement' Q.toSubgroup ((center SL(2,F)).subgroupOf G) := by
  obtain ⟨k, hk_ge, hk_le, heq'⟩ := heq
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hgpos : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with hg0 | hgpos
    · rw [hg0, mul_zero] at hg; omega
    · exact hgpos
  have hqpos : 1 ≤ q := by
    have := Nat.card_pos (α := Q.toSubgroup); omega
  obtain ⟨-, hgq⟩ := CaseArithmetic.case_0_0 g q k hgpos hqpos hk_ge hk_le heq'
  -- `Z' := (center SL(2,F)).subgroupOf G`, central in `↥G`, hence normal.
  have hZ_le_G : center SL(2,F) ≤ G := center_le_G
  have hZ'_central : (center SL(2,F)).subgroupOf G ≤ center ↥G := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [mem_center_iff]
    intro g'
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact mem_center_iff.mp hz (g' : SL(2,F))
  haveI hZ'_normal : ((center SL(2,F)).subgroupOf G).Normal :=
    instNormalLeCenter _ hZ'_central
  have hZ'_card : Nat.card ((center SL(2,F)).subgroupOf G) = Nat.card (center SL(2,F)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ_le_G).toEquiv
  -- `Q.toSubgroup` (a `p`-group) and `Z'` (coprime order) are disjoint.
  have hcopZp : Nat.Coprime (Nat.card (center SL(2,F))) p := by
    rw [SpecialSubgroups.center_SL2_eq_Z]; exact NumericClassEquation.coprime_card_Z_prime
  have hcop_Z'p : Nat.Coprime (Nat.card ((center SL(2,F)).subgroupOf G)) p := by
    rw [hZ'_card]; exact hcopZp
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hcop : Nat.Coprime (Nat.card Q.toSubgroup)
      (Nat.card ((center SL(2,F)).subgroupOf G)) := by
    rw [hn]; exact (Nat.Coprime.pow_right n hcop_Z'p).symm
  have hdisj : Disjoint Q.toSubgroup ((center SL(2,F)).subgroupOf G) :=
    Subgroup.disjoint_of_coprime_natCard hcop
  -- `|Q| ⋅ |Z'| = |G|`, so `Q.toSubgroup` and `Z'` are complementary in `↥G`.
  have hcard_eq : Nat.card Q.toSubgroup * Nat.card ((center SL(2,F)).subgroupOf G)
      = Nat.card G := by
    rw [hq, hZ'_card, hg, hgq, mul_comm]
  have hcomplement : IsComplement' Q.toSubgroup ((center SL(2,F)).subgroupOf G) :=
    isComplement'_of_card_mul_and_disjoint hcard_eq hdisj
  refine ⟨?_, hcomplement⟩
  -- Push `Q.toSubgroup ⊔ Z' = ⊤` forward along `G.subtype` to get the first conjunct.
  have hsup_top : Q.toSubgroup ⊔ (center SL(2,F)).subgroupOf G = ⊤ := hcomplement.sup_eq_top
  have hmap := congrArg (Subgroup.map G.subtype) hsup_top
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hZ_le_G] at hmap
  have hGtop : Subgroup.map G.subtype (⊤ : Subgroup ↥G) = G := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rwa [hGtop] at hmap

open NumericClassEquation in
/-- Butler Case IV (tex 1681-1745): `s = 0, t = 1`. Forces `k = 1` and `q ∈ {2,3}`. Case IVa
(`q = 2`, so `p = 2`) constructs `G ≅ D_n` (dihedral of order `2n`, `n` odd -- note `Z` is
trivial in characteristic `2`, so this is genuinely a dihedral, not dicyclic, group here); Case
IVb (`q = 3`, so `p = 3`) constructs an isomorphism with `SL(2,3)` by an argument "analogous to
Case IIb" (tex ~1785).

RESTATED (justification: as with `case_I`, the previous `heq : ∃ k g1, ...` hid Butler's cyclic
maximal abelian subgroup `A₁` -- here the *unique* `t = 1` class of normalizer-index `2` -- behind
a bare numeral `g1` with no witness subgroup. Restated to carry the witness `A` directly (with the
membership/cyclicity/coprimality/cardinality/normalizer-index-`2` facts Theorem 6.8 attaches to
such a class), `[IsAlgClosed F] [DecidableEq F]` added (needed by every `S2_A`/`S2_B` lemma that
would attach further facts to `A`, matching `case_I`/`dicksons_classification_theorem_class_I`'s
own hypotheses).

With this witness, `CaseArithmetic.case_0_1` gives `k = 1` and `q = 2 ∧ g = 2 * g1` or
`q = 3 ∧ g1 = 2 ∧ g = 12`; `q` is exactly `Nat.card Q.toSubgroup` for the Sylow `p`-subgroup `Q`
(`Q.isPGroup'`/`IsPGroup.iff_card`), so `q = 2` (resp. `3`) forces `p = 2` (resp. `p = 3`)
directly (`Nat.prime_dvd_prime_iff_eq`, since `p ∣ p ^ m = q` for the `m` witnessing `Q`'s
order). In the `p = 2` branch, `Nat.card (center SL(2,F)) = 1` (`CharTwo.two_eq_zero` +
`card_Z_eq_one_of_two_eq_zero`), so `Nat.card A = g1` exactly, and `g1` is odd (coprime to `p = 2`
by `hA_cop`) -- this proves the numeral half of Case IVa (`p = 2`, witness `n := g1` odd) directly.

**Case IVa now PROVED in full** (`DIVERGENCES.md` item 1, unblocked): the final group-recognition
step (`G ≅ DihedralGroup g1`) needs an inverting `y ∈ N_G(A) \ A`, Theorem 6.8(iv) at `p = 2`; this
is now available as `S2_B_MaximalAbelianSubgroup.of_index_normalizer_eq_two_char_two` (`[CharP F 2]`
in place of the odd-characteristic `p_ne_two`). Butler's argument that `y` is an involution
(tex 1706-1718) is run exactly as in `case_II`'s Case IIa (`y` inverts all of the cyclic group `A`,
so `y²` centralizes `A`, hence `y² ∈ A` by maximality, and `y` inverting `y² ∈ A` while fixing it
under conjugation by itself forces `(y²)² = 1`) but concludes more simply: since `A` has *odd*
order `g1` here (no even-order "unique involution" subtlety as in `case_II`), Lagrange alone forces
`y² = 1` directly. Case IVb (`q = 3`, `p = 3`) is **partially proved**, in lockstep with
`case_II`'s `g1 = 3` branch (tex ~1785 itself just says "analogous to Case IIb ... I will leave
it to the reader to verify"): the numerals (`p = 3`, `e = 2`) and the `Q₈`-shaped generator pair
`x0, y0` on `A` are proved directly (reusing the `exists_Q8_generators_of_relIndex_two` extraction
above `case_II`); what remains sorried is the same order-`3`-element/normality gap documented in
`case_II`'s docstring.
-/
lemma case_IV {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F] [Fact (Nat.Prime p)]
    [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q) (g1 k : ℕ)
    -- witness for the unique `t = 1` coprime-type class `A₁` (Theorem 6.8), replacing the bare
    -- numeral `g1` that the original `heq : ∃ k g1, ...` hid it behind.
    (A : Subgroup SL(2,F)) (hA_mem : A ∈ MaximalAbelianSubgroupsOf G)
    (hA_cyc : IsCyclic A) (hA_cop : Nat.Coprime (Nat.card A) p)
    (hA_card : Nat.card A = Nat.card (center SL(2,F)) * g1)
    (hA_relIndex : relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) = 2)
    -- **Completeness** (Theorem 6.8's numeric class equation): every maximal abelian subgroup of
    -- `G` is `G`-conjugate to `A`, or is of Sylow type. (There is no `A₁`-family here, `s = 0`.)
    -- Needed to close Case IVb below (`case_II`'s analogous `hComplete`, without its `A₁` case).
    (hComplete : ∀ B ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B = A) ∨
      IsSylowType p G B)
    (heq : 1 ≤ k ∧ 2 ≤ g1 ∧ 2 * g1 ≤ g ∧
      ClassEquation g q k (s := 0) (t := 1) (fun i => i.elim0) (fun _ => g1)) :
    (p = 2 ∧ ∃ n, Odd n ∧ Isomorphic G (DihedralGroup n)) ∨
      (p = 3 ∧ Isomorphic G SL(2, ZMod 3)) := by
  obtain ⟨hk_ge, hg1_ge, hg_ge, heq'⟩ := heq
  have hgpos : 1 ≤ g := by omega
  have hqpos : 1 ≤ q := by have := Nat.card_pos (α := Q.toSubgroup); omega
  obtain ⟨-, hcase⟩ := case_0_1 g q k g1 hgpos hqpos hk_ge hg1_ge hg_ge heq'
  rcases hcase with ⟨hq2, hgeq⟩ | ⟨hq3, hg1eq2, hgeq12⟩
  · -- **Case IVa** (`q = 2`): a Sylow `p`-subgroup has order `2`, forcing `p = 2` and `e = 1`.
    left
    have hp2 : p = 2 := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp Q.isPGroup'
      rw [hq, hq2] at hm
      have hm0 : m ≠ 0 := by rintro rfl; simp at hm
      have hpdvd : p ∣ 2 := by rw [hm]; exact dvd_pow_self p hm0
      exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hpdvd
    subst hp2
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have he1 : Nat.card (center SL(2,F)) = 1 := by
      rw [SpecialSubgroups.center_SL2_eq_Z]
      exact SpecialSubgroups.card_Z_eq_one_of_two_eq_zero h2
    have hA_card' : Nat.card A = g1 := by rw [hA_card, he1, one_mul]
    have hodd : Odd g1 := by
      have hcop' : Nat.Coprime g1 2 := hA_card' ▸ hA_cop
      rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero, ← Nat.prime_two.coprime_iff_not_dvd]
      exact hcop'.symm
    refine ⟨rfl, g1, hodd, ?_⟩
    -- **Char-2 wiring** (`DIVERGENCES.md` item 1, now unblocked): Theorem 6.8(iv)'s "index-2
    -- normalizer gives an inverting element" is now available at `p = 2` too, via
    -- `S2_B_MaximalAbelianSubgroup.of_index_normalizer_eq_two_char_two` (`[CharP F 2]` in place
    -- of `p_ne_two`, which we have here since `p` has just been `subst`ed to `2`). Butler's own
    -- argument that this inverting element is an involution (tex 1706-1718) is in fact *simpler*
    -- in characteristic `2` than the analogous step in `case_II`'s odd-characteristic Case IIa:
    -- no appeal to `SL(2,F)`'s unique involution is needed. As there, `y` (obtained below)
    -- inverts every element of the cyclic group `A` (not just the generator `g0`), so `y²`
    -- centralizes `A`, hence `y² ∈ A` by `A`'s maximality; `y` (as an element of `A`) then also
    -- inverts `y²`, while conjugating a power of `y` by `y` fixes it, forcing `(y²)² = 1`. Since
    -- `A` has *odd* order `g1` (just shown), Lagrange applied to `y² ∈ A` forces `y² = 1`
    -- directly (`orderOf (y² : A)` divides both `2` and the odd `Nat.card A = g1`, hence `= 1`).
    haveI hA_fin : Finite A :=
      (Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hA_mem.right).to_subtype
    obtain ⟨g0, hg0_gen⟩ := hA_cyc.exists_generator
    have horder_g0 : orderOf g0 = Nat.card A := orderOf_eq_card_of_forall_mem_zpowers hg0_gen
    have horder_g0SL : orderOf (g0 : SL(2,F)) = g1 := by rw [orderOf_coe, horder_g0, hA_card']
    obtain ⟨y, hy_mem, hy_conj⟩ :=
      of_index_normalizer_eq_two_char_two A G hA_mem center_le_G hA_cop hA_relIndex g0
    simp only [Set.mem_sdiff, SetLike.mem_coe, Subgroup.mem_carrier, Subgroup.mem_inf] at hy_mem
    obtain ⟨⟨hy_mem_norm, hy_mem_G⟩, hy_notin_A⟩ := hy_mem
    -- `y` inverts every element of `A` (it inverts the generator `g0`).
    have hinvert : ∀ a : SL(2,F), a ∈ A → y * a * y⁻¹ = a⁻¹ := by
      intro a ha
      obtain ⟨n, hn⟩ := hg0_gen ⟨a, ha⟩
      have hn' : (g0 : SL(2,F)) ^ n = a := by
        have := congrArg (Subtype.val) hn
        simpa using this
      have hconj_pow : y * (g0 : SL(2,F)) ^ n * y⁻¹ = ((g0 : SL(2,F)) ^ n)⁻¹ := by
        have h1 := map_zpow (MulAut.conj y).toMonoidHom (g0 : SL(2,F)) n
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
        rw [h1, hy_conj, Subgroup.coe_inv, _root_.inv_zpow]
      rwa [hn'] at hconj_pow
    -- `y²` commutes with every element of `A`.
    have hy2_comm : ∀ a : SL(2,F), a ∈ A → y ^ 2 * a = a * y ^ 2 := by
      intro a ha
      have h1 : y * a = a⁻¹ * y := by
        have h := hinvert a ha
        have h2 : y * a * y⁻¹ * y = a⁻¹ * y := by rw [h]
        simpa [mul_assoc] using h2
      have h2 : y * a⁻¹ = a * y := by
        have h := hinvert a⁻¹ (Subgroup.inv_mem A ha)
        rw [inv_inv] at h
        have h3 : y * a⁻¹ * y⁻¹ * y = a * y := by rw [h]
        simpa [mul_assoc] using h3
      calc y ^ 2 * a = y * y * a := by rw [pow_two]
        _ = y * (y * a) := by rw [mul_assoc]
        _ = y * (a⁻¹ * y) := by rw [h1]
        _ = y * a⁻¹ * y := by rw [mul_assoc]
        _ = (a * y) * y := by rw [h2]
        _ = a * (y * y) := by rw [mul_assoc]
        _ = a * y ^ 2 := by rw [pow_two]
    -- Maximality of `A` (as an internal subgroup of `↥G`) forces `y² ∈ A`.
    have hy2_mem_G : y ^ 2 ∈ G := Subgroup.pow_mem G hy_mem_G 2
    set A' : Subgroup ↥G := A.subgroupOf G with hA'_def
    set y2' : ↥G := ⟨y ^ 2, hy2_mem_G⟩ with hy2'_def
    have hy2_mem_A : y ^ 2 ∈ A := by
      set kset : Set ↥G := (A' : Set ↥G) ∪ {y2'} with hkset_def
      have hcomm_k : ∀ a ∈ kset, ∀ b ∈ kset, a * b = b * a := by
        haveI := hA_mem.left.1
        rintro a (ha | ha) b (hb | hb)
        · exact setLike_mul_comm ha hb
        · simp only [Set.mem_singleton_iff] at hb; subst hb
          apply Subtype.ext
          have ha' : (a : SL(2,F)) ∈ A := by
            rw [SetLike.mem_coe, hA'_def, Subgroup.mem_subgroupOf] at ha; exact ha
          simpa [hy2'_def] using (hy2_comm a ha').symm
        · simp only [Set.mem_singleton_iff] at ha; subst ha
          apply Subtype.ext
          have hb' : (b : SL(2,F)) ∈ A := by
            rw [SetLike.mem_coe, hA'_def, Subgroup.mem_subgroupOf] at hb; exact hb
          simpa [hy2'_def] using hy2_comm b hb'
        · simp only [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
      haveI hclosure_comm : IsMulCommutative (closure kset) :=
        Subgroup.isMulCommutative_closure hcomm_k
      have hA'_le_closure : A' ≤ closure kset := by
        rw [← Subgroup.closure_eq A']
        exact Subgroup.closure_mono (Set.subset_union_left)
      have hclosure_le : closure kset ≤ A' := hA_mem.left.2 hclosure_comm hA'_le_closure
      have hy2'_mem_closure : y2' ∈ closure kset := subset_closure (Set.mem_union_right _ rfl)
      have hy2'_mem_A' : y2' ∈ A' := hclosure_le hy2'_mem_closure
      rwa [hA'_def, Subgroup.mem_subgroupOf] at hy2'_mem_A'
    -- `(y²)² = 1`: `y` both fixes `y²` (conjugation by a power of itself) and inverts it
    -- (as an element of `A`).
    have h1 : y * y ^ 2 * y⁻¹ = (y ^ 2)⁻¹ := hinvert (y ^ 2) hy2_mem_A
    have h2 : y * y ^ 2 * y⁻¹ = y ^ 2 := by group
    have hz0_inv : (y ^ 2)⁻¹ = y ^ 2 := h1.symm.trans h2
    have hz0sq : y ^ 2 * y ^ 2 = 1 := by
      calc y ^ 2 * y ^ 2 = y ^ 2 * (y ^ 2)⁻¹ := by rw [hz0_inv]
        _ = 1 := mul_inv_cancel _
    have hz0sq' : (y ^ 2) ^ 2 = 1 := by
      have hexp : (y ^ 2) ^ 2 = y ^ 2 * y ^ 2 := by group
      rw [hexp]; exact hz0sq
    -- `A` has *odd* order `g1`; Lagrange forces the order-dividing-`2` element `y² ∈ A` to be `1`.
    have hy2_eq_one : y ^ 2 = 1 := by
      have hordA : orderOf (⟨y ^ 2, hy2_mem_A⟩ : A) ∣ Nat.card A := orderOf_dvd_natCard _
      have hord2 : orderOf (⟨y ^ 2, hy2_mem_A⟩ : A) ∣ 2 := by
        rw [← orderOf_coe]
        exact orderOf_dvd_of_pow_eq_one hz0sq'
      have hcop2 : Nat.Coprime (Nat.card A) 2 := hA_card' ▸ hA_cop
      have hordone : orderOf (⟨y ^ 2, hy2_mem_A⟩ : A) = 1 := by
        rcases Nat.prime_two.eq_one_or_self_of_dvd _ hord2 with h | h
        · exact h
        · exfalso
          rw [h] at hordA
          exact (Nat.prime_two.coprime_iff_not_dvd.mp hcop2.symm) hordA
      have := orderOf_eq_one_iff.mp hordone
      have hval := congrArg (Subtype.val) this
      simpa using hval
    -- Assemble `mulEquiv_dihedralGroup_of`'s hypotheses and conclude.
    set x0 : ↥G := ⟨(g0 : SL(2,F)), hA_mem.right g0.2⟩ with hx0_def
    set y0 : ↥G := ⟨y, hy_mem_G⟩ with hy0_def
    have hx0_ord : orderOf x0 = g1 := by
      have h := orderOf_injective G.subtype (Subgroup.subtype_injective G) x0
      rw [← h]; exact horder_g0SL
    have hy0_2 : y0 ^ 2 = 1 := Subtype.ext hy2_eq_one
    have hy0_ne_one : y0 ≠ 1 := by
      intro h
      apply hy_notin_A
      have hyval : y = 1 := congrArg Subtype.val h
      rw [hyval]; exact Subgroup.one_mem A
    have hconj0 : y0 * x0 * y0⁻¹ = x0⁻¹ := Subtype.ext hy_conj
    have hyx0 : y0 ∉ Subgroup.zpowers x0 := by
      intro hmem
      obtain ⟨kk, hk⟩ := hmem
      apply hy_notin_A
      have hk' : (g0 : SL(2,F)) ^ kk = y := by
        have := congrArg (Subtype.val) hk
        simpa using this
      rw [← hk']
      exact Subgroup.zpow_mem A g0.2 kk
    have hcardG : Nat.card G = 2 * g1 := by rw [hg, he1, one_mul, hgeq]
    haveI : NeZero g1 := ⟨by omega⟩
    exact ⟨mulEquiv_dihedralGroup_of x0 y0 hx0_ord hy0_2 hy0_ne_one hconj0 hyx0 hcardG⟩
  · -- **Case IVb** (`q = 3`): forces `p = 3`; "numerically identical to Case IIb" (tex ~1785).
    -- Partially proved, in lockstep with `case_II`'s `g1 = 3` branch -- see its docstring for
    -- exactly what remains (the same "`N_G(A)` normal in `G`" gap, tex ~1833 waves this off as
    -- "an argument analogous to ... Case IIb ... I will leave it to the reader to verify").
    right
    have hp3 : p = 3 := by
      obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp Q.isPGroup'
      rw [hq, hq3] at hm
      have hm0 : m ≠ 0 := by rintro rfl; simp at hm
      have hpdvd : p ∣ 3 := by rw [hm]; exact dvd_pow_self p hm0
      exact (Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hpdvd
    refine ⟨hp3, ?_⟩
    classical
    subst hp3
    -- `p = 3 ≠ 2` pins `e := Nat.card (center SL(2,F)) = 2` directly (simpler than `case_II`'s
    -- route there, which had to rule out `p = 2` via `q = 1`; here `p = 3` is already known).
    haveI hF2 : NeZero (2 : F) := NeZero_two_of_char_ne_two F (by norm_num)
    have he2 : Nat.card (center SL(2,F)) = 2 := by
      rw [SpecialSubgroups.center_SL2_eq_Z]
      exact SpecialSubgroups.card_Z_eq_two_of_two_ne_zero
    have hp_ne_two : (3 : ℕ) ≠ 2 := by norm_num
    have hA_card' : Nat.card A = 2 * g1 := by rw [hA_card, he2]
    -- `A`'s `Q₈`-shaped generator pair (Butler tex ~1579-1581 reused, via the shared extraction
    -- factored out above `case_II`).
    obtain ⟨x0, y0, hx0_ord, hy0_2, hconj0, hyx0, hx0_mem_A⟩ :=
      exists_Q8_generators_of_relIndex_two G A center_le_G hA_mem hA_cyc hA_cop g1 hg1_ge
        hA_card' hA_relIndex hp_ne_two
    have hx0_ord4 : orderOf x0 = 4 := by rw [hx0_ord, hg1eq2]
    have hy0_2' : y0 ^ 2 = x0 ^ 2 := by rw [hy0_2, hg1eq2]
    have hcardG24 : Nat.card (↥G) = 24 := by rw [hg, he2, hgeq12]
    -- TODO: same residual gap as `case_II`'s `g1 = 3` branch -- **now fully closed there** (see
    -- its proof for the complete argument, using the `hComplete` hypothesis above). The identical
    -- technique applies here, and should in fact be *simpler*: there is no `A₁`-family to
    -- exclude (`s = 0` in this `(s,t) = (0,1)` branch, so `hComplete`'s dispatch is only
    -- `2`-way), and the order-`3` element `r0` can be drawn directly from the Sylow `3`-subgroup
    -- `Q` (`Nat.card Q.toSubgroup = q = 3`, hence cyclic of prime order, via
    -- `IsCyclic_of_prime_card`/a direct generator argument) rather than from a second
    -- maximal-abelian class `A₁`, which does not exist in this branch. This transplant has not
    -- been carried out in this file (only `case_II`'s `s = 1, t = 1` branch was, given the
    -- session's scope); see `DIVERGENCES.md` item 8 for the precise residual statement and
    -- `case_II`'s proof for the template to follow (`N := N_G(A)` shown normal via the
    -- `hComplete`-driven "only-`A`-class" element count; `r0 x0 r0⁻¹` pinned down to one of the
    -- `2` remaining conjugates of `A` inside `N` via the same "third conjugate" counting
    -- argument; finite case split on `r0` vs `r0²`).
    sorry


-- We first need to define the homomorphism of
-- SL(2, GaloisField p k) into SL(2, GaloisField p (2*k))

open Polynomial

/- Embed GF(p^k) into GF(p^m) where k ∣ m -/
variable {p : ℕ} [hp : Fact (Nat.Prime p)] {n m : ℕ+}


noncomputable
abbrev GaloisField.polynomial (p : ℕ) [hp : Fact (Nat.Prime p)] (n : ℕ+) :
  (ZMod p)[X] := X ^ p ^ n.val - X


lemma GaloisField.polynomial_ne_zero : GaloisField.polynomial p n ≠ 0 := by
  rw [GaloisField.polynomial]
  exact FiniteField.X_pow_card_pow_sub_X_ne_zero (ZMod p) n.ne_zero hp.out.one_lt

lemma GaloisField.splits_of_dvd (hn : n ∣ m) :
    Splits ((GaloisField.polynomial p n).map (algebraMap (ZMod p) (GaloisField p m))) := by
  have hinj : Function.Injective (algebraMap (ZMod p) (GaloisField p m)) :=
    (algebraMap (ZMod p) (GaloisField p m)).injective
  have hsk : Splits ((GaloisField.polynomial p m).map (algebraMap (ZMod p) (GaloisField p m))) := by
    haveI : Fintype (GaloisField p m) := Fintype.ofFinite _
    have hcard : Fintype.card (GaloisField p m) = p ^ (m : ℕ) := by
      rw [Fintype.card_eq_nat_card]; exact GaloisField.card p m m.pos.ne'
    have h := IsSplittingField.splits (L := GaloisField p m)
      (X ^ Fintype.card (GaloisField p m) - X : (ZMod p)[X])
    rwa [hcard] at h
  have hdvd_m : (X ^ (p ^ m.val - 1) - 1 : (ZMod p)[X]) ∣ GaloisField.polynomial p m := by
    refine ⟨X, ?_⟩
    suffices (X : (ZMod p)[X]) ^ p ^ m.val = X ^ (p ^ m.val - 1 + 1) by
      simpa [GaloisField.polynomial, sub_mul, ← pow_succ]
    rw [tsub_add_cancel_of_le]
    exact Nat.pow_pos (Nat.Prime.pos Fact.out)
  have hsk' : Splits ((X ^ (p ^ m.val - 1) - 1 : (ZMod p)[X]).map
      (algebraMap (ZMod p) (GaloisField p m))) :=
    Splits.of_dvd hsk ((Polynomial.map_ne_zero_iff hinj).mpr polynomial_ne_zero)
      (Polynomial.map_dvd _ hdvd_m)
  obtain ⟨k, rfl⟩ := hn
  have hd : (p ^ n.val - 1) ∣ (p ^ (n.val * k) - 1) := by
    refine Nat.pow_sub_one_dvd_pow_sub_one p ?_
    exact dvd_mul_right _ _
  have hdx : (X : (ZMod p)[X]) ^ (p ^ n.val - 1) - 1 ∣ X ^ (p ^ (n.val * k) - 1) - 1 := by
    obtain ⟨j, hj⟩ := hd
    simp_rw [hj, pow_mul]
    exact sub_one_dvd_pow_sub_one _ j
  have hbig_ne : (X ^ (p ^ (n.val * k) - 1) - 1 : (ZMod p)[X]) ≠ 0 := by
    refine Monic.ne_zero_of_ne (zero_ne_one' (ZMod p)) ?_
    refine monic_X_pow_sub ?_
    simp [hp.out.one_lt]
  have hs' : Splits ((X ^ (p ^ n.val - 1) - 1 : (ZMod p)[X]).map
      (algebraMap (ZMod p) (GaloisField p (n * k)))) :=
    Splits.of_dvd hsk' ((Polynomial.map_ne_zero_iff hinj).mpr hbig_ne) (Polynomial.map_dvd _ hdx)
  have hexp : p ^ n.val - 1 + 1 = p ^ n.val :=
    tsub_add_cancel_of_le (Nat.pow_pos (Nat.Prime.pos Fact.out))
  have hfact : GaloisField.polynomial p n = X * (X ^ (p ^ n.val - 1) - 1) := by
    rw [GaloisField.polynomial, mul_sub, mul_one, ← pow_succ', hexp]
  rw [hfact, Polynomial.map_mul, Polynomial.map_X]
  exact Splits.mul Splits.X hs'



noncomputable
def GaloisField.algHom_of_dvd (hn : n ∣ m) : GaloisField p n →ₐ[ZMod p] GaloisField p m :=
  Polynomial.SplittingField.lift _ (splits_of_dvd hn)


-- (x) The group hSL(2, Fq ), dπ i, where SL(2, Fq ) C hSL(2, Fq ), dπ i.
noncomputable def GaloisField_ringHom (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ+) :=
  (@GaloisField.algHom_of_dvd p _ k (2*k) (dvd_mul_left k 2)).toRingHom


noncomputable def SL2_monoidHom_SL2  {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ+} :
  SL(2, GaloisField p k.val) →* SL(2, GaloisField p (2* k.val)) :=
    Matrix.SpecialLinearGroup.map
      (@GaloisField.algHom_of_dvd p _ k (2*k) (dvd_mul_left k 2)).toRingHom

open SpecialMatrices

noncomputable def SL2_join_d (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ+) (π : (GaloisField p (2* k.val))ˣ ) :=
 (Subgroup.map (@SL2_monoidHom_SL2 p _ k) (⊤ : Subgroup SL(2, GaloisField p k.val)))
  ⊔
  Subgroup.closure { d π }


/-- Butler Case V (tex 1848-2113): `s = 0, t = 2`. Forces `q > 1`, `k > 1` and (via a
Sylow-orbit/projective-line argument entirely outside the class-equation arithmetic, tex
~1866-2071) `k ∈ {g₁, g₂}`; the remaining analysis splits on `q`: `q ≥ 4` gives Cases Va/Vb
(`G ≅ SL(2,𝔽_q)` resp. `G ≅ ⟨SL(2,𝔽_q), d_π⟩`), while `q ≤ 3` forces `q = p = 3` and splits into
Case Vc (`g₂ = 4`, again `⟨SL(2,𝔽_q), d_π⟩` with `q = 3`) and Case Vd (`g₂ = 5`, `G ≅ SL(2,5)` with
`p = q = 3`, tex ~2088-2113, via the `G/Z` simple-of-order-`60` argument).
Status: statement faithful to paper; proof pending (needs `CaseArithmetic.case_0_2` plus the
substantial projective-line/orbit-counting argument of tex ~1866-2113, well outside pure
class-equation arithmetic). -/
lemma case_V {F : Type*} {p : ℕ} [Fact (Nat.Prime p)] [Field F] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q)
    (heq : ∃ k g1 g2, 2 ≤ g1 ∧ 2 ≤ g2 ∧ 2 * g1 ≤ g ∧ 2 * g2 ≤ g ∧
      ClassEquation g q k (s := 0) (t := 2) (fun i => i.elim0) ![g1, g2]) :
    (∃ k : ℕ+, Isomorphic G SL(2, GaloisField p k.val)) ∨
      (∃ k : ℕ+, ∃ π : (GaloisField p (2 * k.val))ˣ, Isomorphic G (SL2_join_d p k π)) ∨
      (p = 3 ∧ Isomorphic G SL(2, ZMod 5)) := by sorry

inductive Symbols
 | x
 | y

open FreeGroup Symbols PresentedGroup

/-
Relations for the group presentation ⟨x, y | x^n = y^2, y * x * y⁻¹ = x⁻¹ ⟩
-/
def Relations (n : ℕ) : Set (FreeGroup (Symbols)) :=
  {.of x ^ n * (.of y)⁻¹ * (.of y)⁻¹ } ∪
  {.of y * .of x * (.of y)⁻¹ * .of x }

abbrev D (n : ℕ) :=
  PresentedGroup <| Relations n

/-! ### Binary octahedral group `2O` = Butler's `Ŝ₄` (DIVERGENCES.md item 3)

Butler's `Ŝ₄` (tex 2121-2125, 2200) is *the* representation group of `S₄` in which
transpositions lift to elements of order `4` -- citing Suzuki, `S₄` has exactly two double
covers, and this property picks out the **binary octahedral group `2O`** (order `48`), *not*
`GL(2,3)` (the other cover, in which transpositions lift to order-`2` elements, i.e. `GL(2,3)`
has non-central involutions and hence cannot embed in `SL(2,F)` for `p ≠ 2`, which has a
*unique* involution). An earlier draft of this file wrongly rendered `Ŝ₄` as
`GL (Fin 2) (ZMod 3)`; this is corrected here by presenting `2O` directly as the `⟨4,3,2⟩`
binary polyhedral (von Dyck) group `⟨x, y | x⁴ = y³ = (xy)²⟩` (the common central element
`x⁴ = y³ = (xy)²` is the order-`2` element `-1`; modulo it, this is the `(2,3,4)` triangle-group
presentation of the rotation group of the octahedron, `≅ S₄`, order `24`, so the binary cover
has order `48`, matching `Ŝ₄`). See `DIVERGENCES.md` item 3. -/
def BinaryOctahedralRelations : Set (FreeGroup Symbols) :=
  { .of x ^ 4 * ((.of y) ^ 3)⁻¹ } ∪
  { .of x ^ 4 * ((.of x * .of y) ^ 2)⁻¹ }

/-- The **binary octahedral group** `2O` (order `48`), i.e. Butler's `Ŝ₄` -- the representation
group of `S₄` in which transpositions lift to order-`4` elements (tex 2200) -- presented as
`⟨x, y | x⁴ = y³ = (xy)²⟩`. See the module note above and `DIVERGENCES.md` item 3. -/
abbrev BinaryOctahedralGroup := PresentedGroup BinaryOctahedralRelations

/-- **Arithmetic + group-recognition core for Case VI**, factored out of `case_VI` so the
`WLOG g₁ ≤ g₂ ≤ g₃` argument (tex ~2142-2161) only has to build the *ordered* witness data once
per branch (of the six orderings of `(A₁,g₁), (A₂,g₂), (A₃,g₃)`) and delegate here, rather than
duplicating this whole argument six times.

Takes the class-equation data already specialized to `q = 1` (`hsum`, i.e. Butler's Equation
`\eqref{case6b}` `1/(2g_a) + 1/(2g_b) + 1/(2g_c) = 1/g + 1/2`) together with an *assumed* ordering
`ga ≤ gb ≤ gc`, and:
* (pure arithmetic, tex ~2142-2148) forces `ga = 2` (else all three terms are `≤ 1/6`, but their
  sum must exceed `1/2` since `1/g > 0`) and then `gb ∈ {2,3}` (else `2/(2gb) ≤ 1/8` forces the
  remaining sum `≤ 1/4`, contradicting it exceeding `1/4`);
* **Case VIa** (`gb = 2`, tex ~2163-2171, so `ga = gb = 2`): derives `g = 2 gc` and, mirroring
  `case_II`'s Case IIa block (`Aa` playing `case_II`'s `A₁`, `Ac` its `A₂`) but *without* needing
  `case_II`'s Sylow-2/oddness detour (only used there to pin `g₂`'s *parity*, which here is
  established independently -- the `y² = x^{gc}`-pinning argument itself never actually needed
  that oddness): `p ≠ 2` (else `Nat.card (center SL(2,F)) = 1` makes `Nat.card G = g = 2gc` even,
  contradicting `p ∤ Nat.card G` at `p = 2`), `Nat.card (center SL(2,F)) = 2`, `Even gc` (Butler's
  own `[G : N_G(A_a)] = g/4 = gc/2` integrality argument, tex ~2163-2165), and finally the
  dicyclic presentation via `mulEquiv_quaternionGroup_of`;
* **Cases VIb/VIc** (`gb = 3`, forcing `gc ∈ {3,4,5}` by the same style of bound) are sorried:
  `gc = 3` needs Butler's Sylow-conjugacy elimination (tex ~2149-2157, showing this numerical
  solution is *vacuous* -- the two order-`3` classes `A_b, A_c` would have to be conjugate,
  contradicting `t = 3`) which is genuinely group-theoretic, not pure arithmetic, and is not
  attempted here; `gc = 4` needs the `Ŝ₄`/`BinaryOctahedralGroup` representation-group argument
  (tex ~2173-2201); `gc = 5` needs the `SL(2,5)`-relabelling argument citing (the also-sorried)
  Case Vd (tex ~2202-2205). -/
private lemma case_VI_core {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F]
    [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (g : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g) (hgpos : 1 ≤ g)
    (hp_ndvd : ¬ p ∣ Nat.card G)
    (ga gb gc : ℕ) (hab : ga ≤ gb) (hbc : gb ≤ gc)
    (hga_ge : 2 ≤ ga) (hgb_ge : 2 ≤ gb) (hgc_ge : 2 ≤ gc)
    (Aa : Subgroup SL(2,F)) (hAa_mem : Aa ∈ MaximalAbelianSubgroupsOf G)
    (hAa_cop : Nat.Coprime (Nat.card Aa) p)
    (hAa_card : Nat.card Aa = Nat.card (center SL(2,F)) * ga)
    (hAa_relIndex : relIndex (Aa.subgroupOf G) (normalizer (Aa.subgroupOf G : Set ↥G)) = 2)
    (Ac : Subgroup SL(2,F)) (hAc_mem : Ac ∈ MaximalAbelianSubgroupsOf G)
    (hAc_cyc : IsCyclic Ac) (hAc_cop : Nat.Coprime (Nat.card Ac) p)
    (hAc_card : Nat.card Ac = Nat.card (center SL(2,F)) * gc)
    (hAc_relIndex : relIndex (Ac.subgroupOf G) (normalizer (Ac.subgroupOf G : Set ↥G)) = 2)
    (hsum : (1 : ℚ) = 1 / g + ((ga : ℚ) - 1) / (2 * ga) + ((gb : ℚ) - 1) / (2 * gb)
      + ((gc : ℚ) - 1) / (2 * gc)) :
    (∃ n, Even n ∧ Isomorphic G (QuaternionGroup n)) ∨
      Isomorphic G BinaryOctahedralGroup ∨
      (¬ p ∣ Nat.card G ∧ Isomorphic G SL(2, ZMod 5)) := by
  have hgQpos : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hgpos
  have hgaQpos : (0 : ℚ) < (ga : ℚ) := by exact_mod_cast (by omega : 0 < ga)
  have hgbQpos : (0 : ℚ) < (gb : ℚ) := by exact_mod_cast (by omega : 0 < gb)
  have hgcQpos : (0 : ℚ) < (gc : ℚ) := by exact_mod_cast (by omega : 0 < gc)
  have e1 : ((ga : ℚ) - 1) / (2 * ga) = 1 / 2 - 1 / (2 * ga) := one_sub_inv_two_self hgaQpos.ne'
  have e2 : ((gb : ℚ) - 1) / (2 * gb) = 1 / 2 - 1 / (2 * gb) := one_sub_inv_two_self hgbQpos.ne'
  have e3 : ((gc : ℚ) - 1) / (2 * gc) = 1 / 2 - 1 / (2 * gc) := one_sub_inv_two_self hgcQpos.ne'
  rw [e1, e2, e3] at hsum
  have hkey : 1 / (2 * (ga : ℚ)) + 1 / (2 * gb) + 1 / (2 * gc) = 1 / g + 1 / 2 := by linarith
  -- `ga = 2` (tex ~2142-2145): otherwise `ga, gb, gc ≥ 3`, and the three terms sum to `≤ 1/2`.
  have hga_lt3 : ga < 3 := by
    by_contra hcon
    push_neg at hcon
    have hb3 : 3 ≤ gb := le_trans hcon hab
    have hc3 : 3 ≤ gc := le_trans hb3 hbc
    have ba : (1 : ℚ) / (2 * ga) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (3 : ℚ) ≤ (ga : ℚ) := by exact_mod_cast hcon
      linarith
    have bb : (1 : ℚ) / (2 * gb) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (3 : ℚ) ≤ (gb : ℚ) := by exact_mod_cast hb3
      linarith
    have bc : (1 : ℚ) / (2 * gc) ≤ 1 / 6 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (3 : ℚ) ≤ (gc : ℚ) := by exact_mod_cast hc3
      linarith
    have hgpos' : (0 : ℚ) < 1 / g := by positivity
    linarith
  have hga_eq2 : ga = 2 := by omega
  have hgaQ2 : (ga : ℚ) = 2 := by exact_mod_cast hga_eq2
  rw [hgaQ2] at hkey
  have h4 : (1 : ℚ) / (2 * 2) = 1 / 4 := by norm_num
  rw [h4] at hkey
  have hkey2 : 1 / (2 * (gb : ℚ)) + 1 / (2 * gc) = 1 / g + 1 / 4 := by linarith
  -- `gb ∈ {2,3}` (tex ~2146-2149): otherwise `gb, gc ≥ 4`, and the two remaining terms sum to
  -- `≤ 1/4`.
  have hgb_lt4 : gb < 4 := by
    by_contra hcon
    push_neg at hcon
    have hc4 : 4 ≤ gc := le_trans hcon hbc
    have bb : (1 : ℚ) / (2 * gb) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (4 : ℚ) ≤ (gb : ℚ) := by exact_mod_cast hcon
      linarith
    have bc : (1 : ℚ) / (2 * gc) ≤ 1 / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (4 : ℚ) ≤ (gc : ℚ) := by exact_mod_cast hc4
      linarith
    have hgpos' : (0 : ℚ) < 1 / g := by positivity
    linarith
  have hgb_23 : gb = 2 ∨ gb = 3 := by omega
  rcases hgb_23 with hgb2 | hgb3
  · -- **Case VIa** (`ga = 2, gb = 2`, tex ~2163-2171).
    left
    have hgbQ2 : (gb : ℚ) = 2 := by exact_mod_cast hgb2
    rw [hgbQ2, h4] at hkey2
    have hcore : (1 : ℚ) / (2 * gc) = 1 / g := by linarith
    have hgeqQ : (g : ℚ) = 2 * gc := by
      rw [div_eq_div_iff (by positivity) hgQpos.ne'] at hcore
      linarith
    have hgeq : g = 2 * gc := by exact_mod_cast hgeqQ
    -- `Even gc`: `[G : N_G(A_a)]` is a genuine index, hence a natural number, forcing `gc` even
    -- (tex ~2163-2165, `[G:N_G(A_1)] = g_3/2`).
    set Aa' : Subgroup ↥G := Aa.subgroupOf G with hAa'_def
    set Nz : Subgroup ↥G := normalizer (Aa' : Set ↥G) with hNz_def
    have hAa'_le_Nz : Aa' ≤ Nz := Subgroup.le_normalizer
    have hcard_Nz : Nat.card Nz = 2 * Nat.card Aa' := by
      have h1 : Nat.card Nz
          = Nat.card (↥Nz ⧸ Aa'.subgroupOf Nz) * Nat.card (Aa'.subgroupOf Nz) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
      have h2 : Nat.card (Aa'.subgroupOf Nz) = Nat.card Aa' :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAa'_le_Nz).toEquiv
      have h3 : Nat.card (↥Nz ⧸ Aa'.subgroupOf Nz) = Aa'.relIndex Nz := rfl
      rw [h2, h3, hAa_relIndex] at h1
      exact h1
    have hcard_Aa' : Nat.card Aa' = Nat.card Aa :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAa_mem.right).toEquiv
    have hcard_idx : Nat.card G = Nat.card (↥G ⧸ Nz) * Nat.card Nz :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup Nz
    have hepos : 0 < Nat.card (center SL(2,F)) := Nat.card_pos
    have heq4e : Nat.card G = Nat.card (↥G ⧸ Nz) * (4 * Nat.card (center SL(2,F))) := by
      rw [hcard_idx, hcard_Nz, hcard_Aa', hAa_card, hga_eq2]; ring
    have hg4idx : g = 4 * Nat.card (↥G ⧸ Nz) := by
      have h1 : Nat.card (center SL(2,F)) * g
          = Nat.card (center SL(2,F)) * (4 * Nat.card (↥G ⧸ Nz)) := by
        rw [← hg, heq4e]; ring
      exact mul_left_cancel₀ hepos.ne' h1
    have hEvengc : Even gc := ⟨Nat.card (↥G ⧸ Nz), by omega⟩
    -- `p ≠ 2`: else `Nat.card (center SL(2,F)) = 1`, so `Nat.card G = g = 2gc` is even,
    -- contradicting `p ∤ Nat.card G` at `p = 2`.
    have hp_ne_two : p ≠ 2 := by
      intro hp2
      subst hp2
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have he1 : Nat.card (center SL(2,F)) = 1 := by
        rw [SpecialSubgroups.center_SL2_eq_Z]
        exact SpecialSubgroups.card_Z_eq_one_of_two_eq_zero h2
      apply hp_ndvd
      rw [hg, he1, one_mul, hgeq]
      exact ⟨gc, rfl⟩
    have he_le_two : Nat.card (center SL(2,F)) ≤ 2 := by
      rw [SpecialSubgroups.center_SL2_eq_Z]; exact SpecialSubgroups.card_Z_le_two
    have he_ne_one : Nat.card (center SL(2,F)) ≠ 1 := by
      intro he1
      have h2 : (2 : F) = 0 := by
        by_contra h2ne
        haveI : NeZero (2 : F) := ⟨h2ne⟩
        rw [SpecialSubgroups.center_SL2_eq_Z, SpecialSubgroups.card_Z_eq_two_of_two_ne_zero] at he1
        omega
      have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
      exact hp_ne_two (CharP.eq F (‹CharP F p› : CharP F p) hCharP2)
    have he2 : Nat.card (center SL(2,F)) = 2 := by
      have := Nat.card_pos (α := center SL(2,F)); omega
    classical
    -- The rest mirrors `case_II`'s Case IIa block verbatim (`Ac`/`gc` in the role of `A₂`/`g₂`),
    -- deriving Butler's `y² = x^{gc}` identification (tex ~1508-1520/2166-2169) via the same
    -- self-contained cyclic-group argument (maximality of `Ac` forces `y² ∈ Ac`; `y` both fixes
    -- and inverts `y²`, forcing `(y²)² = 1`; uniqueness of `SL(2,F)`'s involution `-1` rules out
    -- `y² = 1`; so `y²` is *the* order-`2` element of the cyclic group `Ac`).
    haveI hF2 : NeZero (2 : F) := ⟨by
      intro h2
      have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
      exact hp_ne_two (CharP.eq F (‹CharP F p› : CharP F p) hCharP2)⟩
    haveI hAc_fin : Finite Ac :=
      (Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hAc_mem.right).to_subtype
    obtain ⟨g0, hg0_gen⟩ := hAc_cyc.exists_generator
    have horder_g0 : orderOf g0 = Nat.card Ac := orderOf_eq_card_of_forall_mem_zpowers hg0_gen
    have horder_g0SL : orderOf (g0 : SL(2,F)) = 2 * gc := by
      rw [orderOf_coe, horder_g0, hAc_card, he2]
    haveI hg0_finord : IsOfFinOrder g0 := orderOf_pos_iff.mp (horder_g0 ▸ Nat.card_pos)
    obtain ⟨y, hy_mem, hy_conj⟩ :=
      of_index_normalizer_eq_two hp_ne_two Ac G hAc_mem center_le_G hAc_cop hAc_relIndex g0
    simp only [Set.mem_sdiff, SetLike.mem_coe, Subgroup.mem_carrier, Subgroup.mem_inf] at hy_mem
    obtain ⟨⟨hy_mem_norm, hy_mem_G⟩, hy_notin_Ac⟩ := hy_mem
    have hinvert : ∀ a : SL(2,F), a ∈ Ac → y * a * y⁻¹ = a⁻¹ := by
      intro a ha
      obtain ⟨n, hn⟩ := hg0_gen ⟨a, ha⟩
      have hn' : (g0 : SL(2,F)) ^ n = a := by
        have := congrArg (Subtype.val) hn
        simpa using this
      have hconj_pow : y * (g0 : SL(2,F)) ^ n * y⁻¹ = ((g0 : SL(2,F)) ^ n)⁻¹ := by
        have h1 := map_zpow (MulAut.conj y).toMonoidHom (g0 : SL(2,F)) n
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
        rw [h1, hy_conj, Subgroup.coe_inv, _root_.inv_zpow]
      rwa [hn'] at hconj_pow
    have hy2_comm : ∀ a : SL(2,F), a ∈ Ac → y ^ 2 * a = a * y ^ 2 := by
      intro a ha
      have h1 : y * a = a⁻¹ * y := by
        have h := hinvert a ha
        have h2 : y * a * y⁻¹ * y = a⁻¹ * y := by rw [h]
        simpa [mul_assoc] using h2
      have h2 : y * a⁻¹ = a * y := by
        have h := hinvert a⁻¹ (Subgroup.inv_mem Ac ha)
        rw [inv_inv] at h
        have h3 : y * a⁻¹ * y⁻¹ * y = a * y := by rw [h]
        simpa [mul_assoc] using h3
      calc y ^ 2 * a = y * y * a := by rw [pow_two]
        _ = y * (y * a) := by rw [mul_assoc]
        _ = y * (a⁻¹ * y) := by rw [h1]
        _ = y * a⁻¹ * y := by rw [mul_assoc]
        _ = (a * y) * y := by rw [h2]
        _ = a * (y * y) := by rw [mul_assoc]
        _ = a * y ^ 2 := by rw [pow_two]
    have hy2_mem_G : y ^ 2 ∈ G := Subgroup.pow_mem G hy_mem_G 2
    set Ac' : Subgroup ↥G := Ac.subgroupOf G with hAc'_def
    set y2' : ↥G := ⟨y ^ 2, hy2_mem_G⟩ with hy2'_def
    have hy2_mem_Ac : y ^ 2 ∈ Ac := by
      set kset : Set ↥G := (Ac' : Set ↥G) ∪ {y2'} with hkset_def
      have hcomm_k : ∀ a ∈ kset, ∀ b ∈ kset, a * b = b * a := by
        haveI := hAc_mem.left.1
        rintro a (ha | ha) b (hb | hb)
        · exact setLike_mul_comm ha hb
        · simp only [Set.mem_singleton_iff] at hb; subst hb
          apply Subtype.ext
          have ha' : (a : SL(2,F)) ∈ Ac := by
            rw [SetLike.mem_coe, hAc'_def, Subgroup.mem_subgroupOf] at ha; exact ha
          simpa [hy2'_def] using (hy2_comm a ha').symm
        · simp only [Set.mem_singleton_iff] at ha; subst ha
          apply Subtype.ext
          have hb' : (b : SL(2,F)) ∈ Ac := by
            rw [SetLike.mem_coe, hAc'_def, Subgroup.mem_subgroupOf] at hb; exact hb
          simpa [hy2'_def] using hy2_comm b hb'
        · simp only [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
      haveI hclosure_comm : IsMulCommutative (closure kset) :=
        Subgroup.isMulCommutative_closure hcomm_k
      have hAc'_le_closure : Ac' ≤ closure kset := by
        rw [← Subgroup.closure_eq Ac']
        exact Subgroup.closure_mono (Set.subset_union_left)
      have hclosure_le : closure kset ≤ Ac' := hAc_mem.left.2 hclosure_comm hAc'_le_closure
      have hy2'_mem_closure : y2' ∈ closure kset := subset_closure (Set.mem_union_right _ rfl)
      have hy2'_mem_Ac' : y2' ∈ Ac' := hclosure_le hy2'_mem_closure
      rwa [hAc'_def, Subgroup.mem_subgroupOf] at hy2'_mem_Ac'
    have h1 : y * y ^ 2 * y⁻¹ = (y ^ 2)⁻¹ := hinvert (y ^ 2) hy2_mem_Ac
    have h2 : y * y ^ 2 * y⁻¹ = y ^ 2 := by group
    have hz0_inv : (y ^ 2)⁻¹ = y ^ 2 := h1.symm.trans h2
    have hz0sq : y ^ 2 * y ^ 2 = 1 := by
      calc y ^ 2 * y ^ 2 = y ^ 2 * (y ^ 2)⁻¹ := by rw [hz0_inv]
        _ = 1 := mul_inv_cancel _
    have hy2_ne_one : y ^ 2 ≠ 1 := by
      intro hy2eq1
      have hy_ne_one : y ≠ 1 := by
        intro hy1
        apply hy_notin_Ac
        rw [hy1]
        exact Subgroup.one_mem Ac
      have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2eq1
      have hord_ne_one : orderOf y ≠ 1 := by
        rw [Ne, orderOf_eq_one_iff]; exact hy_ne_one
      have hy_ord2 : orderOf y = 2 := by
        rcases Nat.prime_two.eq_one_or_self_of_dvd _ hdvd with h | h
        · exact absurd h hord_ne_one
        · exact h
      have hy_eq_negone : y = -1 :=
        SpecialSubgroups.exists_unique_orderOf_eq_two.unique hy_ord2
          SpecialSubgroups.orderOf_neg_one_eq_two
      apply hy_notin_Ac
      rw [hy_eq_negone]
      have hcenle : center SL(2,F) ≤ Ac := center_le G Ac hAc_mem center_le_G
      apply hcenle
      rw [SpecialSubgroups.center_SL2_eq_Z]
      exact SpecialSubgroups.neg_one_mem_Z
    have hz0sq' : (y ^ 2) ^ 2 = 1 := by
      have hexp : (y ^ 2) ^ 2 = y ^ 2 * y ^ 2 := by group
      rw [hexp]; exact hz0sq
    have hz0mem : (⟨y ^ 2, hy2_mem_Ac⟩ : Ac) ∈ Subgroup.zpowers g0 := hg0_gen _
    rw [hg0_finord.mem_zpowers_iff_mem_range_orderOf] at hz0mem
    simp only [Finset.mem_image, Finset.mem_range] at hz0mem
    obtain ⟨n, hn_lt, hn_eq⟩ := hz0mem
    have hn_eq' : (g0 : SL(2,F)) ^ n = y ^ 2 := by
      have := congrArg (Subtype.val) hn_eq
      simpa using this
    have horder_g0_eq : orderOf g0 = 2 * gc := by rw [horder_g0, hAc_card, he2]
    rw [horder_g0_eq] at hn_lt
    have hn2 : (g0 : SL(2,F)) ^ (n * 2) = 1 := by
      rw [pow_mul, hn_eq']; exact hz0sq'
    have hdvd1 : orderOf (g0 : SL(2,F)) ∣ n * 2 := orderOf_dvd_of_pow_eq_one hn2
    rw [horder_g0SL] at hdvd1
    have hgc_dvd_n : gc ∣ n := by
      have h1 : gc * 2 ∣ n * 2 := by rwa [mul_comm 2 gc] at hdvd1
      exact (Nat.mul_dvd_mul_iff_right (by norm_num : (0 : ℕ) < 2)).mp h1
    obtain ⟨t, ht⟩ := hgc_dvd_n
    have hn_ne : ¬ (2 * gc) ∣ n := by
      intro hdvd
      apply hy2_ne_one
      have hdvd' : orderOf (g0 : SL(2,F)) ∣ n := by rw [horder_g0SL]; exact hdvd
      rw [← hn_eq']
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd'
    have ht2 : ¬ 2 ∣ t := by
      intro h2t
      apply hn_ne
      rw [ht]
      obtain ⟨j, hj⟩ := h2t
      exact ⟨j, by rw [hj]; ring⟩
    have ht_lt : t < 2 := by
      by_contra hcon
      push_neg at hcon
      have hge : 2 * gc ≤ gc * t := by
        calc 2 * gc = gc * 2 := by ring
          _ ≤ gc * t := Nat.mul_le_mul_left gc hcon
      rw [← ht] at hge
      omega
    have ht_eq : t = 1 := by omega
    have hn_eq_gc : n = gc := by rw [ht, ht_eq, mul_one]
    have hy2eq : y ^ 2 = (g0 : SL(2,F)) ^ gc := by rw [← hn_eq_gc]; exact hn_eq'.symm
    haveI : NeZero gc := ⟨by omega⟩
    set x0 : ↥G := ⟨(g0 : SL(2,F)), hAc_mem.right g0.2⟩ with hx0_def
    set y0 : ↥G := ⟨y, hy_mem_G⟩ with hy0_def
    have hx0_ord : orderOf x0 = 2 * gc := by
      have h := orderOf_injective G.subtype (Subgroup.subtype_injective G) x0
      rw [← h]; exact horder_g0SL
    have hy0_2 : y0 ^ 2 = x0 ^ gc := Subtype.ext hy2eq
    have hconj0 : y0 * x0 * y0⁻¹ = x0⁻¹ := Subtype.ext hy_conj
    have hyx0 : y0 ∉ Subgroup.zpowers x0 := by
      intro hmem
      obtain ⟨kk, hk⟩ := hmem
      apply hy_notin_Ac
      have hk' : (g0 : SL(2,F)) ^ kk = y := by
        have := congrArg (Subtype.val) hk
        simpa using this
      rw [← hk']
      exact Subgroup.zpow_mem Ac g0.2 kk
    have hcardG4gc : Nat.card G = 4 * gc := by rw [hg, he2, hgeq]; ring
    exact ⟨gc, hEvengc, ⟨mulEquiv_quaternionGroup_of x0 y0 hx0_ord hy0_2 hconj0 hyx0 hcardG4gc⟩⟩
  · -- **Cases VIb/VIc** (`ga = 2, gb = 3`): the arithmetic pins `gc ∈ {3,4,5}`, but beyond that
    -- Butler eliminates `gc = 3` via a Sylow-conjugacy argument showing the two order-`3` classes
    -- `A_b`, `A_c` are forced to be conjugate (tex ~2149-2157), contradicting `t = 3` -- genuinely
    -- group-theoretic, not pure arithmetic, and not attempted here. `gc = 4` (Case VIb, `Ŝ₄`) and
    -- `gc = 5` (Case VIc, `SL(2,5)`) are separate substantial arguments (tex ~2173-2205), also not
    -- attempted here. See the docstring above.
    have hgbQ3 : (gb : ℚ) = 3 := by exact_mod_cast hgb3
    have h6 : (1 : ℚ) / (2 * 3) = 1 / 6 := by norm_num
    rw [hgbQ3, h6] at hkey2
    have hgc_ge3 : 3 ≤ gc := by omega
    have hgc_lt6 : gc < 6 := by
      by_contra hcon
      push_neg at hcon
      have bc : (1 : ℚ) / (2 * gc) ≤ 1 / 12 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        have : (6 : ℚ) ≤ (gc : ℚ) := by exact_mod_cast hcon
        linarith
      have hgpos' : (0 : ℚ) < 1 / g := by positivity
      linarith
    have hgc_345 : gc = 3 ∨ gc = 4 ∨ gc = 5 := by omega
    rcases hgc_345 with hgc3 | hgc4 | hgc5
    · -- TODO: `(ga,gb,gc) = (2,3,3)` needs Butler's Sylow-conjugacy elimination showing this
      -- numerical solution is vacuous (tex ~2149-2157); not attempted here.
      sorry
    · -- TODO: Case VIb, `Ŝ₄`/`BinaryOctahedralGroup` representation-group argument (tex ~2173-2201).
      sorry
    · -- TODO: Case VIc, `SL(2,5)` relabelling from Case Vd (tex ~2202-2205, itself sorried).
      sorry

/-- Butler Case VI (tex 2115-2160): `s = 0, t = 3`. Forces `q = 1` (`CaseArithmetic.case_0_3`)
and, via a further elementary argument (tex ~2145-2156), `g₁ = 2` with
`(g₂,g₃) ∈ {(2,n), (3,4), (3,5)}`. Case VIa (`g₂ = 2`) gives the dicyclic group of order `4n`
(`n` even) as `QuaternionGroup n`; Case VIb (`g₂ = 3, g₃ = 4`) gives `Ŝ₄`, the representation
group of `S₄` in which transpositions have order `4`, i.e. the **binary octahedral group**
`BinaryOctahedralGroup` (*not* `GL(2,3)` -- see the module note above and `DIVERGENCES.md`
item 3); Case VIc (`g₂ = 3, g₃ = 5`) gives `G ≅ SL(2,5)`, this time with `p ∤ |G|`
(unlike the isomorphic-but-distinct Case Vd, where `p = 3 = q`).

RESTATED (justification: as in `case_I`/`case_II`/`case_IV`, the previous `heq : ∃ k g1 g2 g3, ...`
hid Butler's three cyclic maximal abelian subgroups `A₁, A₂, A₃` (all `t`-classes, normalizer
index `2`, since `s = 0` here) behind bare numerals. Restated to carry all three witnesses
directly; `[IsAlgClosed F] [DecidableEq F]` added (needed for any further `S2_B` argument on
these witnesses, matching the other restated cases).

**PROVED up to and including Case VIa** (`ga = gb = 2`, the `(2,2,n)` numeral family, `n` forced
even): `CaseArithmetic.case_0_3` gives `q = 1` directly; the further `g₁ = 2` numeral split (tex
~2145-2156) needs a genuine `WLOG g₁ ≤ g₂ ≤ g₃` argument (the three witness subgroups `A₁, A₂, A₃`
carry no built-in ordering), so the six orderings of `(A₁,g₁), (A₂,g₂), (A₃,g₃)` are enumerated
explicitly below (`rcases le_total` three times, one per pairwise comparison) and each delegates
to `case_VI_core` above, which does the rest of the arithmetic and (for Case VIa) the full
group-recognition argument. **Cases VIb/VIc remain sorried** inside `case_VI_core`: see its own
docstring for exactly what is missing (Butler's Sylow-conjugacy elimination of the `(2,3,3)`
numerical solution, the `Ŝ₄` representation-group argument, and the `SL(2,5)`-relabelling
argument respectively). -/
lemma case_VI {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F] [Fact (Nat.Prime p)]
    [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q) (g1 g2 g3 k : ℕ)
    -- witnesses for the three `t = 3` classes `A₁, A₂, A₃` (Theorem 6.8), replacing the bare
    -- numerals `g1, g2, g3` that the original `heq : ∃ k g1 g2 g3, ...` hid them behind.
    (A1 : Subgroup SL(2,F)) (hA1_mem : A1 ∈ MaximalAbelianSubgroupsOf G)
    (hA1_cyc : IsCyclic A1) (hA1_cop : Nat.Coprime (Nat.card A1) p)
    (hA1_card : Nat.card A1 = Nat.card (center SL(2,F)) * g1)
    (hA1_relIndex : relIndex (A1.subgroupOf G) (normalizer (A1.subgroupOf G : Set ↥G)) = 2)
    (A2 : Subgroup SL(2,F)) (hA2_mem : A2 ∈ MaximalAbelianSubgroupsOf G)
    (hA2_cyc : IsCyclic A2) (hA2_cop : Nat.Coprime (Nat.card A2) p)
    (hA2_card : Nat.card A2 = Nat.card (center SL(2,F)) * g2)
    (hA2_relIndex : relIndex (A2.subgroupOf G) (normalizer (A2.subgroupOf G : Set ↥G)) = 2)
    (A3 : Subgroup SL(2,F)) (hA3_mem : A3 ∈ MaximalAbelianSubgroupsOf G)
    (hA3_cyc : IsCyclic A3) (hA3_cop : Nat.Coprime (Nat.card A3) p)
    (hA3_card : Nat.card A3 = Nat.card (center SL(2,F)) * g3)
    (hA3_relIndex : relIndex (A3.subgroupOf G) (normalizer (A3.subgroupOf G : Set ↥G)) = 2)
    -- `1 ≤ k` added: needed to invoke `CaseArithmetic.case_0_3` below (`k = 0` is not excluded
    -- by the equation itself, division by `0` being `0` in Lean's convention); every sibling
    -- restated lemma in this file (`case_I`/`case_II`/`case_IV`) already carries this hypothesis,
    -- so this brings `case_VI` in line with them (the original statement's omission of it here
    -- looks like an oversight, not a deliberate weakening).
    (hk_ge : 1 ≤ k)
    (heq : 2 ≤ g1 ∧ 2 ≤ g2 ∧ 2 ≤ g3 ∧ (1 < k → k = g1 ∨ k = g2 ∨ k = g3) ∧
      ClassEquation g q k (s := 0) (t := 3) (fun i => i.elim0) ![g1, g2, g3]) :
    (∃ n, Even n ∧ Isomorphic G (QuaternionGroup n)) ∨
      Isomorphic G BinaryOctahedralGroup ∨
      (¬ p ∣ Nat.card G ∧ Isomorphic G SL(2, ZMod 5)) := by
  obtain ⟨hg1_ge, hg2_ge, hg3_ge, hKeq, heq'⟩ := heq
  have hgpos : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with hg0 | hgpos
    · exfalso; rw [hg0, mul_zero] at hg
      have := Nat.card_pos (α := G); omega
    · exact hgpos
  have hqpos : 1 ≤ q := by have := Nat.card_pos (α := Q.toSubgroup); omega
  have hq1 : q = 1 := case_0_3 g q k g1 g2 g3 hgpos hqpos hk_ge hg1_ge hg2_ge hg3_ge hKeq heq'
  subst hq1
  -- `p ∤ Nat.card G` (`q = 1` means the Sylow `p`-subgroup is trivial).
  have hp_ndvd : ¬ p ∣ Nat.card G := by
    have hme : Nat.card Q.toSubgroup = p ^ (Nat.card G).factorization p :=
      Sylow.card_eq_multiplicity Q
    rw [hq] at hme
    intro hdvd
    have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
    have hpos : 0 < (Nat.card G).factorization p :=
      (Fact.out : Nat.Prime p).factorization_pos_of_dvd hGne hdvd
    have h1lt : 1 < p ^ (Nat.card G).factorization p :=
      Nat.one_lt_pow hpos.ne' (Fact.out : Nat.Prime p).one_lt
    omega
  -- the class equation, with `q = 1` substituted (Butler's Equation `\eqref{case6b}`).
  have hsum0 : (1 : ℚ) = 1 / g + ((g1 : ℚ) - 1) / (2 * g1) + ((g2 : ℚ) - 1) / (2 * g2)
      + ((g3 : ℚ) - 1) / (2 * g3) := by
    have heqq := heq'
    unfold ClassEquation at heqq
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
      Matrix.tail_cons, Nat.cast_one, sub_self, zero_div, add_zero, one_mul] at heqq
    linarith [heqq]
  -- **WLOG `g₁ ≤ g₂ ≤ g₃`** (tex ~2142): six branches, one per ordering of the three witnesses
  -- `(A₁,g₁), (A₂,g₂), (A₃,g₃)`, each delegating to `case_VI_core`.
  rcases le_total g1 g2 with h12 | h12
  · rcases le_total g2 g3 with h23 | h23
    · -- `g1 ≤ g2 ≤ g3`
      exact case_VI_core G center_le_G g hg hgpos hp_ndvd g1 g2 g3 h12 h23
        hg1_ge hg2_ge hg3_ge A1 hA1_mem hA1_cop hA1_card hA1_relIndex
        A3 hA3_mem hA3_cyc hA3_cop hA3_card hA3_relIndex (by linarith [hsum0])
    · rcases le_total g1 g3 with h13 | h13
      · -- `g1 ≤ g3 ≤ g2`
        exact case_VI_core G center_le_G g hg hgpos hp_ndvd g1 g3 g2 h13 h23
          hg1_ge hg3_ge hg2_ge A1 hA1_mem hA1_cop hA1_card hA1_relIndex
          A2 hA2_mem hA2_cyc hA2_cop hA2_card hA2_relIndex (by linarith [hsum0])
      · -- `g3 ≤ g1 ≤ g2`
        exact case_VI_core G center_le_G g hg hgpos hp_ndvd g3 g1 g2 h13 h12
          hg3_ge hg1_ge hg2_ge A3 hA3_mem hA3_cop hA3_card hA3_relIndex
          A2 hA2_mem hA2_cyc hA2_cop hA2_card hA2_relIndex (by linarith [hsum0])
  · rcases le_total g1 g3 with h13 | h13
    · -- `g2 ≤ g1 ≤ g3`
      exact case_VI_core G center_le_G g hg hgpos hp_ndvd g2 g1 g3 h12 h13
        hg2_ge hg1_ge hg3_ge A2 hA2_mem hA2_cop hA2_card hA2_relIndex
        A3 hA3_mem hA3_cyc hA3_cop hA3_card hA3_relIndex (by linarith [hsum0])
    · rcases le_total g2 g3 with h23 | h23
      · -- `g2 ≤ g3 ≤ g1`
        exact case_VI_core G center_le_G g hg hgpos hp_ndvd g2 g3 g1 h23 h13
          hg2_ge hg3_ge hg1_ge A2 hA2_mem hA2_cop hA2_card hA2_relIndex
          A1 hA1_mem hA1_cyc hA1_cop hA1_card hA1_relIndex (by linarith [hsum0])
      · -- `g3 ≤ g2 ≤ g1`
        exact case_VI_core G center_le_G g hg hgpos hp_ndvd g3 g2 g1 h23 h12
          hg3_ge hg2_ge hg1_ge A3 hA3_mem hA3_cop hA3_card hA3_relIndex
          A1 hA1_mem hA1_cyc hA1_cop hA1_card hA1_relIndex (by linarith [hsum0])


 -- (v) Ŝ₄ , the representation group of S4 in which the transpositions correspond to
-- the elements of order 4.

instance five_prime : Fact (Nat.Prime 5) := { out := by decide }

/-- Auxiliary for threading `BridgeData` into `case_IV`/`case_V`'s own `2 * g1 ≤ g`-style numeral
hypotheses (Butler's implicit "the number of conjugates of `A` is a positive integer", not carried
by `BridgeData` directly): a coprime-type class `A` with normalizer index `2` has
`2 * Nat.card A ≤ Nat.card G`, via Lagrange applied to `A ≤ N_G(A) ≤ G` (`[N_G(A):A] = 2` gives
`Nat.card (N_G(A)) = 2 * Nat.card A`; mirrors the `hcard_N_via_K'` computation inside `case_I`
above). -/
lemma two_card_le_of_relIndex_normalizer_eq_two {F : Type*} [Field F]
    (G A : Subgroup SL(2,F)) [Finite G] (hA_le : A ≤ G)
    (hrelIndex : relIndex (A.subgroupOf G) (normalizer ((A.subgroupOf G) : Set ↥G)) = 2) :
    2 * Nat.card A ≤ Nat.card G := by
  set A' : Subgroup ↥G := A.subgroupOf G with hA'_def
  set N : Subgroup ↥G := normalizer (A' : Set ↥G) with hN_def
  have hA'_le_N : A' ≤ N := Subgroup.le_normalizer
  have hcard_N : Nat.card N = 2 * Nat.card A' := by
    have h1 : Nat.card N = Nat.card (↥N ⧸ A'.subgroupOf N) * Nat.card (A'.subgroupOf N) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have h2 : Nat.card (A'.subgroupOf N) = Nat.card A' :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'_le_N).toEquiv
    have h3 : Nat.card (↥N ⧸ A'.subgroupOf N) = A'.relIndex N := rfl
    rw [h2, h3, hrelIndex] at h1
    exact h1
  have hA'_card : Nat.card A' = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le).toEquiv
  have hNdvd : Nat.card N ∣ Nat.card G := Subgroup.card_subgroup_dvd_card N
  have hNle : Nat.card N ≤ Nat.card G := Nat.le_of_dvd Nat.card_pos hNdvd
  rw [hA'_card] at hcard_N
  omega

/-- **Theorem 3.6, Class I** (tex 2213-2226, "Class I: when `p = 0` or `|G|` is relatively prime
to `p`"). Every finite subgroup `G ≤ SL(2,F)` of order coprime to `p` (or with `p = 0`) is
isomorphic to one of: a cyclic group; the dicyclic group `⟨x,y | x^n = y^2, yxy⁻¹ = x⁻¹⟩` of order
`4n` for *arbitrary* `n` (mathlib's `QuaternionGroup n`, tex Class I (ii), covering both Case IIa
`n` odd and Case VIa `n` even); `SL(2,3)`; `SL(2,5)`; or `Ŝ₄` (the representation group of `S₄`
with transpositions of order `4`, tex Class I (v)), i.e. the **binary octahedral group**
`BinaryOctahedralGroup` (*not* `GL(2,3)` -- see the module note above `BinaryOctahedralGroup`
and `DIVERGENCES.md` item 3: `GL(2,3)` is the *other* double cover of `S₄`, with order-`2`
transposition lifts and non-central involutions, so it cannot embed in `SL(2,F)` for `p ≠ 2`).
Note: the original statement here had `DihedralGroup n` for a file-level auto-bound `n : Type*`
(ill-typed/vacuously-scoped), and used the *dihedral* group where `SL(2,F)` (with `p ≠ 2`, having
a unique involution) actually only ever produces the *dicyclic*/quaternion group; both bugs are
fixed here. A subsequent draft then used `GL (Fin 2) (ZMod 3)` for `Ŝ₄`; also fixed, see above.
Status: statement faithful to paper; **dispatch structure implemented** (`center_le_G` and
`hp2 : p ≠ 2` added as narrowing hypotheses to invoke `S5_NumericClassEquation.exists_bridgeData`
and dispatch on `CaseArithmetic.case_enumeration`'s six `(s,t)` branches into `case_I` ... `case_VI`
above); the `G = center SL(2,F)` case (where `exists_bridgeData` does not apply) is handled
directly (`center SL(2,F)` is cyclic, `S2_SpecialSubgroups.IsCyclic_Z`). Remaining gaps are
exactly the per-branch pieces documented at each `sorry` inside the proof, plus two *global*
items intentionally left out of scope here (see `DIVERGENCES.md`): the `Z ⊄ G ⟹ |G|` odd `⟹`
Case I/III reduction (this theorem's `hp'` disjunct `p = 0 ∨ Nat.Coprime (Nat.card G) p` does not
itself guarantee `center SL(2,F) ≤ G`, which every case lemma above requires), and the char-`2`
finale (`hp2 : p ≠ 2` rules out the `p = 2` branch of Dickson's classification entirely, matching
`case_IV`'s own residual `p = 2` gap). -/
-- ANCHOR: dicksons_classification_theorem_class_I
theorem dicksons_classification_theorem_class_I {F : Type*} [Field F] [IsAlgClosed F]
    [DecidableEq F] {p : ℕ} [CharP F p] (hp : Prime p) (G : Subgroup (SL(2,F))) [Finite G]
    (hp' : p = 0 ∨ Nat.Coprime (Nat.card G) p)
    -- Narrowing hypotheses (see the docstring above and `DIVERGENCES.md`): `center_le_G` is
    -- needed by every `case_*` lemma above, and `hp2` is needed by `exists_bridgeData` (its own
    -- `p = 2` gap traces back to `case_IV`'s char-`2` branch, `DIVERGENCES.md` item 1).
    (center_le_G : center SL(2,F) ≤ G) (hp2 : p ≠ 2) :
    IsCyclic G ∨
      (∃ n, Isomorphic G (QuaternionGroup n)) ∨
      Isomorphic G SL(2, ZMod 3) ∨
      Isomorphic G SL(2, ZMod 5) ∨
      Isomorphic G BinaryOctahedralGroup := by
  haveI : Fact (Nat.Prime p) := ⟨hp.nat_prime⟩
  by_cases hG_ne : G = center SL(2,F)
  · -- `G` is exactly `center SL(2,F)`, hence cyclic (`IsCyclic_Z`).
    subst hG_ne
    left
    rw [SpecialSubgroups.center_SL2_eq_Z]
    exact SpecialSubgroups.IsCyclic_Z
  · obtain ⟨d⟩ := NumericClassEquation.exists_bridgeData G hp2 center_le_G hG_ne
    -- Destructure `d`'s fields into plain local variables (rather than keeping `d` opaque): this
    -- is what lets `subst` later turn each `case_enumeration` branch's `d.s = _`/`d.t = _` fact
    -- into a genuine retyping of `gs`/`gt`/`As`/`At` etc. along `Fin d.s`/`Fin d.t`, avoiding a
    -- manual `Fin.cast`/`HEq` juggling exercise for the "Fin-shape alignment".
    obtain ⟨g, q, k, s, t, gs, gt, As, At, hAs_mem, hAt_mem, hAs_card, hAt_card, hAs_relIndex,
      hAt_relIndex, hAs_cyclic, hAt_cyclic, hAs_coprime, hAt_coprime, hg, hSylow, hg_pos, hq_pos,
      hk_pos, hgs_ge, hgt_ge, heq, hComplete, hAs_distinct, hAt_distinct⟩ := d
    -- `p ∤ Nat.card G` throughout (that is exactly this theorem's hypothesis `hp'`, `p` prime so
    -- `p ≠ 0`): every Sylow `p`-subgroup of `G` is therefore trivial, forcing `q = k = 1` via
    -- `hSylow` (its "genuine Sylow-type witness" disjunct would otherwise exhibit a *nontrivial*
    -- Sylow `p`-subgroup, contradicting triviality).
    have hp_ne0 : p ≠ 0 := hp.nat_prime.pos.ne'
    have hcop : Nat.Coprime (Nat.card G) p := hp'.resolve_left hp_ne0
    have hpndvd : ¬ p ∣ Nat.card G := hp.nat_prime.coprime_iff_not_dvd.mp hcop.symm
    have hqk1 : q = 1 ∧ k = 1 := by
      rcases hSylow with h | ⟨Q0, K0, S0, -, hQ0eqS0, hQ0ne, -, -, -, -, -, -⟩
      · exact h
      · exfalso
        have hme : Nat.card S0.toSubgroup = p ^ (Nat.card G).factorization p :=
          Sylow.card_eq_multiplicity S0
        rw [Nat.factorization_eq_zero_of_not_dvd hpndvd, pow_zero] at hme
        exact hQ0ne (hQ0eqS0.trans (Subgroup.card_eq_one.mp hme))
    obtain ⟨hq1, hk1⟩ := hqk1
    -- A single (arbitrary) Sylow `p`-subgroup `Q` of `G`, needed by every `case_*` lemma; it is
    -- likewise trivial (`Nat.card Q.toSubgroup = 1 = q`), by the same computation.
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow p G))
    have hqQ : Nat.card Q.toSubgroup = q := by
      have hme : Nat.card Q.toSubgroup = p ^ (Nat.card G).factorization p :=
        Sylow.card_eq_multiplicity Q
      rw [Nat.factorization_eq_zero_of_not_dvd hpndvd, pow_zero] at hme
      rw [hme, hq1]
    -- Dispatch on the six `(s,t)` branches of `CaseArithmetic.case_enumeration`.
    rcases case_enumeration g q k hg_pos hq_pos hk_pos gs gt hgs_ge hgt_ge heq with
      hst | hst | hst | hst | hst | hst
    · -- `(s,t) = (1,0)`: `case_I`. `q = 1` throughout, so `case_I`'s `1 < q` Sylow-witness
      -- bundle is vacuous, and (post-hoc) `Q.toSubgroup = ⊥` makes its cyclic complement `K`
      -- all of `G`, giving `IsCyclic G` directly.
      obtain ⟨hs, ht⟩ := hst
      subst hs; subst ht
      have hgs_eq : gs = fun _ : Fin 1 => gs 0 :=
        funext fun i => congrArg gs (Subsingleton.elim i 0)
      have hgt_eq : gt = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
      rw [hgs_eq, hgt_eq] at heq
      have hQK : 1 < q → IsElementaryAbelian p Q.toSubgroup ∧
          ∃ K : Subgroup SL(2,F), K ≤ G ∧ IsCyclic K ∧
            normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G ∧
            Disjoint Q.toSubgroup (K.subgroupOf G) ∧
            Nat.card K = Nat.card (center SL(2,F)) * k := fun h => absurd h (by omega)
      have hkbundle : (1 < k → k = gs 0) := fun h => absurd h (by omega)
      obtain ⟨-, -, -, K, hcompl, hKcyc, -⟩ :=
        case_I G center_le_G Q g q hg hqQ (gs 0) k (As 0) (hAs_mem 0) (hAs_cyclic 0)
          (hAs_coprime 0) (hAs_card 0) hQK ⟨hk_pos, hgs_ge 0, hkbundle, heq⟩
      left
      have hQbot : Q.toSubgroup = ⊥ := Subgroup.card_eq_one.mp (hqQ.trans hq1)
      have hcm := hcompl.card_mul
      rw [hQbot, Subgroup.card_bot, one_mul] at hcm
      have hKtop : K = ⊤ := Subgroup.eq_top_of_card_eq K hcm
      have hKcyc' : IsCyclic (⊤ : Subgroup ↥G) := hKtop ▸ hKcyc
      exact (MulEquiv.isCyclic Subgroup.topEquiv).mp hKcyc'
    · -- `(s,t) = (1,1)`: `case_II`. Its conclusion is already a sub-disjunction of this
      -- theorem's goal.
      obtain ⟨hs, ht⟩ := hst
      subst hs; subst ht
      have hgs_eq : gs = fun _ : Fin 1 => gs 0 :=
        funext fun i => congrArg gs (Subsingleton.elim i 0)
      have hgt_eq : gt = fun _ : Fin 1 => gt 0 :=
        funext fun i => congrArg gt (Subsingleton.elim i 0)
      rw [hgs_eq, hgt_eq] at heq
      have hKbundle : (gt 0 < k → k = gs 0) := fun h => absurd h (by have := hgt_ge 0; omega)
      have hComplete' : ∀ B ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B = As 0) ∨
          (∃ c ∈ G, conj c • B = At 0) ∨ NumericClassEquation.IsSylowType p G B := by
        intro B hB
        rcases hComplete B hB with ⟨i, c, hcG, hc⟩ | ⟨j, c, hcG, hc⟩ | hsyl
        · rw [Subsingleton.elim i 0] at hc; exact Or.inl ⟨c, hcG, hc⟩
        · rw [Subsingleton.elim j 0] at hc; exact Or.inr (Or.inl ⟨c, hcG, hc⟩)
        · exact Or.inr (Or.inr hsyl)
      rcases case_II G center_le_G Q g q hg hqQ (gs 0) (gt 0) k (As 0) (hAs_mem 0) (hAs_cyclic 0)
          (hAs_coprime 0) (hAs_card 0) (hAs_relIndex 0) (At 0) (hAt_mem 0) (hAt_cyclic 0)
          (hAt_coprime 0) (hAt_card 0) (hAt_relIndex 0) hComplete'
          ⟨hk_pos, hgs_ge 0, hgt_ge 0, hKbundle, heq⟩ with hiso | ⟨n, -, hiso⟩
      · exact Or.inr (Or.inr (Or.inl hiso))
      · exact Or.inr (Or.inl ⟨n, hiso⟩)
    · -- `(s,t) = (0,0)`: `case_III`. Its (proved) conclusion, combined with `q = 1`
      -- (`Q.toSubgroup = ⊥`), forces `G = center SL(2,F)` -- contradicting `hG_ne`. So this
      -- branch cannot actually occur within `dicksons_classification_theorem_class_I`'s context.
      obtain ⟨hs, ht⟩ := hst
      subst hs; subst ht
      have hgs_eq : gs = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
      have hgt_eq : gt = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
      rw [hgs_eq, hgt_eq] at heq
      exfalso
      obtain ⟨hmapsup, -⟩ := case_III G center_le_G Q g q hg hqQ ⟨k, hk_pos, le_of_eq hk1, heq⟩
      have hQbot : Q.toSubgroup = ⊥ := Subgroup.card_eq_one.mp (hqQ.trans hq1)
      rw [hQbot, Subgroup.map_bot, bot_sup_eq] at hmapsup
      exact hG_ne hmapsup.symm
    · -- `(s,t) = (0,1)`: `case_IV`. Butler's own arithmetic (`case_0_1`) forces `q ∈ {2,3}`,
      -- contradicting `q = 1`. So (as with Case III) this branch cannot actually occur here --
      -- it is exactly Butler's Class II (`p ∣ |G|`), not Class I.
      obtain ⟨hs, ht⟩ := hst
      subst hs; subst ht
      have hgs_eq : gs = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
      have hgt_eq : gt = fun _ : Fin 1 => gt 0 :=
        funext fun i => congrArg gt (Subsingleton.elim i 0)
      rw [hgs_eq, hgt_eq] at heq
      exfalso
      have h2card : 2 * Nat.card (At 0) ≤ Nat.card G :=
        two_card_le_of_relIndex_normalizer_eq_two G (At 0) (hAt_mem 0).right (hAt_relIndex 0)
      rw [hAt_card 0, hg] at h2card
      have he : 0 < Nat.card (center SL(2,F)) := Nat.card_pos
      have hg_ge : 2 * (gt 0) ≤ g := by
        have hrw : 2 * (Nat.card (center SL(2,F)) * gt 0)
            = Nat.card (center SL(2,F)) * (2 * gt 0) := by ring
        rw [hrw] at h2card
        exact le_of_mul_le_mul_left h2card he
      obtain ⟨-, hcase⟩ := case_0_1 g q k (gt 0) hg_pos hq_pos hk_pos (hgt_ge 0) hg_ge heq
      rcases hcase with ⟨hq2, -⟩ | ⟨hq3, -, -⟩ <;> omega
    · -- `(s,t) = (0,2)`: `case_V`. Butler's own arithmetic (`case_0_2`) forces `1 < q`,
      -- contradicting `q = 1`; again this branch cannot actually occur here (Butler's Class II).
      obtain ⟨hs, ht⟩ := hst
      subst hs; subst ht
      have hgs_eq : gs = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
      have hgt_eq : gt = ![gt 0, gt 1] := by funext i; fin_cases i <;> simp
      rw [hgs_eq, hgt_eq] at heq
      exfalso
      have he : 0 < Nat.card (center SL(2,F)) := Nat.card_pos
      have h2card0 : 2 * Nat.card (At 0) ≤ Nat.card G :=
        two_card_le_of_relIndex_normalizer_eq_two G (At 0) (hAt_mem 0).right (hAt_relIndex 0)
      have h2card1 : 2 * Nat.card (At 1) ≤ Nat.card G :=
        two_card_le_of_relIndex_normalizer_eq_two G (At 1) (hAt_mem 1).right (hAt_relIndex 1)
      rw [hAt_card 0, hg] at h2card0
      rw [hAt_card 1, hg] at h2card1
      have hg_ge1 : 2 * (gt 0) ≤ g := by
        have hrw : 2 * (Nat.card (center SL(2,F)) * gt 0)
            = Nat.card (center SL(2,F)) * (2 * gt 0) := by ring
        rw [hrw] at h2card0
        exact le_of_mul_le_mul_left h2card0 he
      have hg_ge2 : 2 * (gt 1) ≤ g := by
        have hrw : 2 * (Nat.card (center SL(2,F)) * gt 1)
            = Nat.card (center SL(2,F)) * (2 * gt 1) := by ring
        rw [hrw] at h2card1
        exact le_of_mul_le_mul_left h2card1 he
      obtain ⟨hq_gt1, -⟩ := case_0_2 g q k (gt 0) (gt 1) hg_pos hq_pos hk_pos (hgt_ge 0) (hgt_ge 1)
        hg_ge1 hg_ge2 heq
      omega
    · -- `(s,t) = (0,3)`: `case_VI`. `q = 1` is consistent with Butler's own `case_0_3` here (it
      -- is *his* Class I/VI branch too), so this genuinely dispatches to `case_VI` -- whose own
      -- residual `sorry` (the `g₁ = 2` `WLOG` split, tex ~2145-2156) is therefore inherited here.
      obtain ⟨hs, ht⟩ := hst
      subst hs; subst ht
      have hgs_eq : gs = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
      have hgt_eq : gt = ![gt 0, gt 1, gt 2] := by funext i; fin_cases i <;> simp
      rw [hgs_eq, hgt_eq] at heq
      have hKbundle : (1 < k → k = gt 0 ∨ k = gt 1 ∨ k = gt 2) := fun h => absurd h (by omega)
      rcases case_VI G center_le_G Q g q hg hqQ (gt 0) (gt 1) (gt 2) k
          (At 0) (hAt_mem 0) (hAt_cyclic 0) (hAt_coprime 0) (hAt_card 0) (hAt_relIndex 0)
          (At 1) (hAt_mem 1) (hAt_cyclic 1) (hAt_coprime 1) (hAt_card 1) (hAt_relIndex 1)
          (At 2) (hAt_mem 2) (hAt_cyclic 2) (hAt_coprime 2) (hAt_card 2) (hAt_relIndex 2)
          hk_pos ⟨hgt_ge 0, hgt_ge 1, hgt_ge 2, hKbundle, heq⟩ with ⟨n, -, hiso⟩ | hiso | ⟨-, hiso⟩
      · exact Or.inr (Or.inl ⟨n, hiso⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr hiso)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hiso)))
-- ANCHOR_END: dicksons_classification_theorem_class_I

-- Ŝ₄ is the binary octahedral group `BinaryOctahedralGroup` (*not* `GL(2,3)`); see the module
-- note above `BinaryOctahedralGroup` and `DIVERGENCES.md` item 3.

lemma card_GaloisField_dvd_card_GaloisField (p : ℕ) [Fact (Nat.Prime p)] {m n : ℕ+}
  (m_dvd_n : m ∣ n) :  Nat.card (GaloisField p m.val) ∣ Nat.card (GaloisField p n.val) := by
  rw [GaloisField.card p m m.ne_zero, GaloisField.card p n n.ne_zero]
  apply pow_dvd_pow
  suffices m.val ∣ n.val by exact Nat.le_of_dvd n.prop this
  exact PNat.dvd_iff.mp m_dvd_n

/-- **Theorem 3.6, Class II** (tex 2227-2254, "Class II: when `|G|` is divisible by `p`"). Every
finite subgroup `G ≤ SL(2,F)` of order divisible by `p` is isomorphic to one of: a group with an
elementary abelian normal Sylow `p`-subgroup `Q` and cyclic quotient `G ⧸ Q` of order coprime to
`p` (tex (vi), rendered via a complement `K` to `Q` as in `case_I`); `p = 2` and `G` a dihedral
group of order `2n`, `n` odd (tex (vii)); `p = 3` and `G ≅ SL(2,5)` (tex (viii)); `G ≅ SL(2,𝔽_q)`
for `q = p^k` (tex (ix)); or `G ≅ ⟨SL(2,𝔽_q), d_π⟩` for `q = p^k`, `π ∈ 𝔽_{q²} \ 𝔽_q` with
`π² ∈ 𝔽_q` (tex (x), reusing the `SL2_join_d` construction from `case_V`).
Note: the original statement here had `Isomorphic G Q` for item (vi) (`G` isomorphic to its own
*Sylow subgroup*, rather than `G ⧸ Q` being cyclic of order coprime to `p`) and a garbled,
unrelated existential for item (x); both are corrected here.
Status: statement faithful to paper; proof pending (same dependencies as
`dicksons_classification_theorem_class_I`). -/
-- ANCHOR: dicksons_classification_theorem_class_II
theorem dicksons_classification_theorem_class_II {F : Type*} [Field F] [IsAlgClosed F] {p : ℕ}
    [Fact (Nat.Prime p)] [CharP F p] (G : Subgroup (SL(2,F))) [Finite G] (hp : p ∣ Nat.card G) :
    (∃ Q : Subgroup G, IsElementaryAbelian p Q ∧ Normal Q ∧
        ∃ K : Subgroup G, IsComplement' Q K ∧ IsCyclic K ∧ Nat.Coprime p (Nat.card K)) ∨
      (p = 2 ∧ ∃ n : ℕ, Odd n ∧ Isomorphic G (DihedralGroup n)) ∨
      (p = 3 ∧ Isomorphic G SL(2, ZMod 5)) ∨
      (∃ k : ℕ+, Isomorphic G SL(2, GaloisField p k.val)) ∨
      (∃ k : ℕ+, ∃ π : (GaloisField p (2 * k.val))ˣ, Isomorphic G (SL2_join_d p k π))
  := by sorry
-- ANCHOR_END: dicksons_classification_theorem_class_II



variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

open Matrix LinearMap Subgroup

open scoped MatrixGroups


/-- A projective general linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveGeneralLinearGroup' : Type _ :=
    GL n R ⧸ center (GL n R)



/-- The PGL₂ classification (README, "If `H` is a finite subgroup of `PGL_2(F̄_p)` ..."; this is
Dickson's theorem for `PGL(2,F)`, obtained from `dicksons_classification_theorem_class_I/II` for
`SL(2,F)` by passing to the quotient by the center). Every finite subgroup of
`PGL(Fin 2, 𝔽_p-bar)` is cyclic, dihedral of some order `2n`, isomorphic to `A₄`, `S₄` or `A₅`, or
(conjugate to) `PSL(2,𝕂)`/`PGL(2,𝕂)` for some finite field `𝕂` of characteristic `p`.
Note: the original statement had (a) each disjunct after the first wrapped under a single
`∃ n, _ ∨ _ ∨ ⋯` -- logically harmless since `ℕ` is inhabited, but misleadingly scoped as if `n`
ranged over the whole tail of the disjunction rather than just the dihedral case -- and (b)
`Equiv.Perm (Fin 5)` (i.e. `S₅`, order `120`) in place of `Equiv.Perm (Fin 4)` (`S₄`, order `24`):
`S₅` is not one of Dickson's exceptional subgroups of `PGL₂`, only `A₄, S₄, A₅` are (see README);
both are fixed here so that every disjunct is self-contained.
Status: statement faithful to the README/Butler; proof pending (needs
`dicksons_classification_theorem_class_I/II` pushed down along `SL(2,F) → PGL(2,F)`). -/
-- ANCHOR: FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod
theorem FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod {p : ℕ}
    [Fact (Nat.Prime p)] (𝕂 : Type*) [Field 𝕂] [CharP 𝕂 p] [Finite 𝕂]
    (G : Subgroup (PGL (Fin 2) (AlgebraicClosure (ZMod p)))) [hG : Finite G] :
    IsCyclic G ∨
      (∃ n, Isomorphic G (DihedralGroup n)) ∨
      Isomorphic G (alternatingGroup (Fin 4)) ∨
      Isomorphic G (Equiv.Perm (Fin 4)) ∨
      Isomorphic G (alternatingGroup (Fin 5)) ∨
      Isomorphic G (PSL (Fin 2) (𝕂)) ∨
      Isomorphic G (PGL (Fin 2) (𝕂)) := by
    sorry
-- ANCHOR_END: FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod

#min_imports
