import ClassificationOfSubgroups.Ch4_PGLIsoPSLOverAlgClosedField.ProjectiveGeneralLinearGroup
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_A_MaximalAbelianSubgroup
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_B_MaximalAbelianSubgroup
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S4_CaseArithmetic
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S5_NumericClassEquation
import ClassificationOfSubgroups.Ch7_GroupRecognition
import ClassificationOfSubgroups.Ch7_SimpleGroup60
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
was the same *category* of gap as the one in `case_VI_core`'s `gb = gc = 3` branch below
(tex ~2149-2157, "Sylow-conjugacy elimination... genuinely group-theoretic"), itself since
closed via `caseVI_conj_of_card_six`. -/
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
`y² = 1` directly. Case IVb (`q = 3`, `p = 3`) is now **fully PROVED**, transplanted from
`case_II`'s (fully proved) `g1 = 3` branch (tex ~1785 itself just says "analogous to Case IIb ...
I will leave it to the reader to verify") -- see `DIVERGENCES.md` item 10 for the full account of
that argument. The numerals (`p = 3`, `e = 2`) and the `Q₈`-shaped generator pair `x0, y0` on `A`
are proved directly (reusing the `exists_Q8_generators_of_relIndex_two` extraction above
`case_II`), exactly as before. The residual gap `case_II` closes with an order-`3` element `r0`
drawn from its second maximal-abelian class `A₁` is closed here too, *without* an `A₁`-family
(`s = 0` in this branch, so `hComplete`'s dispatch is only `2`-way, unlike `case_II`'s `3`-way):
`r0` is instead drawn directly from the Sylow `3`-subgroup `Q` (`Nat.card Q.toSubgroup = q = 3` is
prime, so `Q.toSubgroup` is cyclic; a generator, transported down to `↥G` and then `SL(2,F)`, gives
`r0` with membership in `G` automatic from its type) -- otherwise the argument (`N := N_G(A)` shown
normal via the `hComplete`-driven "only-`A`-class" element count on its Sylow-`2` normalizer;
`r0 x0 r0⁻¹` pinned down to one of the `2` remaining conjugates of `A` inside `N` via the "third
conjugate" counting argument; finite case split on `r0` vs `r0²`) runs identically to `case_II`.
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
    -- The gap documented above (Butler tex ~1785, "analogous to Case IIb") is closed exactly as
    -- in `case_II`'s `g1 = 3` branch, using `hComplete` (Theorem 6.8's numeric class equation --
    -- here only a `2`-way disjunct, since there is no `A₁`-family in this branch, `s = 0`):
    -- `N := N_G(A)` is shown to be the *unique* Sylow `2`-subgroup of `G` (via a global
    -- element-order count, `hComplete`-driven), hence normal; an order-`3` element `r0`, drawn
    -- directly from the Sylow `3`-subgroup `Q` (in place of `case_II`'s `A₁`, which does not exist
    -- here), acts on it by conjugation, and since `zpowers y1` (`y1 := r0 x0 r0⁻¹`) is forced --
    -- by the SAME `hComplete`-driven "only the `A`-class" argument, now applied to the *third*
    -- conjugate `zpowers (x0 y1)` -- to coincide with one of the two remaining conjugates of `A`
    -- inside `N`, the exact relations Butler needs are pinned down (up to replacing `r0` by `r0²`
    -- in the second of his two cases).
    classical
    have hA_card4 : Nat.card A = 4 := by rw [hA_card', hg1eq2]
    -- **Step 1**: `N := N_G(A)` has cardinality `8`, hence `[G : N] = 3`.
    set A' : Subgroup ↥G := A.subgroupOf G with hA'_def
    set N : Subgroup ↥G := normalizer (A' : Set ↥G) with hN_def
    have hA'_le_N : A' ≤ N := Subgroup.le_normalizer
    have hcard_N : Nat.card N = 8 := by
      have h1 : Nat.card N = Nat.card (↥N ⧸ A'.subgroupOf N) * Nat.card (A'.subgroupOf N) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
      have h2 : Nat.card (A'.subgroupOf N) = Nat.card A' :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'_le_N).toEquiv
      have h3 : Nat.card (↥N ⧸ A'.subgroupOf N) = A'.relIndex N := rfl
      have hA'_card : Nat.card A' = Nat.card A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_mem.right).toEquiv
      rw [h2, h3, hA_relIndex, hA'_card, hA_card4] at h1
      omega
    have hindexN : Nat.card N * N.index = Nat.card ↥G := Subgroup.card_mul_index N
    have hindex3 : N.index = 3 := by rw [hcard_N] at hindexN; omega
    -- **Step 2**: an order-`3` element `r0 : SL(2,F)`, drawn directly from the Sylow `3`-subgroup
    -- `Q` (there is no `A₁`-family in this branch, `s = 0`, unlike `case_II`'s `g1 = 3` branch,
    -- which sources its analogous `r0` from `A₁`'s cyclic subgroup of order `6`). Since
    -- `Nat.card Q.toSubgroup = q = 3` is prime, `Q.toSubgroup` is cyclic; a generator, transported
    -- down to `↥G` and then `SL(2,F)`, gives `r0` (membership in `G` is automatic from its type).
    have hQcard3 : Nat.card Q.toSubgroup = 3 := by rw [hq, hq3]
    haveI hQcyc : IsCyclic Q.toSubgroup := isCyclic_of_prime_card hQcard3
    obtain ⟨q0, hq0_gen⟩ := hQcyc.exists_generator
    have horder_q0 : orderOf q0 = 3 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hq0_gen, hQcard3]
    set r0G : ↥G := (q0 : ↥G) with hr0G_def
    have hr0G_ord : orderOf r0G = 3 := by
      rw [hr0G_def]
      exact (orderOf_injective Q.toSubgroup.subtype
        (Subgroup.subtype_injective Q.toSubgroup) q0).trans horder_q0
    set r0 : SL(2,F) := (r0G : SL(2,F)) with hr0_def
    have hr0_mem_G : r0 ∈ G := r0G.2
    have hr0_ord : orderOf r0 = 3 := by
      rw [hr0_def]
      exact (orderOf_injective G.subtype (Subgroup.subtype_injective G) r0G).trans hr0G_ord
    have hr0_ne_one : r0 ≠ 1 := by
      intro h
      rw [orderOf_eq_one_iff.mpr h] at hr0_ord
      omega
    have hr0_cube : r0 ^ 3 = 1 := by
      rw [← hr0_ord]; exact pow_orderOf_eq_one r0
    have hr0G_cube : r0G ^ 3 = 1 := by
      rw [← hr0G_ord]; exact pow_orderOf_eq_one r0G
    -- **Step 3**: `A' = ⟨x₀⟩` (as subgroups of `↥G`).
    have hA'_card : Nat.card A' = 4 := by
      rw [hA'_def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_mem.right).toEquiv, hA_card4]
    have hx0_mem_A' : x0 ∈ A' := by rw [hA'_def, Subgroup.mem_subgroupOf]; exact hx0_mem_A
    have hzx0_le_A' : Subgroup.zpowers x0 ≤ A' := by
      rw [Subgroup.zpowers_le]; exact hx0_mem_A'
    have hcard_zx0 : Nat.card (Subgroup.zpowers x0) = 4 := by
      rw [← hx0_ord4]; exact (Nat.card_zpowers x0)
    have hA'_eq_zpowers_x0 : A' = Subgroup.zpowers x0 := by
      apply SetLike.coe_injective
      symm
      exact Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.mpr hzx0_le_A')
        (by show Nat.card A' ≤ Nat.card (Subgroup.zpowers x0); rw [hA'_card, hcard_zx0])
    -- **Step 4**: `r0G` does not centralize `x0` (else it would lie in `A'` by maximality,
    -- contradicting `orderOf r0G = 3 ∤ 4 = Nat.card A'`).
    haveI hA'comm : IsMulCommutative A' := hA_mem.left.1
    have hnc : ¬ Commute r0G x0 := by
      intro hcomm
      have hcomm_all : ∀ a ∈ A', Commute r0G a := by
        intro a ha
        rw [hA'_eq_zpowers_x0, Subgroup.mem_zpowers_iff] at ha
        obtain ⟨n, hn⟩ := ha
        rw [← hn]
        exact hcomm.zpow_right n
      set K : Set ↥G := (A' : Set ↥G) ∪ {r0G} with hK_def
      have hcomm_K : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
        rintro a (ha | ha) b (hb | hb)
        · exact setLike_mul_comm ha hb
        · simp only [Set.mem_singleton_iff] at hb; subst hb
          exact (hcomm_all a ha).symm
        · simp only [Set.mem_singleton_iff] at ha; subst ha
          exact hcomm_all b hb
        · simp only [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; rfl
      haveI hKcomm : IsMulCommutative (Subgroup.closure K) := Subgroup.isMulCommutative_closure hcomm_K
      have hA'_le_closure : A' ≤ Subgroup.closure K := by
        rw [← Subgroup.closure_eq A']; exact Subgroup.closure_mono Set.subset_union_left
      have hclosure_le : Subgroup.closure K ≤ A' := hA_mem.left.2 hKcomm hA'_le_closure
      have hr0G_mem_closure : r0G ∈ Subgroup.closure K := subset_closure (Set.mem_union_right _ rfl)
      have hr0G_mem_A' : r0G ∈ A' := hclosure_le hr0G_mem_closure
      have hdvd : orderOf r0G ∣ Nat.card A' := by
        have h1 := orderOf_dvd_natCard (⟨r0G, hr0G_mem_A'⟩ : A')
        have h2 : orderOf (⟨r0G, hr0G_mem_A'⟩ : A') = orderOf r0G :=
          (orderOf_injective A'.subtype (Subgroup.subtype_injective A') ⟨r0G, hr0G_mem_A'⟩).symm
        rwa [h2] at h1
      rw [hA'_card] at hdvd
      have hr0G_ord : orderOf r0G = 3 := by
        have h := orderOf_injective G.subtype (Subgroup.subtype_injective G) r0G
        rw [← h, hr0G_def]; exact hr0_ord
      rw [hr0G_ord] at hdvd
      norm_num at hdvd
    -- **Step 5**: work at the `SL(2,F)` level. `A = zpowers x0SL`, `x0SL² = -1` (the unique
    -- involution), and `y1 := r0 * x0SL * r0⁻¹` satisfies the `Q₈` relations relative to `x0SL`.
    haveI hAfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hA_card4]; norm_num)
    set x0SL : SL(2,F) := (x0 : SL(2,F)) with hx0SL_def
    have hx0SL_ord4 : orderOf x0SL = 4 := by rw [hx0SL_def, orderOf_coe]; exact hx0_ord4
    have hzx0SL_le_A : Subgroup.zpowers x0SL ≤ A := by
      rw [Subgroup.zpowers_le]; exact hx0_mem_A
    have hcard_zx0SL : Nat.card (Subgroup.zpowers x0SL) = 4 := by
      rw [← hx0SL_ord4]; exact Nat.card_zpowers x0SL
    have hA_eq_zpowers_x0SL : A = Subgroup.zpowers x0SL := by
      apply SetLike.coe_injective
      symm
      exact Set.eq_of_subset_of_ncard_le (SetLike.coe_subset_coe.mpr hzx0SL_le_A)
        (by show Nat.card A ≤ Nat.card (Subgroup.zpowers x0SL); rw [hA_card4, hcard_zx0SL])
        (Set.toFinite (A : Set SL(2,F)))
    -- (`hF2 : NeZero (2 : F)` is already in scope from `case_IV`'s Case IVb setup above, unlike
    -- `case_II`'s analogous point here which has to derive it from `hp_ne_two` via `CharP`.)
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
    -- **Step 6**: `B0 := conj r0 • A` is maximal abelian, equal to `zpowers y1`, and `≠ A`.
    set B0 : Subgroup SL(2,F) := conj r0 • A with hB0_def
    have hB0_eq : B0 = Subgroup.zpowers y1 := by
      rw [hB0_def, hA_eq_zpowers_x0SL, conj_zpowers_eq, ← hy1_def]
    have hB0_mem : B0 ∈ MaximalAbelianSubgroupsOf G :=
      conj_smul_mem_MaximalAbelianSubgroupsOf_of_mem hA_mem hr0_mem_G
    have hB0_ne_A : B0 ≠ A := by
      intro hcontra
      have hy1_mem : y1 ∈ A := by
        rw [← hcontra, hB0_eq]
        exact Subgroup.mem_zpowers y1
      rw [hA_eq_zpowers_x0SL] at hy1_mem
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
    -- (its Sylow `3`-part `Q` -- `p` is already known to be `3` in this branch, unlike `case_II`'s
    -- analogous fact which has to derive `p = 3` from `p ∣ Nat.card G = 24 ∧ p ≠ 2` first -- has
    -- `Nat.card Q` a power of `3` dividing `24`, forcing the power to be exactly `3^1`; `Q` is
    -- disjoint from the order-`2` center, so `Nat.card (Q ⊔ Z F) = 3 * 2 = 6`, not divisible
    -- by `4`).
    have hNoSylowDiv4 : ∀ B : Subgroup SL(2,F), IsSylowType 3 G B → ¬ (4 : ℕ) ∣ Nat.card B := by
      intro B hsyl h4dvd
      obtain ⟨Qp, hQnontriv, hQfin, hQ_le, hB_eq, hQelem, S, hQS⟩ := hsyl
      haveI := hQfin
      have hQ_bot_lt : (⊥ : Subgroup SL(2,F)) < Qp :=
        bot_lt_iff_ne_bot.mpr ((Subgroup.nontrivial_iff_ne_bot Qp).mp hQnontriv)
      have hQ_isPGroup : IsPGroup 3 Qp :=
        IsElementaryAbelian.IsPGroup 3 (Fact.out : Nat.Prime 3) Qp hQelem hQ_bot_lt
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
    have hB0_conj_A : ∃ c ∈ G, conj c • B0 = A := by
      rcases hComplete B0 hB0_mem with ⟨c, hcG, hc⟩ | hsyl
      · exact ⟨c, hcG, hc⟩
      · exact absurd (hcard_B0 ▸ (by norm_num : (4:ℕ) ∣ 4)) (hNoSylowDiv4 B0 hsyl)
    -- **Step 8**: the same argument, applied via `centralizer {z} ⊓ G`, shows that *any* order-`4`
    -- element `z ∈ G` generates a cyclic subgroup `G`-conjugate to `A`.
    have key : ∀ z : SL(2,F), z ∈ G → orderOf z = 4 → ∃ c ∈ G, conj c • Subgroup.zpowers z = A := by
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
      rcases hComplete Cz hCz_mem with ⟨c, hcG, hc⟩ | hsyl
      · refine ⟨c, hcG, ?_⟩
        have hthis : Nat.card (conj c • Cz : Subgroup SL(2,F)) = Nat.card Cz :=
          card_conj_smul_eq_card c
        rw [hc, hA_card4] at hthis
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
    -- lies in the `zpowers` of another, i.e. `A = zpowers x0SL`, `zpowers y0SL`, `zpowers z0SL`
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
    have hyx0SL : y0SL ∉ A := by
      rw [hA_eq_zpowers_x0SL]
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
        have := SpecialSubgroups.orderOf_neg_one_eq_two (F := F)
        rw [h, orderOf_one] at this
        norm_num at this
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
      rw [hA_eq_zpowers_x0SL, Subgroup.mem_zpowers_iff]
      refine ⟨-1, ?_⟩
      have hxz : x0SL⁻¹ * z0SL = y0SL := by rw [hz0SL_def]; group
      rw [← hxz, h, mul_one, _root_.zpow_neg_one]
    have hz0SL_ord4 : orderOf z0SL = 4 := by
      have hne1 : z0SL ^ 2 ≠ 1 := by
        rw [hz0SL_sq]
        intro h
        have := SpecialSubgroups.orderOf_neg_one_eq_two (F := F)
        rw [h, orderOf_one] at this
        norm_num at this
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
    -- distinct cyclic subgroups (`A`, `zpowers y0SL`, `zpowers z0SL`).
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
    have hA_ne_zy : A ≠ Subgroup.zpowers y0SL := by
      intro h
      apply hyx0SL
      rw [h]; exact Subgroup.mem_zpowers y0SL
    have hA_ne_zz : A ≠ Subgroup.zpowers z0SL := by
      intro h
      have : z0SL ∈ A := by rw [h]; exact Subgroup.mem_zpowers z0SL
      rw [hA_eq_zpowers_x0SL] at this
      exact general_ninv x0SL z0SL hxinvz hz0SL_ord4 this
    have hzy_ne_zz : Subgroup.zpowers y0SL ≠ Subgroup.zpowers z0SL := by
      intro h
      have : z0SL ∈ Subgroup.zpowers y0SL := by rw [h]; exact Subgroup.mem_zpowers z0SL
      exact general_ninv y0SL z0SL hyinvz hz0SL_ord4 this
    -- **Step 11**: `zpowers y0SL` and `zpowers z0SL` are also `G`-conjugates of `A` (via `key`),
    -- hence -- together with `A` itself and `B0` -- (at least) `4` elements of the `3`-element
    -- set `ConjClassOf G A`, forcing `B0` to coincide with one of `zpowers y0SL`, `zpowers z0SL`.
    have hy0SL_mem_G : y0SL ∈ G := y0.2
    have hz0SL_mem_G : z0SL ∈ G := by
      rw [hz0SL_def]; exact Subgroup.mul_mem G x0.2 hy0SL_mem_G
    obtain ⟨cy, hcyG, hcy⟩ := key y0SL hy0SL_mem_G hy0SL_ord4
    obtain ⟨cz, hczG, hcz⟩ := key z0SL hz0SL_mem_G hz0SL_ord4
    have hCC_card : Nat.card (ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G)) = 3 := by
      rw [card_ConjClassOf_eq_index_normalizer]
      exact hindex3
    have hA_mem_CC : A ∈ ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G) :=
      ⟨1, G.one_mem, by simp⟩
    have hzy_mem_CC : Subgroup.zpowers y0SL ∈
        ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      rw [smul_eq_iff_eq_inv_smul, ← map_inv] at hcy
      exact ⟨cy⁻¹, G.inv_mem hcyG, hcy.symm⟩
    have hzz_mem_CC : Subgroup.zpowers z0SL ∈
        ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      rw [smul_eq_iff_eq_inv_smul, ← map_inv] at hcz
      exact ⟨cz⁻¹, G.inv_mem hczG, hcz.symm⟩
    have hB0_mem_CC : B0 ∈ ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G) :=
      ⟨r0, hr0_mem_G, rfl⟩
    haveI hCCfin : Finite (ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G)) :=
      Nat.finite_of_card_ne_zero (by rw [hCC_card]; norm_num)
    -- Since `{A, zpowers y0SL, zpowers z0SL}` is a `3`-element subset of the `3`-element set
    -- `ConjClassOf G A`, they are equal: `ConjClassOf G A` has *exactly* these `3` members.
    have hCC_eq : ({A, Subgroup.zpowers y0SL, Subgroup.zpowers z0SL} : Set (Subgroup SL(2,F)))
        = ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      apply Set.eq_of_subset_of_ncard_le
      · intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact hA_mem_CC
        · exact hzy_mem_CC
        · exact hzz_mem_CC
      · have e1 : ({Subgroup.zpowers y0SL, Subgroup.zpowers z0SL} :
            Set (Subgroup SL(2,F))).ncard = 2 := Set.ncard_pair hzy_ne_zz
        have e2 : ({A, Subgroup.zpowers y0SL, Subgroup.zpowers z0SL} :
            Set (Subgroup SL(2,F))).ncard = 3 := by
          rw [Set.ncard_insert_of_notMem (by simp [hA_ne_zy, hA_ne_zz]), e1]
        have hcceq : (ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G)).ncard
            = Nat.card (ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G)) := rfl
        rw [e2, hcceq, hCC_card]
      · exact Set.toFinite _
    have hB0_cases : B0 = A ∨ B0 = Subgroup.zpowers y0SL ∨ B0 = Subgroup.zpowers z0SL := by
      have := hCC_eq ▸ hB0_mem_CC
      simpa using this
    have hB0_cases' : B0 = Subgroup.zpowers y0SL ∨ B0 = Subgroup.zpowers z0SL :=
      hB0_cases.resolve_left hB0_ne_A
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
        have := SpecialSubgroups.orderOf_neg_one_eq_two (F := F)
        rw [h, orderOf_one] at this
        norm_num at this
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
    -- **Step 15**: `z1` is `∉ A` and `∉ zpowers y1` (so `A, zpowers y1, zpowers z1` are pairwise
    -- distinct), and (via `key`) `zpowers z1` is a `G`-conjugate of `A`.
    have hz1_notin_A : z1 ∉ A := by
      rw [hA_eq_zpowers_x0SL]; exact general_ninv x0SL z1 hxinvz1 hz1_ord4
    have hz1_notin_zy1 : z1 ∉ Subgroup.zpowers y1 := general_ninv y1 z1 hyinvz1 hz1_ord4
    have hzy1_ne_zz1 : Subgroup.zpowers y1 ≠ Subgroup.zpowers z1 := by
      intro h; exact hz1_notin_zy1 (h ▸ Subgroup.mem_zpowers z1)
    have hA_ne_zz1 : A ≠ Subgroup.zpowers z1 := by
      intro h; exact hz1_notin_A (h ▸ Subgroup.mem_zpowers z1)
    have hy1_mem_G : y1 ∈ G := by
      rw [hy1_def]; exact Subgroup.mul_mem G (Subgroup.mul_mem G hr0_mem_G x0.2) (G.inv_mem hr0_mem_G)
    have hz1_mem_G : z1 ∈ G := by rw [hz1_def]; exact Subgroup.mul_mem G x0.2 hy1_mem_G
    obtain ⟨cz1, hcz1G, hcz1⟩ := key z1 hz1_mem_G hz1_ord4
    have hzz1_mem_CC : Subgroup.zpowers z1 ∈
        ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      rw [smul_eq_iff_eq_inv_smul, ← map_inv] at hcz1
      exact ⟨cz1⁻¹, G.inv_mem hcz1G, hcz1.symm⟩
    -- **Step 16**: `φ(y1) := r0 * y1 * r0⁻¹` has order `4`, is `≠ A`-generator, `≠ y1`-generator
    -- (via the `r0³ = 1` / non-centralizing arguments), hence -- since `ConjClassOf` has only the
    -- `3` elements `A, zpowers y1 ∈ {zpowers y0SL, zpowers z0SL}, ` and both `zpowers z1` and
    -- `zpowers (φ y1)` avoid `A` and `zpowers y1` while lying in `ConjClassOf` -- they coincide.
    set phi_y1 : SL(2,F) := r0 * y1 * r0⁻¹ with hphiy1_def
    have hphiy1_ord4 : orderOf phi_y1 = 4 := by rw [hphiy1_def, orderOf_conj]; exact hy1_ord4
    have hphiy1_mem_G : phi_y1 ∈ G := by
      rw [hphiy1_def]
      exact Subgroup.mul_mem G (Subgroup.mul_mem G hr0_mem_G hy1_mem_G) (G.inv_mem hr0_mem_G)
    have hh : r0 * phi_y1 * r0⁻¹ = x0SL := by
      have h0 := hiterate3 x0SL
      rw [← hy1_def, ← hphiy1_def] at h0
      exact h0
    have hphiy1_ne_A : Subgroup.zpowers phi_y1 ≠ A := by
      intro heqA
      have hmemA : phi_y1 ∈ A := heqA ▸ Subgroup.mem_zpowers phi_y1
      rw [hA_eq_zpowers_x0SL] at hmemA
      rcases order4_mem_zpowers x0SL phi_y1 hx0SL_ord4 hphiy1_ord4 hmemA with heq | heq
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
        have hordneg1 := SpecialSubgroups.orderOf_neg_one_eq_two (F := F)
        rw [hy1sq1, orderOf_one] at hordneg1
        norm_num at hordneg1
    -- **Step 17**: `zpowers phi_y1 = zpowers z1` (both are the unique element of
    -- `ConjClassOf G A \ {A, zpowers y1}`).
    have hzy1_ne_A : Subgroup.zpowers y1 ≠ A := hB0_eq ▸ hB0_ne_A
    obtain ⟨cphi, hcphiG, hcphi⟩ := key phi_y1 hphiy1_mem_G hphiy1_ord4
    have hphiy1_mem_CC : Subgroup.zpowers phi_y1 ∈
        ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      rw [smul_eq_iff_eq_inv_smul, ← map_inv] at hcphi
      exact ⟨cphi⁻¹, G.inv_mem hcphiG, hcphi.symm⟩
    have hsub2 : ({A, Subgroup.zpowers y1} : Set (Subgroup SL(2,F)))
        ⊆ ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hA_mem_CC
      · exact hB0_eq ▸ hB0_mem_CC
    have hcard2 : ({A, Subgroup.zpowers y1} : Set (Subgroup SL(2,F))).ncard = 2 :=
      Set.ncard_pair hzy1_ne_A.symm
    have hCCcard_eq : (ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G)).ncard
        = Nat.card (ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G)) := rfl
    have hCC_diff_card : (ConjClassOf G (⟨A, hA_mem⟩ : MaximalAbelianSubgroupsOf G)
        \ ({A, Subgroup.zpowers y1} : Set (Subgroup SL(2,F)))).ncard = 1 := by
      rw [Set.ncard_diff hsub2 (Set.toFinite _), hcard2, hCCcard_eq, hCC_card]
    have hzz1_in_diff : Subgroup.zpowers z1 ∈ ConjClassOf G (⟨A, hA_mem⟩ :
        MaximalAbelianSubgroupsOf G) \ ({A, Subgroup.zpowers y1} : Set (Subgroup SL(2,F))) := by
      refine ⟨hzz1_mem_CC, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨hA_ne_zz1.symm, fun h => hzy1_ne_zz1 h.symm⟩
    have hphiy1_in_diff : Subgroup.zpowers phi_y1 ∈ ConjClassOf G (⟨A, hA_mem⟩ :
        MaximalAbelianSubgroupsOf G) \ ({A, Subgroup.zpowers y1} : Set (Subgroup SL(2,F))) := by
      refine ⟨hphiy1_mem_CC, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      push_neg
      exact ⟨hphiy1_ne_A, hphiy1_ne_y1⟩
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
        apply hz1_notin_A
        rw [hA_eq_zpowers_x0SL]
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

/-- Butler's constraint on the twisting unit `π` of item (x)/Case Vb (tex ~1848-2113, 2213-2254):
`π ∈ 𝔽_{q²} \ 𝔽_q` while `π² ∈ 𝔽_q` (which forces `π²` to be a *nonsquare* of `𝔽_q`: from
`π² = a²` with `a ∈ 𝔽_q` follows `π = ±a ∈ 𝔽_q`). The subfield `𝔽_q ⊆ 𝔽_{q²}` is rendered as
`Set.range (GaloisField_ringHom p k)`. Wave 20 exhibited the
`⟨SL(2,𝔽_q), d_π⟩ ⧸ {±1} ≅ PGL(2,𝔽_q)` identification as FALSE for arbitrary `π` (see
`pgl_descent_SL2_join_d_quotient`), so every statement producing or consuming the `SL2_join_d`
shape now carries this spec. -/
def SL2_join_d_pi_spec (p : ℕ) [Fact (Nat.Prime p)] (k : ℕ+)
    (π : (GaloisField p (2 * k.val))ˣ) : Prop :=
  (π : GaloisField p (2 * k.val)) ∉ Set.range (GaloisField_ringHom p k) ∧
    ((π : GaloisField p (2 * k.val)) ^ 2) ∈ Set.range (GaloisField_ringHom p k)


/-- Butler's class equation for `(s,t) = (0,2)` is symmetric in the two `t`-class numerals. -/
lemma caseV_classEquation_swap (g q k ga gb : ℕ)
    (h : ClassEquation g q k (s := 0) (t := 2) (fun i => i.elim0) ![ga, gb]) :
    ClassEquation g q k (s := 0) (t := 2) (fun i => i.elim0) ![gb, ga] := by
  unfold ClassEquation at h ⊢
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, add_zero] at h ⊢
  linarith

/-- Lagrange for the normalizer of a normalizer-index-`2` class witness. -/
lemma caseV_two_mul_dvd_g_of_relIndex_normalizer_eq_two {F : Type*} [Field F]
    (G A : Subgroup SL(2,F)) [Finite G] (hA_le : A ≤ G) (g gA : ℕ)
    (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hA_card : Nat.card A = Nat.card (center SL(2,F)) * gA)
    (hrelIndex : relIndex (A.subgroupOf G) (normalizer ((A.subgroupOf G) : Set ↥G)) = 2) :
    2 * gA ∣ g := by
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
  rw [hcard_N, hA'_card, hA_card, hg] at hNdvd
  have he : 0 < Nat.card (center SL(2,F)) := Nat.card_pos
  have h1 : Nat.card (center SL(2,F)) * (2 * gA) ∣ Nat.card (center SL(2,F)) * g := by
    have hrw : 2 * (Nat.card (center SL(2,F)) * gA) = Nat.card (center SL(2,F)) * (2 * gA) := by
      ring
    rwa [hrw] at hNdvd
  exact (mul_dvd_mul_iff_left he.ne').mp h1

/-- Lagrange for `N_G(Q) = Q ⋊ K`: `q * k ∣ g`. -/
lemma caseV_q_mul_k_dvd_g {F : Type*} {p : ℕ} [Field F] [Fact (Nat.Prime p)]
    (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G) (g q k : ℕ)
    (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q)
    (K : Subgroup SL(2,F)) (hK_le : K ≤ G)
    (hK_card : Nat.card K = Nat.card (center SL(2,F)) * k)
    (hNQK : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G)
    (hQK_disj : Disjoint Q.toSubgroup (K.subgroupOf G)) :
    q * k ∣ g := by
  set Nz : Subgroup ↥G := normalizer (Q.toSubgroup : Set ↥G) with hNz_def
  have hQ_le_Nz : Q.toSubgroup ≤ Nz := Subgroup.le_normalizer
  have hK_le_Nz : K.subgroupOf G ≤ Nz := by rw [hNQK]; exact le_sup_right
  set Qn : Subgroup ↥Nz := Q.toSubgroup.subgroupOf Nz with hQn_def
  set Kn : Subgroup ↥Nz := (K.subgroupOf G).subgroupOf Nz with hKn_def
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
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_Nz).toEquiv]; exact hq
  have hcard_Kn : Nat.card Kn = Nat.card (center SL(2,F)) * k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_Nz).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le).toEquiv]
    exact hK_card
  have hNz_dvd : Nat.card Nz ∣ Nat.card G := Subgroup.card_subgroup_dvd_card Nz
  rw [← hcard_Nz, hcard_Qn, hcard_Kn, hg] at hNz_dvd
  have he : 0 < Nat.card (center SL(2,F)) := Nat.card_pos
  have h1 : Nat.card (center SL(2,F)) * (q * k) ∣ Nat.card (center SL(2,F)) * g := by
    have hrw : q * (Nat.card (center SL(2,F)) * k)
        = Nat.card (center SL(2,F)) * (q * k) := by ring
    rwa [hrw] at hNz_dvd
  exact (mul_dvd_mul_iff_left he.ne').mp h1

/-- Pure orbit-count helper: if a finite group `H` acts on a finite type `β`, `b₀` is a global
fixed point, and every other point has an orbit of cardinality `m`, then `m ∣ card β - 1`. -/
lemma caseV_dvd_card_sub_one_of_orbit {H : Type*} [Group H] {β : Type*} [MulAction H β]
    [Finite β] {m : ℕ} (b₀ : β) (hb₀ : ∀ h : H, h • b₀ = b₀)
    (horb : ∀ b : β, b ≠ b₀ → Nat.card (MulAction.orbit H b) = m) :
    m ∣ Nat.card β - 1 := by
  classical
  letI : Fintype (MulAction.orbitRel.Quotient H β) := Fintype.ofFinite _
  set Ω := MulAction.orbitRel.Quotient H β with hΩ
  set f : Ω → ℕ := fun ω => Nat.card (MulAction.orbit H ω.out) with hf_def
  have key : Nat.card β = ∑ ω : Ω, f ω := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits H β), Nat.card_sigma]
  have hb₀orbit : Nat.card (MulAction.orbit H b₀) = 1 := by
    have hset : MulAction.orbit H b₀ = {b₀} := by
      ext x
      simp only [MulAction.mem_orbit_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨h, rfl⟩; exact hb₀ h
      · rintro rfl; exact ⟨1, one_smul _ _⟩
    rw [hset, Nat.card_eq_one_iff_unique]
    exact ⟨Set.uniqueSingleton b₀ |>.instSubsingleton, ⟨b₀, rfl⟩⟩
  set ω₀ : Ω := Quotient.mk'' b₀ with hω₀
  have hfω₀ : f ω₀ = 1 := by
    have hmem : ω₀.out ∈ MulAction.orbit H b₀ := by
      have : Quotient.mk'' ω₀.out = (Quotient.mk'' b₀ : Ω) := by rw [Quotient.out_eq']
      rwa [Quotient.eq'', MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at this
    rw [hf_def]
    simp only
    rw [MulAction.orbit_eq_iff.mpr hmem, hb₀orbit]
  have hfne : ∀ ω : Ω, ω ≠ ω₀ → f ω = m := by
    intro ω hω
    have hout : ω.out ≠ b₀ := by
      intro h
      apply hω
      rw [hω₀, ← h, Quotient.out_eq']
    exact horb ω.out hout
  have hsum : ∑ ω : Ω, f ω = 1 + (Finset.univ.erase ω₀).card * m := by
    rw [← Finset.add_sum_erase Finset.univ f (Finset.mem_univ ω₀), hfω₀]
    congr 1
    rw [Finset.sum_congr rfl (fun ω hω => hfne ω (Finset.mem_erase.mp hω).1),
      Finset.sum_const, smul_eq_mul]
  rw [key, hsum]
  simp only [Nat.add_sub_cancel_left]
  exact dvd_mul_left m _

/-- Lagrange for `N_G(Q) = Q ⋊ K`: `|N_G(Q)| = q · (e · k)`. (Complement block of
`caseV_q_mul_k_dvd_g`, isolated for the orbit-count argument of `caseV_k_dvd_q_sub_one`.) -/
lemma caseV_card_normalizer_Q {F : Type*} {p : ℕ} [Field F] [Fact (Nat.Prime p)]
    (G : Subgroup SL(2,F)) [Finite G] (Q : Sylow p G) (q k : ℕ)
    (hq : Nat.card Q.toSubgroup = q)
    (K : Subgroup SL(2,F)) (hK_le : K ≤ G)
    (hK_card : Nat.card K = Nat.card (center SL(2,F)) * k)
    (hNQK : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G)
    (hQK_disj : Disjoint Q.toSubgroup (K.subgroupOf G)) :
    Nat.card ↥(normalizer (Q.toSubgroup : Set ↥G)) = q * (Nat.card (center SL(2,F)) * k) := by
  set Nz : Subgroup ↥G := normalizer (Q.toSubgroup : Set ↥G) with hNz_def
  have hQ_le_Nz : Q.toSubgroup ≤ Nz := Subgroup.le_normalizer
  have hK_le_Nz : K.subgroupOf G ≤ Nz := by rw [hNQK]; exact le_sup_right
  set Qn : Subgroup ↥Nz := Q.toSubgroup.subgroupOf Nz with hQn_def
  set Kn : Subgroup ↥Nz := (K.subgroupOf G).subgroupOf Nz with hKn_def
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
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_Nz).toEquiv]; exact hq
  have hcard_Kn : Nat.card Kn = Nat.card (center SL(2,F)) * k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_Nz).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le).toEquiv]
    exact hK_card
  rw [← hcard_Nz, hcard_Qn, hcard_Kn]

/-- Cardinality of a join of two disjoint subgroups, one of which is normal:
`|H ⊔ K| = |H| · |K|`. (Used for `|Q × Z| = q·e` in `caseV_card_stabilizer_eq`.) -/
lemma caseV_card_sup_disjoint_normal {Γ : Type*} [Group Γ] (H K : Subgroup Γ)
    [Finite ↥(H ⊔ K)] (hK : K.Normal) (hdisj : Disjoint H K) :
    Nat.card ↥(H ⊔ K) = Nat.card ↥H * Nat.card ↥K := by
  have hHle : H ≤ H ⊔ K := le_sup_left
  have hKle : K ≤ H ⊔ K := le_sup_right
  haveI : (K.subgroupOf (H ⊔ K)).Normal := hK.subgroupOf (H ⊔ K)
  have hsup : H.subgroupOf (H ⊔ K) ⊔ K.subgroupOf (H ⊔ K) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hHle hKle, Subgroup.subgroupOf_self]
  have hdisj' : H.subgroupOf (H ⊔ K) ⊓ K.subgroupOf (H ⊔ K) = ⊥ := by
    rw [← subgroupOf_inf_eq, disjoint_iff.mp hdisj, Subgroup.bot_subgroupOf]
  have hcompl : IsComplement' (H.subgroupOf (H ⊔ K)) (K.subgroupOf (H ⊔ K)) := by
    apply isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hdisj')
    have h := Subgroup.mul_normal (H.subgroupOf (H ⊔ K)) (K.subgroupOf (H ⊔ K))
    rw [hsup, Subgroup.coe_top] at h
    exact h.symm
  have hcard := hcompl.card_mul
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKle).toEquiv] at hcard
  exact hcard.symm

/-- Butler Thm 6.8(iii) (tex ~899-1000), the `hstab` ingredient of `caseV_k_dvd_q_sub_one`: the
stabiliser of a noncentral `b ∈ Q` under the conjugation action of `N_G(Q)` is
`C_G(b) ∩ N_G(Q) = Q × Z`, of cardinality `q · e` (`e = |Z(SL(2,F))|`). Proof: conjugate `Q` to
the standard shear group via `exists_conj_Sylow_eq_S_inf_and_normalizer_le_L`, so the image `x` of
`b` is `c (s σ) c⁻¹` (`σ ≠ 0`); the stabiliser is `centralizer {b} ⊓ N_G(Q)`, and using
`centralizer_s_eq_SZ` (`C_{SL₂}(s σ) = SZ`) every element normalising `Q` and centralising `x`
lands in `Q'` or `(-1)·Q'`, giving `centralizer {b} ⊓ N_G(Q) = Q ⊔ Z`; `Q` abelian (`⊆ conj c • S`)
and `Z` central provide the reverse inclusion, and `caseV_card_sup_disjoint_normal` computes the
cardinality (`Q ∩ Z = ⊥` since `-1 ∉ Q` unless `char = 2` collapses `-1 = 1`). -/
lemma caseV_card_stabilizer_eq {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F]
    [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (q : ℕ) (hq : Nat.card Q.toSubgroup = q)
    (b : ↥Q.toSubgroup) (hb : b ≠ 1) :
    Nat.card (MulAction.stabilizer (↥(normalizer (Q.toSubgroup : Set ↥G))) b)
      = q * Nat.card (center SL(2,F)) := by
  classical
  set Nsub : Subgroup ↥G := normalizer (Q.toSubgroup : Set ↥G) with hNsub_def
  set β : ↥G := Q.toSubgroup.subtype b with hβ_def
  set Zc : Subgroup ↥G := (center SL(2,F)).subgroupOf G with hZc_def
  set M : Subgroup ↥G := Q.toSubgroup ⊔ Zc with hM_def
  have hβ_mem : β ∈ Q.toSubgroup := b.2
  have hQne : Q.toSubgroup ≠ ⊥ := by
    have : Nontrivial ↥Q.toSubgroup := nontrivial_of_ne b 1 hb
    exact (Subgroup.nontrivial_iff_ne_bot _).mp this
  obtain ⟨c, hQeq, -⟩ := exists_conj_Sylow_eq_S_inf_and_normalizer_le_L G Q hQne
  have hβ_ne : β ≠ 1 := by
    intro hcontra
    apply hb
    apply Subgroup.subtype_injective Q.toSubgroup
    rw [_root_.map_one, ← hβ_def]; exact hcontra
  have hxβ_conjS : G.subtype β ∈ MulAut.conj c • SpecialSubgroups.S F := by
    have hmem : G.subtype β ∈ map G.subtype Q.toSubgroup := mem_map_of_mem G.subtype hβ_mem
    rw [hQeq] at hmem
    exact hmem.1
  obtain ⟨σ, hσ⟩ := (mem_pointwise_smul_iff_inv_smul_mem).mp hxβ_conjS
  have hx_eq : G.subtype β = c * s σ * c⁻¹ := by
    have h1 : G.subtype β = (MulAut.conj c) • ((MulAut.conj c)⁻¹ • (G.subtype β)) :=
      (smul_inv_smul (MulAut.conj c) _).symm
    rw [← hσ] at h1
    rw [h1, MulAut.smul_def, MulAut.conj_apply]
  have hσ0 : σ ≠ 0 := by
    intro h0
    apply hβ_ne
    apply Subgroup.subtype_injective G
    rw [_root_.map_one, hx_eq, h0, s_zero_eq_one, mul_one, mul_inv_cancel]
  have hQ'_le_S : map G.subtype Q.toSubgroup ≤ MulAut.conj c • SpecialSubgroups.S F := by
    rw [hQeq]; exact inf_le_left
  haveI hScomm : IsMulCommutative (MulAut.conj c • SpecialSubgroups.S F : Subgroup SL(2,F)) := by
    have hrw : (MulAut.conj c • SpecialSubgroups.S F : Subgroup SL(2,F))
        = (SpecialSubgroups.S F).map (MulAut.conj c).toMonoidHom := rfl
    rw [hrw]; infer_instance
  haveI hQ'comm : IsMulCommutative (map G.subtype Q.toSubgroup) :=
    ⟨⟨fun x y => Subtype.ext (setLike_mul_comm (hQ'_le_S x.2) (hQ'_le_S y.2))⟩⟩
  have hQ_subgroupOf_eq : (map G.subtype Q.toSubgroup).subgroupOf G = Q.toSubgroup :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective G) Q.toSubgroup
  haveI hQcomm : IsMulCommutative Q.toSubgroup := by
    rw [← hQ_subgroupOf_eq]; infer_instance
  have hZc_le_center : Zc ≤ Subgroup.center (↥G) := by
    intro g hg
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subgroup.subtype_injective G
    rw [_root_.map_mul, _root_.map_mul]
    have hgc : G.subtype g ∈ center SL(2,F) := Subgroup.mem_subgroupOf.mp hg
    exact Subgroup.mem_center_iff.mp hgc (G.subtype h)
  have hle_easy : M ≤ Subgroup.centralizer {β} ⊓ Nsub := by
    rw [hM_def]
    apply sup_le
    · apply le_inf
      · intro g hg
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact setLike_mul_comm hg hβ_mem
      · exact Subgroup.le_normalizer
    · apply le_inf
      · exact hZc_le_center.trans (Subgroup.center_le_centralizer {β})
      · exact hZc_le_center.trans (Subgroup.center_le_normalizer (Q.toSubgroup : Set ↥G))
  have hM_le_N : M ≤ Nsub := hle_easy.trans inf_le_right
  have hle_hard : Subgroup.centralizer {β} ⊓ Nsub ≤ M := by
    intro g hg
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp hg.1
    have hyx : G.subtype g * G.subtype β = G.subtype β * G.subtype g := by
      rw [← _root_.map_mul, ← _root_.map_mul, hcomm]
    have hm_mem : (c⁻¹ * G.subtype g * c) ∈ Subgroup.centralizer {s σ} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hsσ : s σ = c⁻¹ * G.subtype β * c := by rw [hx_eq]; group
      rw [hsσ]
      have e1 : (c⁻¹ * G.subtype g * c) * (c⁻¹ * G.subtype β * c)
          = c⁻¹ * (G.subtype g * G.subtype β) * c := by group
      have e2 : (c⁻¹ * G.subtype β * c) * (c⁻¹ * G.subtype g * c)
          = c⁻¹ * (G.subtype β * G.subtype g) * c := by group
      rw [e1, e2, hyx]
    rw [centralizer_s_eq_SZ hσ0] at hm_mem
    have hm_set : (c⁻¹ * G.subtype g * c) ∈ ((SpecialSubgroups.SZ F) : Set SL(2,F)) := hm_mem
    simp only [SpecialSubgroups.SZ, coe_set_mk, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      Set.mem_union, Set.mem_setOf_eq] at hm_set
    have hg_in_G : G.subtype g ∈ G := g.2
    rcases hm_set with ⟨τ, hτ⟩ | ⟨τ, hτ⟩
    · have hy_eq : G.subtype g = c * s τ * c⁻¹ := by rw [hτ]; group
      have hy_in : G.subtype g ∈ MulAut.conj c • SpecialSubgroups.S F := by
        rw [hy_eq]
        have hcs : (MulAut.conj c) • (s τ) = c * s τ * c⁻¹ := by
          rw [MulAut.smul_def, MulAut.conj_apply]
        rw [← hcs]
        exact smul_mem_pointwise_smul (s τ) (MulAut.conj c) (SpecialSubgroups.S F) ⟨τ, rfl⟩
      have hy_map : G.subtype g ∈ map G.subtype Q.toSubgroup := by
        rw [hQeq]; exact ⟨hy_in, hg_in_G⟩
      have hgQ : g ∈ Q.toSubgroup :=
        (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective G)).mp hy_map
      rw [hM_def]; exact Subgroup.mem_sup_left hgQ
    · have hy_eq : G.subtype g = c * (-s τ) * c⁻¹ := by rw [hτ]; group
      have hg'_eq : (-1 : SL(2,F)) * G.subtype g = c * s τ * c⁻¹ := by
        rw [hy_eq]
        have h1 : c * (-s τ) * c⁻¹ = -(c * s τ * c⁻¹) := by rw [mul_neg, neg_mul]
        rw [h1, neg_one_mul, neg_neg]
      have hneg1_mem : (-1 : SL(2,F)) ∈ center SL(2,F) := by
        rw [SpecialSubgroups.center_SL2_eq_Z]; exact SpecialSubgroups.neg_one_mem_Z
      set z : ↥G := ⟨(-1 : SL(2,F)), center_le_G hneg1_mem⟩ with hz_def
      have hz_Zc : z ∈ Zc := Subgroup.mem_subgroupOf.mpr hneg1_mem
      have hg'_in : c * s τ * c⁻¹ ∈ MulAut.conj c • SpecialSubgroups.S F := by
        have hcs : (MulAut.conj c) • (s τ) = c * s τ * c⁻¹ := by
          rw [MulAut.smul_def, MulAut.conj_apply]
        rw [← hcs]
        exact smul_mem_pointwise_smul (s τ) (MulAut.conj c) (SpecialSubgroups.S F) ⟨τ, rfl⟩
      have hzg_subtype : G.subtype (z * g) = c * s τ * c⁻¹ := by
        rw [_root_.map_mul]
        show (-1 : SL(2,F)) * G.subtype g = c * s τ * c⁻¹
        exact hg'_eq
      have hg'_G : c * s τ * c⁻¹ ∈ G := by rw [← hzg_subtype]; exact (z * g).2
      have hzg_map : G.subtype (z * g) ∈ map G.subtype Q.toSubgroup := by
        rw [hQeq, hzg_subtype]; exact ⟨hg'_in, hg'_G⟩
      have hzg_Q : z * g ∈ Q.toSubgroup :=
        (Subgroup.mem_map_iff_mem (Subgroup.subtype_injective G)).mp hzg_map
      have hg_eq : g = z⁻¹ * (z * g) := by group
      rw [hM_def, hg_eq]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (inv_mem hz_Zc))
        (Subgroup.mem_sup_left hzg_Q)
  have hkey : Subgroup.centralizer {β} ⊓ Nsub = M := le_antisymm hle_hard hle_easy
  have hstab_eq : MulAction.stabilizer (↥Nsub) b = M.subgroupOf Nsub := by
    ext n
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, ← hkey, Subgroup.mem_inf]
    have smul_val : ((n • b : ↥Q.toSubgroup) : ↥G) = (n : ↥G) * β * (n : ↥G)⁻¹ := rfl
    constructor
    · intro h
      refine ⟨?_, n.2⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hval : (n : ↥G) * β * (n : ↥G)⁻¹ = β := by
        have hc := congrArg Subtype.val h
        rw [smul_val] at hc
        exact hc
      rw [mul_inv_eq_iff_eq_mul] at hval
      exact hval
    · rintro ⟨hc, -⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      have hval : (n : ↥G) * β * (n : ↥G)⁻¹ = β := by rw [hc]; group
      apply Subtype.ext
      rw [smul_val]; exact hval
  rw [hstab_eq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM_le_N).toEquiv, hM_def]
  haveI : Finite ↥(Q.toSubgroup ⊔ Zc) := Subtype.finite
  have hZc_normal : Zc.Normal := by
    rw [hZc_def]; exact Subgroup.Normal.subgroupOf (inferInstance) G
  have hdisj : Disjoint Q.toSubgroup Zc := by
    rw [Subgroup.disjoint_def]
    intro g hgQ hgZ
    have hgc : G.subtype g ∈ center SL(2,F) := Subgroup.mem_subgroupOf.mp hgZ
    rw [SpecialSubgroups.center_SL2_eq_Z, ← SetLike.mem_coe, SpecialSubgroups.set_Z_eq,
      Set.mem_insert_iff, Set.mem_singleton_iff] at hgc
    rcases hgc with h1 | hn1
    · apply Subgroup.subtype_injective G
      rw [_root_.map_one]; exact h1
    · have hgQ' : G.subtype g ∈ map G.subtype Q.toSubgroup := mem_map_of_mem G.subtype hgQ
      rw [hQeq] at hgQ'
      have hin : G.subtype g ∈ MulAut.conj c • SpecialSubgroups.S F := hgQ'.1
      rw [hn1] at hin
      have hin' : (MulAut.conj c)⁻¹ • (-1 : SL(2,F)) ∈ SpecialSubgroups.S F :=
        (mem_pointwise_smul_iff_inv_smul_mem).mp hin
      have hcomp : (MulAut.conj c)⁻¹ • (-1 : SL(2,F)) = -1 := by
        have hci : (MulAut.conj c)⁻¹ = MulAut.conj c⁻¹ := (_root_.map_inv MulAut.conj c).symm
        rw [hci]
        simp only [MulAut.smul_def, MulAut.conj_apply, inv_inv, mul_neg_one, neg_mul,
          inv_mul_cancel]
      rw [hcomp] at hin'
      obtain ⟨ρ, hρ⟩ := hin'
      have hFF : (1 : F) = -1 := by
        have h00 := congrArg (fun A : SL(2,F) => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hρ
        simpa [SpecialMatrices.s] using h00
      have h1F : (1 : F) + 1 = 0 := by nth_rewrite 1 [hFF]; exact neg_add_cancel 1
      have h2z : (2 : F) = 0 := by rw [← one_add_one_eq_two]; exact h1F
      have hcollapse : (1 : SL(2,F)) = -1 :=
        SpecialSubgroups.SpecialLinearGroup.neg_one_eq_one_of_two_eq_zero h2z
      apply Subgroup.subtype_injective G
      rw [_root_.map_one, hn1]; exact hcollapse.symm
  rw [caseV_card_sup_disjoint_normal Q.toSubgroup Zc hZc_normal hdisj, hq]
  congr 1
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe center_le_G).toEquiv

/-- Butler (6.14), tex 1897-1913: `k ∣ q - 1`. `N_G(Q)` acts on `Q` by conjugation (via the
normalizer's `MulDistribMulAction`); `1` is fixed and every noncentral `b ∈ Q` has an orbit of
size `[N_G(Q) : Stab(b)] = k`, so `k ∣ |Q| - 1 = q - 1` (`caseV_dvd_card_sub_one_of_orbit`). The
orbit size is `k` because `|N_G(Q)| = q·e·k` (`caseV_card_normalizer_Q`) and `Stab(b) =
C_G(b) ∩ N_G(Q) = Q × Z` has cardinality `q·e` (`caseV_card_stabilizer_eq`, Butler Thm 6.8(iii),
`C_G(x) = Q × Z` for noncentral unipotent `x`). Fully proven. -/
lemma caseV_k_dvd_q_sub_one {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F]
    [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (q k : ℕ) (hq : Nat.card Q.toSubgroup = q)
    (K : Subgroup SL(2,F)) (hK_le : K ≤ G) (hK_cyc : IsCyclic K)
    (hK_card : Nat.card K = Nat.card (center SL(2,F)) * k)
    (hNQK : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G)
    (hQK_disj : Disjoint Q.toSubgroup (K.subgroupOf G)) :
    k ∣ q - 1 := by
  classical
  haveI : Finite ↥Q.toSubgroup := Subtype.finite
  haveI : Finite ↥(normalizer (Q.toSubgroup : Set ↥G)) := Subtype.finite
  have hcardNz : Nat.card ↥(normalizer (Q.toSubgroup : Set ↥G))
      = q * (Nat.card (center SL(2,F)) * k) :=
    caseV_card_normalizer_Q G Q q k hq K hK_le hK_card hNQK hQK_disj
  set e := Nat.card (center SL(2,F)) with he_def
  have hq_pos : 0 < q := by rw [← hq]; exact Nat.card_pos
  have he_pos : 0 < e := by rw [he_def]; exact Nat.card_pos
  have horb : ∀ b : ↥Q.toSubgroup, b ≠ 1 →
      Nat.card (MulAction.orbit (↥(normalizer (Q.toSubgroup : Set ↥G))) b) = k := by
    intro b hb
    have hos : Nat.card (MulAction.orbit (↥(normalizer (Q.toSubgroup : Set ↥G))) b)
        * Nat.card (MulAction.stabilizer (↥(normalizer (Q.toSubgroup : Set ↥G))) b)
        = Nat.card ↥(normalizer (Q.toSubgroup : Set ↥G)) := by
      have h1 : Nat.card (MulAction.orbit (↥(normalizer (Q.toSubgroup : Set ↥G))) b)
          = (MulAction.stabilizer (↥(normalizer (Q.toSubgroup : Set ↥G))) b).index := by
        rw [Nat.card_coe_set_eq, ← MulAction.index_stabilizer]
      rw [h1, Subgroup.index_mul_card]
    -- RESIDUAL (Butler 6.8(iii)): the stabiliser of the conjugation action at a noncentral
    -- `b ∈ Q` is `C_G(b) ∩ N_G(Q) = Q × Z`, of cardinality `q · e`.
    have hstab : Nat.card (MulAction.stabilizer (↥(normalizer (Q.toSubgroup : Set ↥G))) b)
        = q * e := by
      rw [he_def]
      exact caseV_card_stabilizer_eq G center_le_G Q q hq b hb
    rw [hstab, hcardNz] at hos
    have hqe : 0 < q * e := Nat.mul_pos hq_pos he_pos
    have hfin : Nat.card (MulAction.orbit (↥(normalizer (Q.toSubgroup : Set ↥G))) b) * (q * e)
        = k * (q * e) := by rw [hos]; ring
    exact Nat.eq_of_mul_eq_mul_right hqe hfin
  have hdvd : k ∣ Nat.card ↥Q.toSubgroup - 1 :=
    caseV_dvd_card_sub_one_of_orbit
      (H := ↥(normalizer (Q.toSubgroup : Set ↥G))) (1 : ↥Q.toSubgroup)
      (fun h => smul_one h) horb
  rwa [hq] at hdvd

/-- Butler tex 1928-1933 ("Applying Lemma `caseVlemma`, `Q` is not normal in `G`"): hence
`|N_G(Q)| = e q k < e g = |G|`, i.e. `q * k ≠ g`. Proof: `K` is cyclic with `|K| = e·k > e`
and (via the Sylow complement `N_G(Q) = Q ⋊ K`) order coprime to `p`, so
`K_mem_MaximalAbelianSubgroups_of_center_lt_card_K` makes `K` maximal abelian; `hComplete`
(ruling out Sylow type by coprimality) plus `relIndex_normalizer_conj_smul_eq` gives
`[N_G(K) : K] = 2`, so `Sylow.not_normal_subgroup_of_G` applies. If `q * k = g` then
`|N_G(Q)| = e q k = e g = |G|` forces `N_G(Q) = ⊤`, i.e. `Q ⊴ G`, contradiction. -/
lemma caseV_qk_ne_g {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F]
    [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q k : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q) (hq2 : 2 ≤ q) (hk2 : 2 ≤ k)
    (A : Subgroup SL(2,F)) (hA_mem : A ∈ MaximalAbelianSubgroupsOf G)
    (hA_relIndex : relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) = 2)
    (B : Subgroup SL(2,F)) (hB_mem : B ∈ MaximalAbelianSubgroupsOf G)
    (hB_relIndex : relIndex (B.subgroupOf G) (normalizer (B.subgroupOf G : Set ↥G)) = 2)
    (K : Subgroup SL(2,F)) (hK_le : K ≤ G) (hK_cyc : IsCyclic K)
    (hK_card : Nat.card K = Nat.card (center SL(2,F)) * k)
    (hNQK : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G)
    (hQK_disj : Disjoint Q.toSubgroup (K.subgroupOf G))
    (hComplete : ∀ B' ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B' = A) ∨
      (∃ c ∈ G, conj c • B' = B) ∨ NumericClassEquation.IsSylowType p G B') :
    q * k ≠ g := by
  have he_pos : 0 < Nat.card (center SL(2,F)) := Nat.card_pos
  haveI : Finite ↥K :=
    Finite.of_injective (Subgroup.inclusion hK_le) (Subgroup.inclusion_injective hK_le)
  -- `Q` is nontrivial.
  have hQ_ne_bot : Q.toSubgroup ≠ ⊥ := by
    intro h
    have h1 : (1 : ℕ) = q := by rw [← hq, h]; exact Subgroup.card_bot.symm
    omega
  -- Cardinality of the internal `K`.
  have hcard_KsubG : Nat.card (K.subgroupOf G) = Nat.card (center SL(2,F)) * k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le).toEquiv, hK_card]
  -- === complement block (modelled on `caseV_q_mul_k_dvd_g`) ===
  set Nz : Subgroup ↥G := normalizer (Q.toSubgroup : Set ↥G) with hNz_def
  have hQ_le_Nz : Q.toSubgroup ≤ Nz := Subgroup.le_normalizer
  have hK'_le_Nz : K.subgroupOf G ≤ Nz := by rw [hNQK]; exact le_sup_right
  set Qn : Subgroup ↥Nz := Q.toSubgroup.subgroupOf Nz with hQn_def
  set Kn : Subgroup ↥Nz := (K.subgroupOf G).subgroupOf Nz with hKn_def
  have hsup : Qn ⊔ Kn = ⊤ := by
    have h := congrArg (Subgroup.subgroupOf · Nz) hNQK
    rw [Subgroup.subgroupOf_self, Subgroup.subgroupOf_sup hQ_le_Nz hK'_le_Nz] at h
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
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_Nz).toEquiv]; exact hq
  have hcard_Kn_eq : Nat.card Kn = Nat.card (K.subgroupOf G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK'_le_Nz).toEquiv
  have hcard_Nz_eq : Nat.card Nz = q * Nat.card (K.subgroupOf G) := by
    rw [← hcard_Nz, hcard_Qn, hcard_Kn_eq]
  -- === coprimality: `Nat.card (K.subgroupOf G)` is coprime to `p` ===
  have hqne : (q : ℕ) ≠ 0 := by omega
  have hNz_dvd_G : Nat.card Nz ∣ Nat.card G := Subgroup.card_subgroup_dvd_card Nz
  have hdvd_qcard : q * Nat.card (K.subgroupOf G) ∣ Nat.card G := hcard_Nz_eq ▸ hNz_dvd_G
  have hG_card : Nat.card G = q * Q.toSubgroup.index := by
    have h := Subgroup.index_mul_card Q.toSubgroup
    rw [hq] at h
    rw [← h]; ring
  have hdvd2 : q * Nat.card (K.subgroupOf G) ∣ q * Q.toSubgroup.index := hG_card ▸ hdvd_qcard
  have hcardK_dvd_index : Nat.card (K.subgroupOf G) ∣ Q.toSubgroup.index :=
    (mul_dvd_mul_iff_left hqne).mp hdvd2
  have hp_ndvd_index : ¬ p ∣ Q.toSubgroup.index := Q.not_dvd_index
  have hp_ndvd_K : ¬ p ∣ Nat.card (K.subgroupOf G) :=
    fun h => hp_ndvd_index (h.trans hcardK_dvd_index)
  have hcop_KsubG : Nat.Coprime (Nat.card (K.subgroupOf G)) p :=
    ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hp_ndvd_K).symm
  -- === `K` (internal) is cyclic, big, hence maximal abelian ===
  have hK'_cyc : IsCyclic (K.subgroupOf G) :=
    (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hK_le)).mpr hK_cyc
  have hKZ_gt : Nat.card (K.subgroupOf G) > Nat.card (center SL(2,F)) := by
    rw [hcard_KsubG]
    have h1 : Nat.card (center SL(2,F)) * 2 ≤ Nat.card (center SL(2,F)) * k :=
      Nat.mul_le_mul (le_refl _) hk2
    omega
  have hNG_arg : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G := hNQK
  have hK_maxAb : map G.subtype (K.subgroupOf G) ∈ MaximalAbelianSubgroupsOf G :=
    K_mem_MaximalAbelianSubgroups_of_center_lt_card_K G Q hQ_ne_bot (K.subgroupOf G)
      hK'_cyc hNG_arg hKZ_gt hcop_KsubG
  -- `map G.subtype (K.subgroupOf G) = K` since `K ≤ G`.
  have hMA : map G.subtype (K.subgroupOf G) = K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hK_le]
  have hK_maxAb' : K ∈ MaximalAbelianSubgroupsOf G := hMA ▸ hK_maxAb
  -- === `[N_G(K) : K] = 2` via `hComplete` ===
  have hNK : relIndex (K.subgroupOf G)
      (normalizer ((K.subgroupOf G : Subgroup ↥G) : Set ↥G)) = 2 := by
    rcases hComplete (map G.subtype (K.subgroupOf G)) hK_maxAb with
      ⟨c, hc, hconj⟩ | ⟨c, hc, hconj⟩ | hsyl
    · rw [hMA] at hconj
      have hrel := NumericClassEquation.relIndex_normalizer_conj_smul_eq (G := G) (A := K) hc
      rw [hconj, hA_relIndex] at hrel
      exact hrel.symm
    · rw [hMA] at hconj
      have hrel := NumericClassEquation.relIndex_normalizer_conj_smul_eq (G := G) (A := K) hc
      rw [hconj, hB_relIndex] at hrel
      exact hrel.symm
    · exfalso
      rw [hMA] at hsyl
      have hpdvd : p ∣ Nat.card K := NumericClassEquation.dvd_card_of_isSylowType hsyl
      have hpdvd' : p ∣ Nat.card (K.subgroupOf G) := by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le).toEquiv]
      exact hp_ndvd_K hpdvd'
  -- === assemble non-normality (Butler `caseVlemma`) ===
  have hQK_arg : map G.subtype (normalizer (Q.toSubgroup : Set ↥G))
      = map G.subtype Q.toSubgroup ⊔ K := by
    rw [← hNz_def, hNQK, Subgroup.map_sup, hMA]
  have hQcapK_arg : map G.subtype Q.toSubgroup ⊓ K = ⊥ := by
    rw [← hMA, ← Subgroup.map_inf Q.toSubgroup (K.subgroupOf G) G.subtype
      (G.subtype_injective), disjoint_iff.mp hQK_disj, Subgroup.map_bot]
  have hnot_normal : ¬ Normal Q.toSubgroup :=
    Sylow.not_normal_subgroup_of_G G K Q hK_maxAb' hQK_arg hQcapK_arg hNK
  -- === conclude `q * k ≠ g` ===
  intro heq
  apply hnot_normal
  have hNz_top : Nz = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard_Nz_eq, hcard_KsubG, hg, ← heq]; ring
  rw [hNz_def] at hNz_top
  exact normalizer_eq_top_iff.mp hNz_top

/-- Case V arithmetic core: fully proven. -/
theorem caseV_arith (g q g1 g2 : ℕ) (hgpos : 1 ≤ g) (hq2 : 2 ≤ q)
    (hg1 : 2 ≤ g1) (hg2 : 2 ≤ g2)
    (horbit : g1 ∣ q - 1)
    (hNQ_dvd : q * g1 ∣ g) (hNQ_ne : q * g1 ≠ g)
    (hNA2_dvd : 2 * g2 ∣ g)
    (hg2q_cop : Nat.Coprime g2 q)
    (heq : ClassEquation g q g1 (s := 0) (t := 2) (fun i => i.elim0) ![g1, g2]) :
    (4 ≤ q ∧ ∃ i, (i = 1 ∨ i = 2) ∧ 2 * g1 = i * (q - 1) ∧ 2 * g2 = i * (q + 1) ∧
        2 * g = i * (q * (q ^ 2 - 1)))
      ∨ (q = 3 ∧ g1 = 2 ∧ ((g2 = 4 ∧ g = 24) ∨ (g2 = 5 ∧ g = 60))) := by
  -- normalize the class equation to Butler's `case5b`
  unfold ClassEquation at heq
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, add_zero] at heq
  have hgQ : (0:ℚ) < g := by exact_mod_cast hgpos
  have hqQ : (0:ℚ) < q := by exact_mod_cast (show 0 < q by omega)
  have hg1Q : (0:ℚ) < g1 := by exact_mod_cast (show 0 < g1 by omega)
  have hg2Q : (0:ℚ) < g2 := by exact_mod_cast (show 0 < g2 by omega)
  have hgne : (g:ℚ) ≠ 0 := ne_of_gt hgQ
  have hqne : (q:ℚ) ≠ 0 := ne_of_gt hqQ
  have hg1ne : (g1:ℚ) ≠ 0 := ne_of_gt hg1Q
  have hg2ne : (g2:ℚ) ≠ 0 := ne_of_gt hg2Q
  rw [one_sub_inv_two_self hg1ne, one_sub_inv_two_self hg2ne] at heq
  have e5b : (1:ℚ)/(2*g1) + 1/(2*g2) = 1/g + ((q:ℚ)-1)/(q*g1) := by linarith
  -- integer index witnesses
  obtain ⟨b, hb⟩ := hNQ_dvd
  obtain ⟨a, ha⟩ := hNA2_dvd
  have hbpos : 1 ≤ b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · rw [mul_zero] at hb; omega
    · exact h
  have hapos : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | h
    · rw [mul_zero] at ha; omega
    · exact h
  have hb2 : 2 ≤ b := by
    rcases Nat.lt_or_ge b 2 with h | h
    · exfalso
      have hb1 : b = 1 := by omega
      rw [hb1, mul_one] at hb
      exact hNQ_ne hb.symm
    · exact h
  -- master identity `2a + 2b = 2 + qb` (Butler's `case5b` cleared of denominators)
  have hgb : (g:ℚ) = q * g1 * b := by exact_mod_cast hb
  have hga : (g:ℚ) = 2 * g2 * a := by exact_mod_cast ha
  have t1 : (1:ℚ)/(2*g1) * (2*g) = q * b := by
    rw [hgb]; field_simp
  have t2 : (1:ℚ)/(2*g2) * (2*g) = 2 * a := by
    rw [hga]; field_simp
  have t3 : (1:ℚ)/g * (2*g) = 2 := by field_simp
  have t4 : ((q:ℚ)-1)/(q*g1) * (2*g) = 2*((q:ℚ)-1)*b := by
    rw [hgb]; field_simp
  have masterQ : (q:ℚ)*b + 2*a = 2 + 2*((q:ℚ)-1)*b := by
    calc (q:ℚ)*b + 2*a = ((1:ℚ)/(2*g1) + 1/(2*g2)) * (2*g) := by rw [add_mul, t1, t2]
      _ = ((1:ℚ)/g + ((q:ℚ)-1)/(q*g1)) * (2*g) := by rw [e5b]
      _ = 2 + 2*((q:ℚ)-1)*b := by rw [add_mul, t3, t4]
  have master : 2*a + 2*b = 2 + q*b := by
    have h : 2*(a:ℚ) + 2*(b:ℚ) = 2 + (q:ℚ)*(b:ℚ) := by linear_combination masterQ
    exact_mod_cast h
  -- (6.14) witness; `q = 2` impossible
  obtain ⟨d, hd⟩ := horbit
  have hq3 : 3 ≤ q := by
    by_contra hcon
    have hq2' : q = 2 := by omega
    rw [hq2'] at hd
    have h1 : g1 * d = 1 := by simpa using hd.symm
    have hdvd1 : g1 ∣ 1 := ⟨d, h1.symm⟩
    have := Nat.le_of_dvd one_pos hdvd1
    omega
  have hdpos : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · rw [mul_zero] at hd; omega
    · exact h
  have hqd : q = g1 * d + 1 := by rw [← hd]; omega
  -- key integer identity and the integer `i := 2 g₂ / b`
  have hmz : 2*(a:ℤ) + 2*(b:ℤ) = 2 + (q:ℤ)*(b:ℤ) := by exact_mod_cast master
  have haz : (g:ℤ) = 2 * g2 * a := by exact_mod_cast ha
  have hbz : (g:ℤ) = q * g1 * b := by exact_mod_cast hb
  have hbdvd : ((2:ℤ) * g2) = b * ((q:ℤ)*g1 + 2*g2 - q*g2) := by
    linear_combination (-(g2:ℤ)) * hmz - haz + hbz
  have hbdvdN : b ∣ 2 * g2 := by
    have h1 : (b:ℤ) ∣ 2 * (g2:ℤ) := ⟨_, hbdvd⟩
    exact_mod_cast h1
  obtain ⟨i, hi⟩ := hbdvdN
  have hipos : 1 ≤ i := by
    rcases Nat.eq_zero_or_pos i with rfl | h
    · rw [mul_zero] at hi; omega
    · exact h
  -- (6.15): `q g₁ + 2 g₂ = i + q g₂`
  have h615 : q * g1 + 2 * g2 = i + q * g2 := by
    have hiz : (2:ℤ) * g2 = b * i := by exact_mod_cast hi
    have hbne : (b:ℤ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
    have hcancel : (b:ℤ) * ((q:ℤ)*g1 + 2*g2) = b * ((i:ℤ) + q*g2) := by
      linear_combination hiz - hbdvd
    have h2 := mul_left_cancel₀ hbne hcancel
    exact_mod_cast h2
  -- `i ≤ g₂` and `g₁ < g₂`
  have hile : i ≤ g2 := by
    have h1 : 2 * i ≤ b * i := Nat.mul_le_mul hb2 le_rfl
    linarith [hi, h1]
  have hg1g2 : g1 < g2 := by
    by_contra hcon
    have hcon' : g2 ≤ g1 := not_lt.mp hcon
    have h1 : q * g2 ≤ q * g1 := Nat.mul_le_mul le_rfl hcon'
    linarith [h615, hile, hg2]
  rcases Nat.lt_or_ge q 4 with hqlt4 | hq4
  · -- Cases Vc/Vd: `q = 3`
    right
    have hq3' : q = 3 := by omega
    subst hq3'
    have h2' : g1 * d = 2 := by simpa using hd.symm
    have hg1e : g1 = 2 := by
      have hdvd : g1 ∣ 2 := ⟨d, h2'.symm⟩
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hde : d = 1 := by rw [hg1e] at h2'; omega
    refine ⟨rfl, hg1e, ?_⟩
    rw [hg1e] at h615
    have hig2 : i + g2 = 6 := by omega
    have hg2gt : 2 < g2 := by omega
    have hg2ne3 : g2 ≠ 3 := by
      rintro rfl
      exact (by decide : ¬ Nat.Coprime 3 3) hg2q_cop
    have hg2cases : g2 = 4 ∨ g2 = 5 := by omega
    rcases hg2cases with rfl | rfl
    · left
      refine ⟨rfl, ?_⟩
      have hie : i = 2 := by omega
      rw [hie] at hi
      have hbe : b = 4 := by omega
      rw [hg1e, hbe] at hb
      omega
    · right
      refine ⟨rfl, ?_⟩
      have hie : i = 1 := by omega
      rw [hie] at hi
      have hbe : b = 10 := by omega
      rw [hg1e, hbe] at hb
      omega
  · -- Cases Va/Vb: `q ≥ 4`
    left
    refine ⟨hq4, ?_⟩
    have hz615 : (q:ℤ)*g1 + 2*g2 = i + q*g2 := by exact_mod_cast h615
    have hzq4 : (4:ℤ) ≤ q := by exact_mod_cast hq4
    have hzg1 : (2:ℤ) ≤ g1 := by exact_mod_cast hg1
    have hzg2 : (2:ℤ) ≤ g2 := by exact_mod_cast hg2
    have hzi : (1:ℤ) ≤ i := by exact_mod_cast hipos
    have hzile : (i:ℤ) ≤ g2 := by exact_mod_cast hile
    -- `g₂ < 2 g₁` (6.18)
    have hg2lt : g2 < 2 * g1 := by
      by_contra hcon
      have hcon' : 2 * g1 ≤ g2 := not_lt.mp hcon
      have hzcon : 2*(g1:ℤ) ≤ g2 := by exact_mod_cast hcon'
      nlinarith [mul_le_mul_of_nonneg_left hzcon (by linarith : (0:ℤ) ≤ (q:ℤ) - 2),
        mul_nonneg (by linarith : (0:ℤ) ≤ (q:ℤ) - 4) (by linarith : (0:ℤ) ≤ (g1:ℤ))]
    have hzg2lt : (g2:ℤ) < 2*g1 := by exact_mod_cast hg2lt
    -- (6.16a): `g₂ - i = (d g₂ - q) g₁`, and `d g₂ - q = 1`
    have hzqd : (q:ℤ) = g1 * d + 1 := by exact_mod_cast hqd
    have h616a : (g2:ℤ) - i = ((d:ℤ)*g2 - q) * g1 := by
      linear_combination hz615 + (g2:ℤ) * hzqd
    have hE_nonneg : 0 ≤ (d:ℤ)*g2 - q := by
      by_contra hcon
      have hcon' : (d:ℤ)*g2 - q < 0 := not_le.mp hcon
      have hE1 : (d:ℤ)*g2 - q ≤ -1 := by linarith [Int.lt_iff_add_one_le.mp hcon']
      have h2 : ((d:ℤ)*g2 - q) * g1 ≤ (-1) * g1 :=
        mul_le_mul_of_nonneg_right hE1 (by linarith)
      linarith [h616a]
    have hE_le1 : (d:ℤ)*g2 - q ≤ 1 := by
      by_contra hcon
      have hcon' : (1:ℤ) < (d:ℤ)*g2 - q := not_le.mp hcon
      have hE2 : (2:ℤ) ≤ (d:ℤ)*g2 - q := by linarith [Int.lt_iff_add_one_le.mp hcon']
      have h2 : (2:ℤ) * g1 ≤ ((d:ℤ)*g2 - q) * g1 :=
        mul_le_mul_of_nonneg_right hE2 (by linarith)
      linarith [h616a]
    have hE_ne0 : (d:ℤ)*g2 - q ≠ 0 := by
      intro hE0
      have hdq : d * g2 = q := by
        have h1 : (d:ℤ)*(g2:ℤ) = (q:ℤ) := by linarith
        exact_mod_cast h1
      have hdvd : g2 ∣ q := ⟨d, by rw [← hdq]; ring⟩
      have h1 : g2 ∣ Nat.gcd g2 q := Nat.dvd_gcd dvd_rfl hdvd
      have h2 : Nat.gcd g2 q = 1 := hg2q_cop
      rw [h2] at h1
      have := Nat.le_of_dvd one_pos h1
      omega
    have hE1 : (d:ℤ)*g2 - q = 1 := by
      have h0 : 0 < (d:ℤ)*g2 - q := lt_of_le_of_ne hE_nonneg (Ne.symm hE_ne0)
      have h1 : 1 ≤ (d:ℤ)*g2 - q := by linarith [Int.lt_iff_add_one_le.mp h0]
      linarith
    -- (6.19) and the endgame `i d = 2`
    have h619 : (g2:ℤ) = g1 + i := by
      rw [hE1, one_mul] at h616a
      linarith
    have h2g1z : 2*(g1:ℤ) = i*((q:ℤ)-1) := by
      linear_combination hz615 + ((q:ℤ)-2) * h619
    have hidz : (i:ℤ) * d = 2 := by
      have hg1zne : (g1:ℤ) ≠ 0 := by exact_mod_cast (show g1 ≠ 0 by omega)
      have hcalc : (2:ℤ) * g1 = ((i:ℤ)*d) * g1 := by
        linear_combination h2g1z + (i:ℤ) * hzqd
      have := mul_right_cancel₀ hg1zne hcalc
      linarith
    have hid : i * d = 2 := by exact_mod_cast hidz
    have hi12 : i = 1 ∨ i = 2 := by
      have hidvd : i ∣ 2 := ⟨d, hid.symm⟩
      exact (Nat.dvd_prime Nat.prime_two).mp hidvd
    have hq1le : 1 ≤ q := by omega
    refine ⟨i, hi12, ?_, ?_, ?_⟩
    · have h1 : ((2*g1 : ℕ) : ℤ) = ((i*(q-1) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hq1le]
        linarith [h2g1z]
      exact_mod_cast h1
    · have h2g2z : 2*(g2:ℤ) = i*((q:ℤ)+1) := by linear_combination 2*h619 + h2g1z
      have h1 : ((2*g2 : ℕ) : ℤ) = ((i*(q+1) : ℕ) : ℤ) := by
        push_cast
        linarith [h2g2z]
      exact_mod_cast h1
    · have h2g2z : 2*(g2:ℤ) = i*((q:ℤ)+1) := by linear_combination 2*h619 + h2g1z
      have hbqz : (b:ℤ) = (q:ℤ) + 1 := by
        have hiz : (2:ℤ) * g2 = b * i := by exact_mod_cast hi
        have hine : (i:ℤ) ≠ 0 := by exact_mod_cast (show i ≠ 0 by omega)
        have h1 : (b:ℤ)*i = ((q:ℤ)+1)*i := by linarith [h2g2z, hiz]
        have := mul_right_cancel₀ hine h1
        linarith
      have hfin : 2*(g:ℤ) = i*((q:ℤ)*((q:ℤ)^2 - 1)) := by
        linear_combination 2*hbz + (q:ℤ)*(b:ℤ)*h2g1z + (i:ℤ)*(q:ℤ)*((q:ℤ)-1)*hbqz
      have hq2le : 1 ≤ q^2 := Nat.one_le_pow 2 q (by omega)
      have h1 : ((2*g : ℕ) : ℤ) = ((i*(q*(q^2-1)) : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hq2le]
        linarith [hfin]
      exact_mod_cast h1

/-- Unique involution of a subgroup containing the center (`p ≠ 2`). -/
lemma caseV_exists_unique_involution {F : Type*} [Field F] [NeZero (2:F)]
    (G : Subgroup SL(2,F)) (center_le_G : center SL(2,F) ≤ G) :
    ∃! x : ↥G, orderOf x = 2 := by
  have hneg1_mem : (-1 : SL(2,F)) ∈ G := by
    apply center_le_G
    rw [SpecialSubgroups.center_SL2_eq_Z]
    exact SpecialSubgroups.neg_one_mem_Z
  refine ⟨⟨-1, hneg1_mem⟩, ?_, ?_⟩
  · have h1 : orderOf ((⟨-1, hneg1_mem⟩ : ↥G) : SL(2,F)) = 2 :=
      SpecialSubgroups.orderOf_neg_one_eq_two
    rwa [orderOf_coe] at h1
  · rintro y hy
    have hy' : orderOf (y : SL(2,F)) = 2 := by rw [orderOf_coe]; exact hy
    obtain ⟨τ, hτ2, hτuniq⟩ := SpecialSubgroups.exists_unique_orderOf_eq_two (F := F)
    have h1 : (y : SL(2,F)) = τ := hτuniq _ hy'
    have h2 : (-1 : SL(2,F)) = τ := hτuniq _ SpecialSubgroups.orderOf_neg_one_eq_two
    exact Subtype.ext (by rw [h1, ← h2])

/-! ### Case Vd/VIc, Butler tex 2088-2111: elementary group theory feeding `caseV_d_recognition`.

Butler derives `|G/Z| = 60` and `G/Z` simple directly from the `SL(2,F)` class-equation
arithmetic (where `Z = Z(SL(2,F)) = {±1}` is manifestly of order `2`). The abstract recognition
lemma only sees `|H| = 120`, a unique involution, and `IsSimpleGroup (H ⧸ Z(H))`, so it must
*recover* `|Z(H)| = 2` (equivalently `|H/Z(H)| = 60`). This is the classical fact that the only
simple group whose order lies strictly between `1` and `120` and divides `120` (with even
cofactor) is `A₅` of order `60` — proved here by ruling out simple groups of every intermediate
order `{6,10,12,15,20}` and `30`, none of which appears in mathlib. -/

-- A group of order `2q` (`q` prime) has an index-`2`, hence normal, cyclic subgroup: not simple.
lemma caseV_d_not_simple_two_mul_prime {Q : Type*} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (hcard : Nat.card Q = 2 * q) : ¬ IsSimpleGroup Q := by
  intro hs
  have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' q ⟨2, by rw [hcard]; ring⟩
  have hzp : Nat.card (Subgroup.zpowers g) = q := by rw [Nat.card_zpowers, hg]
  have hqpos : 0 < q := by omega
  have hidx : (Subgroup.zpowers g).index = 2 := by
    have h := Subgroup.card_mul_index (Subgroup.zpowers g)
    rw [hzp, hcard] at h
    exact Nat.eq_of_mul_eq_mul_left hqpos (by rw [h]; ring)
  have hnorm : (Subgroup.zpowers g).Normal := Subgroup.normal_of_index_eq_two hidx
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  · have : Nat.card (Subgroup.zpowers g) = 1 := by rw [hb]; exact Subgroup.card_bot
    omega
  · have : Nat.card (Subgroup.zpowers g) = Nat.card Q := by rw [ht]; exact Subgroup.card_top
    omega

lemma caseV_d_not_simple_sylow_card_one {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (P : Sylow p Q) (hn : Nat.card (Sylow p Q) = 1)
    (hpos : 1 < Nat.card (P : Subgroup Q)) (hlt : Nat.card (P : Subgroup Q) < Nat.card Q) :
    ¬ IsSimpleGroup Q := by
  intro hs
  haveI : Subsingleton (Sylow p Q) := Nat.card_eq_one_iff_unique.mp hn |>.1
  have hnorm : (P : Subgroup Q).Normal := Sylow.normal_of_subsingleton P
  rcases hnorm.eq_bot_or_eq_top with hb | ht
  · rw [hb] at hpos; rw [Subgroup.card_bot] at hpos; omega
  · rw [ht] at hlt; rw [Subgroup.card_top] at hlt; omega

lemma caseV_d_sylow_card_ne_one_of_simple {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hs : IsSimpleGroup Q) (P : Sylow p Q) (hpos : 1 < Nat.card (P : Subgroup Q))
    (hlt : Nat.card (P : Subgroup Q) < Nat.card Q) : Nat.card (Sylow p Q) ≠ 1 :=
  fun hn => caseV_d_not_simple_sylow_card_one P hn hpos hlt hs

lemma caseV_d_not_simple_15 {Q : Type*} [Group Q] [Finite Q] (hcard : Nat.card Q = 15) :
    ¬ IsSimpleGroup Q := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain P := Classical.arbitrary (Sylow 5 Q)
  have hf : (15 : ℕ).factorization 5 = 1 := by
    rw [show (15 : ℕ) = 5 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcardP : Nat.card (P : Subgroup Q) = 5 := by rw [P.card_eq_multiplicity, hcard, hf, pow_one]
  have hidx : (P : Subgroup Q).index = 3 := by
    have := P.toSubgroup.card_mul_index; rw [hcardP, hcard] at this; omega
  have hn : Nat.card (Sylow 5 Q) = 1 := by
    have hdvd : Nat.card (Sylow 5 Q) ∣ 3 := hidx ▸ P.card_dvd_index
    have hmod : Nat.card (Sylow 5 Q) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 Q
    have hle : Nat.card (Sylow 5 Q) ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 5 Q) := Nat.card_pos
    unfold Nat.ModEq at hmod; interval_cases (Nat.card (Sylow 5 Q)) <;> omega
  exact caseV_d_not_simple_sylow_card_one P hn (by omega) (by omega)

lemma caseV_d_not_simple_20 {Q : Type*} [Group Q] [Finite Q] (hcard : Nat.card Q = 20) :
    ¬ IsSimpleGroup Q := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain P := Classical.arbitrary (Sylow 5 Q)
  have hf : (20 : ℕ).factorization 5 = 1 := by
    rw [show (20 : ℕ) = 5 * 4 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hcardP : Nat.card (P : Subgroup Q) = 5 := by rw [P.card_eq_multiplicity, hcard, hf, pow_one]
  have hidx : (P : Subgroup Q).index = 4 := by
    have := P.toSubgroup.card_mul_index; rw [hcardP, hcard] at this; omega
  have hn : Nat.card (Sylow 5 Q) = 1 := by
    have hdvd : Nat.card (Sylow 5 Q) ∣ 4 := hidx ▸ P.card_dvd_index
    have hmod : Nat.card (Sylow 5 Q) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 Q
    have hle : Nat.card (Sylow 5 Q) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 5 Q) := Nat.card_pos
    unfold Nat.ModEq at hmod; interval_cases (Nat.card (Sylow 5 Q)) <;> omega
  exact caseV_d_not_simple_sylow_card_one P hn (by omega) (by omega)

/-! The two `p²·q`-type orders `12` and `30` need an element count: `n_p·(p-1)` elements of
order `p` when `p ‖ |Q|`. -/

lemma caseV_d_inf_eq_bot_of_card_prime {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (A B : Subgroup Q) (hA : Nat.card A = p) (hB : Nat.card B = p) (hAB : A ≠ B) :
    A ⊓ B = ⊥ := by
  have hdvd : Nat.card (A ⊓ B : Subgroup Q) ∣ p := by
    rw [← hA]; exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact Subgroup.card_eq_one.mp h1
  · exfalso; apply hAB
    have hAI : (A ⊓ B : Subgroup Q) = A := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left; rw [hp', hA]
    have hBI : (A ⊓ B : Subgroup Q) = B := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_right; rw [hp', hB]
    rw [← hAI, hBI]

lemma caseV_d_orderOf_eq_of_mem_card_prime {Q : Type*} [Group Q] {p : ℕ} [Fact p.Prime]
    {P : Subgroup Q} (hP : Nat.card P = p) {x : Q} (hx : x ∈ P) (hx1 : x ≠ 1) :
    orderOf x = p := by
  have hdvd : orderOf (⟨x, hx⟩ : P) ∣ p := hP ▸ orderOf_dvd_natCard _
  have hne : orderOf (⟨x, hx⟩ : P) ≠ 1 :=
    fun h => hx1 (Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h))
  have hop : orderOf (⟨x, hx⟩ : P) = p := ((Nat.dvd_prime (Fact.out)).mp hdvd).resolve_left hne
  show orderOf ((⟨x, hx⟩ : P) : Q) = p
  rw [orderOf_coe]; exact hop

lemma caseV_d_card_orderOf_eq_prime {Q : Type*} [Group Q] [Fintype Q] {p : ℕ} [Fact p.Prime]
    (hmult : (Nat.card Q).factorization p = 1) :
    (Finset.univ.filter (fun x : Q => orderOf x = p)).card = Nat.card (Sylow p Q) * (p - 1) := by
  classical
  letI : Fintype (Sylow p Q) := Fintype.ofFinite _
  have hpp : p.Prime := Fact.out
  have hcardSyl : ∀ P : Sylow p Q, Nat.card (P : Subgroup Q) = p := by
    intro P; rw [P.card_eq_multiplicity, hmult, pow_one]
  set T : Sylow p Q → Finset Q :=
    fun P => Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q) ∧ orderOf x = p) with hT
  have hbi : Finset.univ.filter (fun x : Q => orderOf x = p) = Finset.univ.biUnion T := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hT]
    constructor
    · intro hx
      have hzc : Nat.card (Subgroup.zpowers x) = p ^ (Nat.card Q).factorization p := by
        rw [Nat.card_zpowers, hx, hmult, pow_one]
      refine ⟨Sylow.ofCard (Subgroup.zpowers x) hzc, ?_, hx⟩
      rw [Sylow.coe_ofCard]; exact Subgroup.mem_zpowers x
    · rintro ⟨P, -, hxo⟩; exact hxo
  have hdisj : (↑(Finset.univ : Finset (Sylow p Q)) : Set (Sylow p Q)).PairwiseDisjoint T := by
    intro P _ P' _ hPP'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxP hxP'
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hxP hxP'
    have hinf : (P : Subgroup Q) ⊓ (P' : Subgroup Q) = ⊥ :=
      caseV_d_inf_eq_bot_of_card_prime hpp _ _ (hcardSyl P) (hcardSyl P')
        (fun h => hPP' (Sylow.ext h))
    have hxmem : x ∈ (P : Subgroup Q) ⊓ (P' : Subgroup Q) := ⟨hxP.1, hxP'.1⟩
    rw [hinf, Subgroup.mem_bot] at hxmem
    rw [hxmem] at hxP
    simp only [orderOf_one, Subgroup.one_mem, true_and] at hxP
    exact absurd hxP.symm hpp.ne_one
  rw [hbi, Finset.card_biUnion hdisj]
  have hterm : ∀ P : Sylow p Q, (T P).card = p - 1 := by
    intro P
    have hTP : T P = (Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q))).filter (· ≠ 1) := by
      rw [hT]; ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hxP, hxo⟩
        exact ⟨hxP, fun h => by rw [h, orderOf_one] at hxo; exact hpp.ne_one hxo.symm⟩
      · rintro ⟨hxP, hx1⟩; exact ⟨hxP, caseV_d_orderOf_eq_of_mem_card_prime (hcardSyl P) hxP hx1⟩
    rw [hTP]
    have hmemcard : (Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q))).card = p := by
      have h1 : (Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q))).card
          = Nat.card (P : Subgroup Q) := by
        rw [show (Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q))).card
            = Fintype.card {x // x ∈ (P : Subgroup Q)} from (Fintype.card_subtype _).symm,
          ← Nat.card_eq_fintype_card]
      rw [h1, hcardSyl P]
    have h1mem : (1 : Q) ∈ Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q)) := by simp
    rw [Finset.filter_ne', Finset.card_erase_of_mem h1mem, hmemcard]
  rw [Finset.sum_congr rfl (fun P _ => hterm P), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, smul_eq_mul]

lemma caseV_d_not_simple_30 {Q : Type*} [Group Q] [Finite Q] (hcard : Nat.card Q = 30) :
    ¬ IsSimpleGroup Q := by
  classical
  intro hs
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hf5 : (Nat.card Q).factorization 5 = 1 := by
    rw [hcard, show (30 : ℕ) = 5 * 6 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hf3 : (Nat.card Q).factorization 3 = 1 := by
    rw [hcard, show (30 : ℕ) = 3 * 10 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain P5 := Classical.arbitrary (Sylow 5 Q)
  obtain P3 := Classical.arbitrary (Sylow 3 Q)
  have hc5P : Nat.card (P5 : Subgroup Q) = 5 := by rw [P5.card_eq_multiplicity, hf5, pow_one]
  have hc3P : Nat.card (P3 : Subgroup Q) = 3 := by rw [P3.card_eq_multiplicity, hf3, pow_one]
  have hn5 : Nat.card (Sylow 5 Q) = 6 := by
    have hidx : (P5 : Subgroup Q).index = 6 := by
      have := P5.toSubgroup.card_mul_index; rw [hc5P, hcard] at this; omega
    have hdvd : Nat.card (Sylow 5 Q) ∣ 6 := hidx ▸ P5.card_dvd_index
    have hmod : Nat.card (Sylow 5 Q) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 Q
    have hle : Nat.card (Sylow 5 Q) ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 5 Q) := Nat.card_pos
    have hne : Nat.card (Sylow 5 Q) ≠ 1 :=
      caseV_d_sylow_card_ne_one_of_simple hs P5 (by omega) (by omega)
    unfold Nat.ModEq at hmod; interval_cases (Nat.card (Sylow 5 Q)) <;> omega
  have hn3 : Nat.card (Sylow 3 Q) = 10 := by
    have hidx : (P3 : Subgroup Q).index = 10 := by
      have := P3.toSubgroup.card_mul_index; rw [hc3P, hcard] at this; omega
    have hdvd : Nat.card (Sylow 3 Q) ∣ 10 := hidx ▸ P3.card_dvd_index
    have hmod : Nat.card (Sylow 3 Q) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 Q
    have hle : Nat.card (Sylow 3 Q) ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 3 Q) := Nat.card_pos
    have hne : Nat.card (Sylow 3 Q) ≠ 1 :=
      caseV_d_sylow_card_ne_one_of_simple hs P3 (by omega) (by omega)
    unfold Nat.ModEq at hmod; interval_cases (Nat.card (Sylow 3 Q)) <;> omega
  have hcnt5 := caseV_d_card_orderOf_eq_prime (Q := Q) (p := 5) hf5
  have hcnt3 := caseV_d_card_orderOf_eq_prime (Q := Q) (p := 3) hf3
  rw [hn5] at hcnt5; rw [hn3] at hcnt3
  have hdisj : Disjoint (Finset.univ.filter (fun x : Q => orderOf x = 5))
      (Finset.univ.filter (fun x : Q => orderOf x = 3)) := by
    rw [Finset.disjoint_left]; intro x h5 h3
    simp only [Finset.mem_filter] at h5 h3; omega
  have hunion := Finset.card_union_of_disjoint hdisj
  have hle : (Finset.univ.filter (fun x : Q => orderOf x = 5) ∪
      Finset.univ.filter (fun x : Q => orderOf x = 3)).card ≤ Fintype.card Q :=
    Finset.card_le_univ _
  rw [hunion, hcnt5, hcnt3, ← Nat.card_eq_fintype_card, hcard] at hle
  omega

lemma caseV_d_not_simple_12 {Q : Type*} [Group Q] [Finite Q] (hcard : Nat.card Q = 12) :
    ¬ IsSimpleGroup Q := by
  classical
  intro hs
  haveI : Fintype Q := Fintype.ofFinite Q
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hf3 : (Nat.card Q).factorization 3 = 1 := by
    rw [hcard, show (12 : ℕ) = 3 * 4 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain P3 := Classical.arbitrary (Sylow 3 Q)
  have hc3P : Nat.card (P3 : Subgroup Q) = 3 := by rw [P3.card_eq_multiplicity, hf3, pow_one]
  have hn3 : Nat.card (Sylow 3 Q) = 4 := by
    have hidx : (P3 : Subgroup Q).index = 4 := by
      have := P3.toSubgroup.card_mul_index; rw [hc3P, hcard] at this; omega
    have hdvd : Nat.card (Sylow 3 Q) ∣ 4 := hidx ▸ P3.card_dvd_index
    have hmod : Nat.card (Sylow 3 Q) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 Q
    have hle : Nat.card (Sylow 3 Q) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 3 Q) := Nat.card_pos
    have hne : Nat.card (Sylow 3 Q) ≠ 1 :=
      caseV_d_sylow_card_ne_one_of_simple hs P3 (by omega) (by omega)
    unfold Nat.ModEq at hmod; interval_cases (Nat.card (Sylow 3 Q)) <;> omega
  have hcnt3 := caseV_d_card_orderOf_eq_prime (Q := Q) (p := 3) hf3
  rw [hn3] at hcnt3
  have hcompl : (Finset.univ.filter (fun x : Q => orderOf x ≠ 3)).card ≤ 4 := by
    have hdisj : Disjoint (Finset.univ.filter (fun x : Q => orderOf x ≠ 3))
        (Finset.univ.filter (fun x : Q => orderOf x = 3)) := by
      rw [Finset.disjoint_left]; intro x h1 h2
      simp only [Finset.mem_filter] at h1 h2; exact h1.2 h2.2
    have hle : (Finset.univ.filter (fun x : Q => orderOf x ≠ 3)
        ∪ Finset.univ.filter (fun x : Q => orderOf x = 3)).card ≤ Fintype.card Q :=
      Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisj, hcnt3, ← Nat.card_eq_fintype_card, hcard] at hle
    omega
  have hf2 : (Nat.card Q).factorization 2 = 2 := by
    rw [hcard, show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), smul_eq_mul]
  have hc2P : ∀ P : Sylow 2 Q, Nat.card (P : Subgroup Q) = 4 := by
    intro P; rw [P.card_eq_multiplicity, hf2]; norm_num
  have hset : ∀ P : Sylow 2 Q,
      Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q))
        = Finset.univ.filter (fun x : Q => orderOf x ≠ 3) := by
    intro P
    have hsub : Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q))
        ⊆ Finset.univ.filter (fun x : Q => orderOf x ≠ 3) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hdvd : orderOf x ∣ 4 := by
        have hd : orderOf (⟨x, hx⟩ : (P : Subgroup Q)) ∣ 4 := by
          have := orderOf_dvd_natCard (⟨x, hx⟩ : (P : Subgroup Q)); rwa [hc2P P] at this
        show orderOf ((⟨x, hx⟩ : (P : Subgroup Q)) : Q) ∣ 4
        rw [orderOf_coe]; exact hd
      intro h3; rw [h3] at hdvd; omega
    have hcardP : (Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q))).card = 4 := by
      have h1 : (Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q))).card
          = Nat.card (P : Subgroup Q) := by
        rw [show (Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q))).card
            = Fintype.card {x // x ∈ (P : Subgroup Q)} from (Fintype.card_subtype _).symm,
          ← Nat.card_eq_fintype_card]
      rw [h1, hc2P P]
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcardP]; exact hcompl)
  haveI : Subsingleton (Sylow 2 Q) := by
    refine ⟨fun P P' => Sylow.ext (SetLike.ext (fun x => ?_))⟩
    have hP := hset P; have hP' := hset P'
    constructor <;> intro hx
    · have : x ∈ Finset.univ.filter (fun y : Q => y ∈ (P' : Subgroup Q)) := by
        rw [hP', ← hP]; simp [hx]
      simpa using this
    · have : x ∈ Finset.univ.filter (fun y : Q => y ∈ (P : Subgroup Q)) := by
        rw [hP, ← hP']; simp [hx]
      simpa using this
  obtain P2 := Classical.arbitrary (Sylow 2 Q)
  have hn2 : Nat.card (Sylow 2 Q) = 1 :=
    Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩
  exact caseV_d_not_simple_sylow_card_one P2 hn2 (by rw [hc2P P2]; omega)
    (by rw [hc2P P2, hcard]; omega) hs

/-- **Case Vd/VIc (Butler tex 2088-2109): `|Z(H)| = 2`.** A finite group `H` of order `120`
with a unique involution and simple central quotient `H ⧸ Z(H)` has center of order exactly `2`
(so `|H/Z(H)| = 60`). The unique involution is central (`isCentral_of_unique_involution`), giving
`2 ∣ |Z(H)|`; if `H/Z(H)` were cyclic then `H` would be abelian and `Z(H) = ⊤`, contradicting
simplicity, so `H/Z(H)` is nonabelian; and every candidate order `120/|Z(H)| ∈ {1,…,30}` for a
nonabelian simple quotient is excluded (primes give cyclic quotients; the composite orders
`4,6,10,12,15,20,30` admit no simple group), leaving `|H/Z(H)| = 60`. -/
lemma caseV_d_center_card_eq_two {H : Type*} [Group H] [Finite H] (hcard : Nat.card H = 120)
    (hinv : ∃! τ : H, orderOf τ = 2) (hsimple : IsSimpleGroup (H ⧸ center H)) :
    Nat.card (center H) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  -- unique involution is central; gives 2 ∣ |center H|
  obtain ⟨τ, hτ2, hτu⟩ := hinv
  have hτne1 : τ ≠ 1 := by intro h; rw [h, orderOf_one] at hτ2; exact absurd hτ2 (by norm_num)
  have hτsq : τ ^ 2 = 1 := by rw [← hτ2]; exact pow_orderOf_eq_one τ
  have huniq2 : ∀ g : H, g ^ 2 = 1 → g ≠ 1 → g = τ := by
    intro g hg2 hg1
    exact hτu g (orderOf_eq_prime hg2 hg1)
  have hτC : τ ∈ center H := Ch7GroupRecognition.isCentral_of_unique_involution hτsq hτne1 huniq2
  have h2dvd : 2 ∣ Nat.card (center H) := by
    have hoc : orderOf (⟨τ, hτC⟩ : center H) = 2 := by
      have htr : orderOf ((⟨τ, hτC⟩ : center H) : H) = orderOf (⟨τ, hτC⟩ : center H) :=
        orderOf_coe _
      rw [← htr]; exact hτ2
    rw [← hoc]; exact orderOf_dvd_natCard _
  -- |center| * |H/center| = 120
  have hmul : Nat.card (center H) * Nat.card (H ⧸ center H) = 120 := by
    have h := Subgroup.card_mul_index (center H)
    rw [hcard] at h; exact h
  -- H/center is not cyclic
  have hncyc : ¬ IsCyclic (H ⧸ center H) := by
    intro hcyc
    haveI := hcyc
    have hcomm : ∀ a b : H, a * b = b * a :=
      fun a b => (isMulCommutative_of_isCyclic_quotient_center_self (G := H)).is_comm.comm a b
    have htop : center H = ⊤ := by
      rw [eq_top_iff]; intro x _; rw [Subgroup.mem_center_iff]; intro g; exact hcomm g x
    have h1 : Nat.card (H ⧸ center H) = 1 := by
      rw [show Nat.card (H ⧸ center H) = (center H).index from rfl, htop, Subgroup.index_top]
    haveI := hsimple.toNontrivial
    have := Finite.one_lt_card (α := H ⧸ center H)
    omega
  -- n ∣ 60
  set n := Nat.card (H ⧸ center H) with hn_def
  have hn_pos : 0 < n := Nat.card_pos
  have hn_dvd60 : n ∣ 60 := by
    obtain ⟨k, hk⟩ := h2dvd
    have h2kn : 2 * (k * n) = 120 := by rw [← mul_assoc, ← hk]; exact hmul
    have hkn : k * n = 60 := by omega
    exact ⟨k, by rw [← hkn]; ring⟩
  -- enumerate divisors of 60
  have hcases : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 10 ∨ n = 12 ∨ n = 15
      ∨ n = 20 ∨ n = 30 ∨ n = 60 := by
    have hle : n ≤ 60 := Nat.le_of_dvd (by norm_num) hn_dvd60
    interval_cases n <;> omega
  -- rule out each proper divisor
  have h60 : n = 60 := by
    rcases hcases with h|h|h|h|h|h|h|h|h|h|h|h
    · exfalso; haveI := hsimple.toNontrivial
      have := Finite.one_lt_card (α := H ⧸ center H)
      rw [← hn_def] at this; omega
    · exact absurd (isCyclic_of_prime_card (α := H ⧸ center H) (p := 2)
        (by rw [← hn_def]; exact h)) hncyc
    · exact absurd (isCyclic_of_prime_card (α := H ⧸ center H) (p := 3)
        (by rw [← hn_def]; exact h)) hncyc
    · exact absurd (caseV_d_not_simple_two_mul_prime (Q := H ⧸ center H) (q := 2)
        (by rw [← hn_def]; omega)) (fun hh => hh hsimple)
    · exact absurd (isCyclic_of_prime_card (α := H ⧸ center H) (p := 5)
        (by rw [← hn_def]; exact h)) hncyc
    · exact absurd (caseV_d_not_simple_two_mul_prime (Q := H ⧸ center H) (q := 3)
        (by rw [← hn_def]; omega)) (fun hh => hh hsimple)
    · exact absurd (caseV_d_not_simple_two_mul_prime (Q := H ⧸ center H) (q := 5)
        (by rw [← hn_def]; omega)) (fun hh => hh hsimple)
    · exact absurd (caseV_d_not_simple_12 (Q := H ⧸ center H) (by rw [← hn_def]; exact h))
        (fun hh => hh hsimple)
    · exact absurd (caseV_d_not_simple_15 (Q := H ⧸ center H) (by rw [← hn_def]; exact h))
        (fun hh => hh hsimple)
    · exact absurd (caseV_d_not_simple_20 (Q := H ⧸ center H) (by rw [← hn_def]; exact h))
        (fun hh => hh hsimple)
    · exact absurd (caseV_d_not_simple_30 (Q := H ⧸ center H) (by rw [← hn_def]; exact h))
        (fun hh => hh hsimple)
    · exact h
  rw [h60] at hmul; omega

/-- (SORRY) **The sole remaining gap of Case Vd/VIc — Schur's theorem.** A finite group `H`
of order `120` with a unique involution and `H ⧸ Z(H) ≃* A₅` is `≅ SL(2, ZMod 5)`. Butler
(tex 2111) invokes this as "beyond the scope of this thesis", citing Schur: `A₅` is perfect with
Schur multiplier `H₂(A₅) = C₂`, so up to isomorphism it has exactly two central `C₂`-extensions —
the split one `A₅ × C₂` and the universal cover `SL(2,5) = 2I` (the binary icosahedral group).
Since `|H| = 120` forces `|Z(H)| = 2` (`caseV_d_center_card_eq_two`), `H` is one of these two, and
the *unique involution* hypothesis excludes the split extension `A₅ × C₂` (which has `15` further
involutions from `A₅`), leaving `H ≅ SL(2,5)`.

**Missing infrastructure:** mathlib has group cohomology `H²` (`RepresentationTheory.Homological.
GroupCohomology.LowDegree`) but no universal-central-extension / Schur-cover API and no computation
`H₂(A₅) = C₂`. A formalizable route: build the concrete perfect central `C₂`-extension `SL(2,5)`
of `A₅` as the universal cover, then show any perfect central `C₂`-extension of a perfect group is
a quotient of its universal cover — here an iso by order. All *other* content of Case Vd/VIc is
proven (`caseV_d_center_card_eq_two` and the assembly in `caseV_d_recognition`). -/
lemma caseV_d_schur_cover {H : Type*} [Group H] [Finite H] (hcard : Nat.card H = 120)
    (hinv : ∃! τ : H, orderOf τ = 2)
    (e : H ⧸ center H ≃* alternatingGroup (Fin 5)) :
    Isomorphic H SL(2, ZMod 5) := by
  sorry

/-- **Case Vd/VIc recognition (Butler tex 2088-2111): `|H| = 120` + unique involution + simple
central quotient `H ⧸ Z(H)` ⟹ `H ≅ SL(2, ZMod 5)`.** Reduces to two facts: `|Z(H)| = 2`
(`caseV_d_center_card_eq_two`, fully proven) so `|H/Z(H)| = 60`, whence `H ⧸ Z(H) ≃* A₅`
(`Ch7SimpleGroup60.isSimpleGroup_card_sixty_iso_alternating`); and Schur's theorem
(`caseV_d_schur_cover`, the sole remaining `sorry`) identifying the resulting perfect central
`C₂`-extension of `A₅` (with a unique involution) as `SL(2,5)`. The abstract statement (order
`120`, unique involution, simple quotient) is the reusable core shared by Case Vd and Case VIc,
each of which supplies a `Subgroup SL(2,F)` with `|Z| = 2`. -/
lemma caseV_d_recognition {H : Type*} [Group H] [Finite H] (hcard : Nat.card H = 120)
    (hinv : ∃! τ : H, orderOf τ = 2)
    (hsimple : IsSimpleGroup (H ⧸ center H)) :
    Isomorphic H SL(2, ZMod 5) := by
  have hZ2 : Nat.card (center H) = 2 := caseV_d_center_card_eq_two hcard hinv hsimple
  have h60 : Nat.card (H ⧸ center H) = 60 := by
    have hmul : Nat.card (center H) * Nat.card (H ⧸ center H) = 120 := by
      have h := Subgroup.card_mul_index (center H); rw [hcard] at h; exact h
    rw [hZ2] at hmul; omega
  obtain ⟨e⟩ := Ch7SimpleGroup60.isSimpleGroup_card_sixty_iso_alternating hsimple h60
  exact caseV_d_schur_cover hcard hinv e

/-- The center of a group `H` lies inside every maximal abelian subgroup: joining a maximal
abelian subgroup with the (central) `center H` keeps it abelian, so maximality forces equality. -/
lemma caseV_d_center_le_maximalAbelian {H : Type*} [Group H] (A : Subgroup H)
    (hA : IsMaximalAbelian A) : Subgroup.center H ≤ A := by
  have hAcomm : IsMulCommutative A := hA.1
  have hjoin : IsMulCommutative (Subgroup.center H ⊔ A : Subgroup H) :=
    IsComm_of_center_join_IsComm A hAcomm
  have hle : (Subgroup.center H ⊔ A : Subgroup H) ≤ A := hA.2 hjoin le_sup_right
  exact le_sup_left.trans hle

/-- **Case Vd (Butler tex 2088-2102): `G ⧸ Z` is simple.** With `|G| = 120` and `|Z| = 2`, so
`|G/Z| = 60`, this replaces Butler's element-order census by a Sylow argument. Bridge B1:
`|center ↥G| = 2` from `center ↥G ≤ A' ∩ B'` (`caseV_d_center_le_maximalAbelian`, orders `4` and
`10`) and the central `Z ≤ center ↥G` (order `2`). Bridge B2: the image `B̄` of `B' = B.subgroupOf
G` in `G/Z` is a Sylow-`5` (order `5`) that is not normal (else `B'` would be, contradicting
`|N_G(B')| = 20 ≠ 120` from `hB_relIndex`), so `n₅(G/Z) ≠ 1`. Then
`Ch7SimpleGroup60.isSimpleGroup_of_card_60_of_sylow5_ne_one` concludes. -/
lemma caseV_d_quotient_simple {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F]
    [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q) (ga gb k : ℕ)
    (A : Subgroup SL(2,F)) (hA_mem : A ∈ MaximalAbelianSubgroupsOf G)
    (hA_cyc : IsCyclic A) (hA_cop : Nat.Coprime (Nat.card A) p)
    (hA_card : Nat.card A = Nat.card (center SL(2,F)) * ga)
    (hA_relIndex : relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) = 2)
    (B : Subgroup SL(2,F)) (hB_mem : B ∈ MaximalAbelianSubgroupsOf G)
    (hB_cyc : IsCyclic B) (hB_cop : Nat.Coprime (Nat.card B) p)
    (hB_card : Nat.card B = Nat.card (center SL(2,F)) * gb)
    (hB_relIndex : relIndex (B.subgroupOf G) (normalizer (B.subgroupOf G : Set ↥G)) = 2)
    (K : Subgroup SL(2,F)) (hK_le : K ≤ G) (hK_cyc : IsCyclic K)
    (hK_card : Nat.card K = Nat.card (center SL(2,F)) * k)
    (hNQK : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G)
    (hQK_disj : Disjoint Q.toSubgroup (K.subgroupOf G))
    (hComplete : ∀ B' ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B' = A) ∨
      (∃ c ∈ G, conj c • B' = B) ∨ NumericClassEquation.IsSylowType p G B')
    (hp3 : p = 3) (hq3 : q = 3) (hga2 : ga = 2) (hgb5 : gb = 5) (hg60 : g = 60)
    (hkga : k = ga) (he2 : Nat.card (center SL(2,F)) = 2) :
    IsSimpleGroup (↥G ⧸ center ↥G) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hcard120G : Nat.card ↥G = 120 := by rw [hg, he2, hg60]
  -- B1: |center ↥G| = 2
  have hZc_le : (center SL(2,F)).subgroupOf G ≤ Subgroup.center ↥G := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro h
    apply Subgroup.subtype_injective G
    rw [_root_.map_mul, _root_.map_mul]
    have hgc : G.subtype x ∈ center SL(2,F) := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_center_iff.mp hgc (G.subtype h)
  have hZc_card : Nat.card ((center SL(2,F)).subgroupOf G) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe center_le_G).toEquiv, he2]
  have h2dvd : 2 ∣ Nat.card (Subgroup.center ↥G) := by
    have h := Subgroup.card_dvd_of_le hZc_le; rwa [hZc_card] at h
  have hcenA : Subgroup.center ↥G ≤ A.subgroupOf G := caseV_d_center_le_maximalAbelian _ hA_mem.1
  have hcenB : Subgroup.center ↥G ≤ B.subgroupOf G := caseV_d_center_le_maximalAbelian _ hB_mem.1
  have hcardA : Nat.card (A.subgroupOf G) = 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_mem.2).toEquiv, hA_card, he2, hga2]
  have hcardB : Nat.card (B.subgroupOf G) = 10 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_mem.2).toEquiv, hB_card, he2, hgb5]
  have hcen_dvd4 : Nat.card (Subgroup.center ↥G) ∣ 4 := by
    have h := Subgroup.card_dvd_of_le hcenA; rwa [hcardA] at h
  have hcen_dvd10 : Nat.card (Subgroup.center ↥G) ∣ 10 := by
    have h := Subgroup.card_dvd_of_le hcenB; rwa [hcardB] at h
  have hcen_dvd2 : Nat.card (Subgroup.center ↥G) ∣ 2 :=
    (Nat.dvd_gcd hcen_dvd4 hcen_dvd10).trans (by norm_num)
  have hZ2 : Nat.card (Subgroup.center ↥G) = 2 := Nat.dvd_antisymm hcen_dvd2 h2dvd
  -- |G/Z| = 60
  have hqcard : Nat.card (↥G ⧸ Subgroup.center ↥G) = 60 := by
    have h := Subgroup.card_mul_index (Subgroup.center ↥G)
    rw [hcard120G, hZ2] at h
    rw [← Subgroup.index_eq_card]; omega
  -- B2: n₅(G/Z) ≠ 1
  have hn5 : Nat.card (Sylow 5 (↥G ⧸ Subgroup.center ↥G)) ≠ 1 := by
    set π := QuotientGroup.mk' (Subgroup.center ↥G) with hπ
    set B' := B.subgroupOf G with hB'
    set Bbar := B'.map π with hBbar
    have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
    have hker : π.ker = Subgroup.center ↥G := QuotientGroup.ker_mk' _
    have hZleB' : Subgroup.center ↥G ≤ B' := hcenB
    have hcomap : Bbar.comap π = B' := by
      rw [hBbar, Subgroup.comap_map_eq_self (by rw [hker]; exact hZleB')]
    have hB'idx : B'.index = 12 := by
      have h := Subgroup.card_mul_index B'
      rw [hcardB, hcard120G] at h; omega
    have hBbaridx : Bbar.index = 12 := by
      have h : (Bbar.comap π).index = Bbar.index := Subgroup.index_comap_of_surjective _ hsurj
      rw [hcomap, hB'idx] at h; omega
    have hBbarcard : Nat.card Bbar = 5 := by
      have h := Subgroup.card_mul_index Bbar
      rw [hqcard, hBbaridx] at h; omega
    have hfact60 : (Nat.card (↥G ⧸ Subgroup.center ↥G)).factorization 5 = 1 := by
      rw [hqcard, show (60 : ℕ) = 5 * 12 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_self (by norm_num),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    -- B' not normal (normalizer would be ⊤, but relIndex says 2 ≠ 12)
    have hB'_not_normal : ¬ B'.Normal := by
      intro hn
      have htop : normalizer (B' : Set ↥G) = ⊤ := @Subgroup.normalizer_eq_top _ _ B' hn
      have h := hB_relIndex
      rw [htop, Subgroup.relIndex_top_right] at h
      omega
    have hBbar_not_normal : ¬ Bbar.Normal := by
      intro hn
      exact hB'_not_normal (hcomap ▸ hn.comap π)
    intro hn5eq1
    haveI : Subsingleton (Sylow 5 (↥G ⧸ Subgroup.center ↥G)) :=
      (Nat.card_eq_one_iff_unique.mp hn5eq1).1
    let PB : Sylow 5 (↥G ⧸ Subgroup.center ↥G) :=
      Sylow.ofCard Bbar (by rw [hBbarcard, hfact60]; norm_num)
    have hcoe : (PB : Subgroup (↥G ⧸ Subgroup.center ↥G)) = Bbar := Sylow.coe_ofCard _ _
    have hnorm := Sylow.normal_of_subsingleton PB
    rw [hcoe] at hnorm
    exact hBbar_not_normal hnorm
  exact Ch7SimpleGroup60.isSimpleGroup_of_card_60_of_sylow5_ne_one hqcard hn5

/-- Butler tex 2046-2054 (Case Va root-count crux): in a field `F`, two `n`-element finsets whose
members are all roots of `Xⁿ - 1` coincide (both equal `nthRootsFinset n 1`, which has `≤ n`
elements). Applied with `n = q - 1` to `𝕄 = {ω : d_ω ∈ K}` and `𝔽_q^*` — both of cardinality
`q - 1`, both consisting of `(q-1)`-th roots of unity — this gives `𝕄 = 𝔽_q^*`, the step that
distinguishes Case Va from Vb (where only `ω²` is forced to be a `(q-1)`-th root). -/
lemma caseV_finset_eq_of_card_of_pow_eq_one {F : Type*} [Field F] {n : ℕ} (hn : 0 < n)
    (S T : Finset F)
    (hS : ∀ x ∈ S, x ^ n = 1) (hT : ∀ x ∈ T, x ^ n = 1)
    (hScard : S.card = n) (hTcard : T.card = n) : S = T := by
  classical
  set R := nthRootsFinset n (1 : F) with hR
  have hSsub : S ⊆ R := fun x hx => (mem_nthRootsFinset hn 1).mpr (hS x hx)
  have hTsub : T ⊆ R := fun x hx => (mem_nthRootsFinset hn 1).mpr (hT x hx)
  have hRcard : R.card ≤ n := by
    rw [hR, nthRootsFinset]
    exact (Multiset.toFinset_card_le _).trans (card_nthRoots n 1)
  have hSR : S = R := Finset.eq_of_subset_of_card_le hSsub (by rw [hScard]; exact hRcard)
  have hTR : T = R := Finset.eq_of_subset_of_card_le hTsub (by rw [hTcard]; exact hRcard)
  rw [hSR, hTR]

/-- Order of `SL(2, 𝔽_q)` for `q = pⁿ` (Butler tex 2054, "Proposition ordersl2q":
`|SL(2,𝔽_q)| = q(q²-1)`), specialised to the `GaloisField` realisation of `𝔽_q`. Feeds the final
cardinality match `|G̃| = |SL(2,𝔽_q)|` concluding Cases Va (and, mutatis mutandis, Vb). -/
lemma caseV_card_SL2_GaloisField {p : ℕ} [Fact (Nat.Prime p)] (n : ℕ+) :
    Nat.card SL(2, GaloisField p n.val) = ((p ^ (n : ℕ)) ^ 2 - 1) * p ^ (n : ℕ) := by
  haveI : Fintype (GaloisField p n.val) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p n.val) = p ^ (n : ℕ) := by
    rw [Fintype.card_eq_nat_card]; exact GaloisField.card p n.val n.pos.ne'
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  have hq1 : p ^ (n : ℕ) > 1 := Nat.one_lt_pow n.pos.ne' hp1
  rw [Nat.card_eq_fintype_card, SL_card hcard hq1]

/- ==========================================================================================
`caseV_geo_*` — the algebraic heart of Steps 1-3 of the shared `caseV_a`/`caseV_b` route
(Butler tex 1953-2038), proved without transcribing the projective-line argument. The Q-side
of Step 1 (`Q ⊆ S`, `N(Q) ⊆ L`) is supplied by `exists_conj_Sylow_eq_S_inf_and_normalizer_le_L`
(Ch6); these lemmas discharge the anti-diagonal `y` of Step 2 and the double-coset disjointness
of Step 3, and are frame-agnostic so both `caseV_a` and `caseV_b` consume them next wave.
Residual (not yet mechanised): the `K ⊆ D` refinement and `u = t₁` of Step 1, and the covering
half of the Step-3 partition (the `(q+1)|N(Q)| = |G̃|` cardinality count). -/
section CaseVGeo
variable {F : Type*} [Field F]

/-- tex `onemore` (2017-2020): the (0,1) (top-right) entry of the general element
`t_λ d_ω y t_μ` of the double coset `N(Q) y Q`, where `y = d_ρ w`, is `ω ρ`. -/
lemma caseV_geo_onemore_topRight (lam mu : F) (om rho : Fˣ) :
    (s lam * d om * (d rho * w) * s mu).1 0 1 = (om : F) * (rho : F) := by
  rw [d_mul_w_eq_dw]
  simp [s, d, dw, Matrix.mul_apply, Fin.sum_univ_two]

/-- tex 2022: since `ω, ρ ∈ F^*`, the element `t_λ d_ω y t_μ` has nonzero top-right entry,
hence is not lower-triangular, i.e. lies outside `H = L F ⊇ N(Q)`. -/
lemma caseV_geo_onemore_notMem_L [DecidableEq F] (lam mu : F) (om rho : Fˣ) :
    s lam * d om * (d rho * w) * s mu ∉ SpecialSubgroups.L F := by
  rw [SpecialSubgroups.mem_L_iff_lower_triangular, MatrixShapes.IsLowerTriangular,
    caseV_geo_onemore_topRight]
  exact mul_ne_zero (Units.ne_zero om) (Units.ne_zero rho)

/-- tex `mattr` matrix (2029-2033): the conjugate `y t_λ y⁻¹` (with `y = d_ρ w`) is the upper
shear `!![1, -ρ²λ; 0, 1]`; its top-right entry `-ρ²λ` drives the `ω = -ρλ` identity of Step 4. -/
lemma caseV_geo_conj_shear (lam : F) (rho : Fˣ) :
    ((d rho * w) * s lam * (d rho * w)⁻¹).1 = !![1, -(rho:F)^2 * lam; 0, 1] := by
  simp only [d_mul_w_eq_dw]
  apply Matrix.fin_two_ext <;>
    (simp [s, dw, Matrix.mul_apply, Fin.sum_univ_two]; try ring)

/-- A lower-triangular `SL(2,F)` matrix has invertible diagonal: `n₀₀·n₁₁ = 1`. -/
lemma caseV_geo_lowerTri_diag (n : SL(2,F)) (hn : n.1 0 1 = 0) :
    n.1 0 0 * n.1 1 1 = 1 := by
  have h := n.property
  rw [Matrix.det_fin_two, hn] at h
  linear_combination h

/-- Step 3 core (tex 2016-2022), frame-agnostic: for *any* lower-triangular `n, q ∈ SL(2,F)`
and `ρ ∈ F^*`, the double-coset element `n · (d_ρ w) · q` has top-right entry `n₀₀ ρ q₁₁`. -/
lemma caseV_geo_doset_topRight (n q : SL(2,F)) (hn : n.1 0 1 = 0) (hq : q.1 0 1 = 0) (rho : Fˣ) :
    (n * (d rho * w) * q).1 0 1 = n.1 0 0 * (rho : F) * q.1 1 1 := by
  rw [show n * (d rho * w) * q = n * dw rho * q from by rw [d_mul_w_eq_dw]]
  show (n.1 * (dw rho).1 * q.1) 0 1 = _
  simp only [dw, Matrix.mul_apply, Fin.sum_univ_two, Fin.isValue,
    of_apply, cons_val', cons_val_zero, cons_val_one, cons_val_fin_one, empty_val', hn, hq]
  ring

/-- Step 3 disjointness (tex 2016-2022): with `N, Q` lower-triangular (`≤ L F`, as furnished by
`exists_conj_Sylow_eq_S_inf_and_normalizer_le_L` in the normalized frame), every element of the
double coset `N · (d_ρ w) · Q` lies outside `H = L F`, so `N (d_ρ w) Q` is disjoint from `N`. -/
lemma caseV_geo_doset_notMem_L [DecidableEq F] {N Q : Subgroup SL(2,F)}
    (hN : N ≤ SpecialSubgroups.L F) (hQ : Q ≤ SpecialSubgroups.L F) (rho : Fˣ)
    {n : SL(2,F)} (hn : n ∈ N) {q : SL(2,F)} (hq : q ∈ Q) :
    n * (d rho * w) * q ∉ SpecialSubgroups.L F := by
  have hnL : n.1 0 1 = 0 := (SpecialSubgroups.mem_L_iff_lower_triangular).mp (hN hn)
  have hqL : q.1 0 1 = 0 := (SpecialSubgroups.mem_L_iff_lower_triangular).mp (hQ hq)
  rw [SpecialSubgroups.mem_L_iff_lower_triangular, MatrixShapes.IsLowerTriangular,
    caseV_geo_doset_topRight n q hnL hqL]
  have hn00 : n.1 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one (caseV_geo_lowerTri_diag n hnL)
  have hq11 : q.1 1 1 ≠ 0 := right_ne_zero_of_mul_eq_one (caseV_geo_lowerTri_diag q hqL)
  exact mul_ne_zero (mul_ne_zero hn00 (Units.ne_zero rho)) hq11

/-- Packaged Step-3 disjointness as a `Disjoint` of the double coset with `N` (tex `gsplit`,
disjoint half). -/
lemma caseV_geo_doset_disjoint_L [DecidableEq F] {N Q : Subgroup SL(2,F)}
    (hN : N ≤ SpecialSubgroups.L F) (hQ : Q ≤ SpecialSubgroups.L F) (rho : Fˣ) :
    Disjoint (DoubleCoset.doubleCoset (d rho * w) (N : Set SL(2,F)) (Q : Set SL(2,F)))
      (N : Set SL(2,F)) := by
  rw [Set.disjoint_left]
  rintro x hxD hxN
  obtain ⟨n, hn, q, hq, rfl⟩ := DoubleCoset.mem_doubleCoset.mp hxD
  exact caseV_geo_doset_notMem_L hN hQ rho hn hq (hN hxN)

/-- Step 2, anti-diagonal form (tex 1989-1991): any element of `N_{SL₂}(D) = DW F` that is not
diagonal is of the form `y = d_ρ w`. -/
lemma caseV_geo_y_eq_dw {y : SL(2,F)} (hy : y ∈ SpecialSubgroups.DW F)
    (hy' : y ∉ SpecialSubgroups.D F) : ∃ rho : Fˣ, y = d rho * w := by
  rcases hy with (⟨δ, rfl⟩ | ⟨δ, rfl⟩)
  · exact absurd SpecialSubgroups.d_mem_D hy'
  · exact ⟨δ, rfl⟩

/-- Step 2, `y ∉ D` (tex 1971-1988, algebraic replacement of the projective interchange argument):
an element `y` that inverts a noncentral diagonal `x` (`y x y⁻¹ = x⁻¹`) cannot itself be diagonal,
since `D` is abelian and would force `x = x⁻¹`, i.e. `x` central. -/
lemma caseV_geo_inverting_notMem_D {x y : SL(2,F)} (hx : x ∈ SpecialSubgroups.D F)
    (hxnc : x ∉ SpecialSubgroups.Z F) (hinv : y * x * y⁻¹ = x⁻¹) :
    y ∉ SpecialSubgroups.D F := by
  rintro ⟨δ', rfl⟩
  obtain ⟨δ, rfl⟩ := hx
  have hcomm : d δ' * d δ * (d δ')⁻¹ = d δ := by
    rw [inv_d_eq_d_inv, d_mul_d_eq_d_mul, d_mul_d_eq_d_mul, mul_comm δ' δ, mul_assoc,
      mul_inv_cancel, mul_one]
  rw [hcomm, inv_d_eq_d_inv, d_eq_d_iff] at hinv
  apply hxnc
  rw [SpecialSubgroups.mem_Z_iff]
  have hsq : δ ^ 2 = 1 ^ 2 := by
    rw [one_pow, pow_two]; nth_rewrite 1 [hinv]; exact inv_mul_cancel δ
  rcases Units.eq_or_eq_neg_of_sq_eq_sq δ 1 hsq with h1 | h1
  · exact Or.inl (by rw [h1, d_one_eq_one])
  · exact Or.inr (by rw [h1, d_neg_one_eq_neg_one])

/-- Step 2, packaged (tex 1971-1991): if `K ≤ D` with `|K| > 2`, `x ∈ K` noncentral, and
`y ∈ N_{SL₂}(K)` inverts `x` (`y x y⁻¹ = x⁻¹`, from Butler 6.8(iv)), then `y = d_ρ w`. Uses
`normalizer_subgroup_D_eq_DW_of_two_lt_card` (`N(K) = DW`) to place `y ∈ DW`, then the two
algebraic facts above. This is the full Step-2 output consumed by Step 3. -/
lemma caseV_geo_y_eq_dw_of_inverting [DecidableEq F] {K : Subgroup SL(2,F)}
    (hKD : K ≤ SpecialSubgroups.D F) (hK2 : 2 < Nat.card K) {x y : SL(2,F)}
    (hxK : x ∈ K) (hxnc : x ∉ SpecialSubgroups.Z F) (hyN : y ∈ normalizer K)
    (hinv : y * x * y⁻¹ = x⁻¹) : ∃ rho : Fˣ, y = d rho * w := by
  have hyDW : y ∈ SpecialSubgroups.DW F := by
    rw [← normalizer_subgroup_D_eq_DW_of_two_lt_card hK2 hKD]; exact hyN
  exact caseV_geo_y_eq_dw hyDW (caseV_geo_inverting_notMem_D (hKD hxK) hxnc hinv)

end CaseVGeo

/- ==========================================================================================
`caseV` Step-5 subfield realisation (Butler tex 2040-2054), frame-independent and shared by Cases
Va/Vb. The fixed field `R F p n` of the `n`-th Frobenius is the copy of `𝔽_q = 𝔽_{pⁿ}` sitting
inside the ambient algebraically closed `F`; these two lemmas give its cardinality (`= q`) and its
ring isomorphism with `GaloisField p n`, so `SL(2, R F p n)` transports to `SL(2, GaloisField p n)`
via `SL2_mulEquiv_of_ringEquiv`. -/

/-- The subfield `R F p n` (fixed field of the `n`-th Frobenius) has exactly `pⁿ` elements: its
carrier is the root set of the separable, fully-split (`F` algebraically closed) polynomial
`Xᵖ^ⁿ - X`, whose `pⁿ` roots are counted by `card_rootSet_eq_natDegree`. -/
lemma caseV_card_R {F : Type*} [Field F] [IsAlgClosed F] {p : ℕ} [Fact (Nat.Prime p)]
    [CharP F p] (n : ℕ+) : Nat.card (R F p n) = p ^ (n : ℕ) := by
  classical
  set f : F[X] := X ^ (p ^ (n : ℕ)) - X with hf
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hsep : f.Separable :=
    galois_poly_separable (K := F) p (p ^ (n : ℕ)) (dvd_pow_self p n.pos.ne')
  have hsplit : Splits (f.map (algebraMap F F)) := IsAlgClosed.splits (f.map (algebraMap F F))
  have hnd : f.natDegree = p ^ (n : ℕ) :=
    FiniteField.X_pow_card_pow_sub_X_natDegree_eq F n.pos.ne' hp1
  have hcard_root : Fintype.card (f.rootSet F) = p ^ (n : ℕ) := by
    rw [card_rootSet_eq_natDegree hsep hsplit, hnd]
  have hfne : f ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hnd; exact (pow_pos (by omega : 0 < p) (n : ℕ)).ne' hnd.symm
  have hset : (R F p n : Set F) = f.rootSet F := by
    ext x
    simp only [SetLike.mem_coe, R, RingHom.mem_eqLocusField, RingHom.id_apply]
    rw [Polynomial.mem_rootSet]
    simp only [hf, map_sub, aeval_X_pow, aeval_X, sub_eq_zero]
    exact ⟨fun h => ⟨hfne, h⟩, fun h => h.2⟩
  have key : Nat.card (R F p n) = Fintype.card (f.rootSet F) :=
    (Nat.card_congr (Equiv.setCongr hset)).trans Nat.card_eq_fintype_card
  rw [key, hcard_root]

/-- Step-5 subfield realisation (frame-independent): the fixed field `R F p n` is ring-isomorphic
to `GaloisField p n`, via `GaloisField.algEquivGaloisField` applied to `caseV_card_R`. -/
lemma caseV_ringEquiv_R_GaloisField {F : Type*} [Field F] [IsAlgClosed F] {p : ℕ}
    [Fact (Nat.Prime p)] [CharP F p] (n : ℕ+) :
    Nonempty (R F p n ≃+* GaloisField p n.val) := by
  haveI hchar : CharP (R F p n) p := CharP.subring F p (R F p n).toSubring
  letI : Algebra (ZMod p) (R F p n) := (ZMod.castHom (dvd_refl p) (R F p n)).toAlgebra
  exact ⟨(GaloisField.algEquivGaloisField p n.val (caseV_card_R n)).toRingEquiv⟩

/-- (SORRY) Case Va, Butler tex 1953-2054 (`i = 1` or `e = 1`, so `ei = 2`, `|K| = q - 1`):
`G ≅ SL(2, 𝔽_q)` with `𝔽_q = GaloisField p n`, `q = pⁿ`.

ROUTE MAP (the geometric normalization of Steps 1-3 is shared verbatim with `caseV_b`).

* **Step 1 — projective-line normalization (tex 1953-1985).** By Butler 6.7 each noncentral
  element of the Sylow `Q` shares one fixed point `P₁ ∈ ℒ` on the projective line, and each
  noncentral element of `K` fixes `P₁` and one other point `P₂` (6.8(v)). For noncentral `u ∈ Q`
  set `P₃ = u • P₂`; then `P₁, P₂, P₃` are distinct. Triple transitivity (Ch5
  `SL2_triptrans_on_projectivization`, Butler 6.6) supplies `v ∈ L` sending `P₁,P₂,P₃` to
  `R₁ = ⟦0,1⟧`, `R₂ = ⟦1,0⟧`, `R₃ = ⟦1,1⟧`. Passing to `G̃ = v G v⁻¹` (WLOG, `G̃` conjugate to
  `G`): `vQv⁻¹` fixes `R₁` and has order-`p` noncentral elements, so lands in the lower shears
  `T` (repo `s`/`S`); `vKv⁻¹` fixes `R₁, R₂` so lands in the diagonals `D` (repo `d`); and the
  `R₂ ↦ R₃` computation pins `u = t₁`. Net: `Q ⊆ T`, `K ⊆ D`, `u = t₁`.
* **Step 2 — the anti-diagonal `y` (tex 1987-2011).** Let `x` generate `K`; by 6.8(iv) pick
  `y ∈ N_G̃(K) ∖ K` with `y x = x⁻¹ y`. Since `x` fixes `R₁`, `y` maps `{R₁,R₂}` to itself;
  `y R₁ = R₁` would force `y ∈ D` (contradiction, `D` centralises `x`), so `y` interchanges
  `R₁ ↔ R₂`, whence `y = d_ρ w = !![0, ρ; -ρ⁻¹, 0]` is anti-diagonal (repo `d ρ * w`).
* **Step 3 — double-coset partition (tex 2013-2038).** Counting right cosets,
  `[N_G̃(Q) y Q : N_G̃(Q)] = [Q : Q ∩ y⁻¹ N_G̃(Q) y] = q` (the intersection is trivial as only
  `1 ∈ Q` fixes `R₂`), so `|N_G̃(Q) y Q| = q·|N_G̃(Q)|`. The product `t_λ d_ω y t_μ` has nonzero
  top-right entry (tex `onemore`) hence lies outside `H = Stab(R₁)` (lower-triangulars) ⊇ `N_G̃(Q)`,
  so `N_G̃(Q) y Q ∩ N_G̃(Q) = ∅`; and `(q+1)|N_G̃(Q)| = (q+1)·e·q·g₁ = e·i·q·(q²-1)/2 = |G̃|`.
  Therefore `G̃ = N_G̃(Q) y Q ⊍ N_G̃(Q)` (tex `gsplit`).
* **Step 4 — `𝕄 = 𝔽_q^*` (tex 2040-2054, Va-specific).** Set `ℕ = {λ : t_λ ∈ Q}`,
  `𝕄 = {ω : d_ω ∈ K}`. For `t_λ ∈ Q ∖ Z`, `y t_λ y⁻¹ ∉ H` lands in `N_G̃(Q) y Q`; equating
  top-right entries gives `ω = -ρλ` (tex `mattr`). Taking `λ = -1` shows `d_ρ ∈ K`, so `y` may be
  replaced by `w` (`ρ = 1`), simplifying to `ω = -λ` (`mattr2`). Since `ei = 2` and `|K| = q-1`,
  every `ω ∈ 𝕄` is a `(q-1)`-th root of unity; the subfield `𝔽_q = R F p n` (repo `R`, tex 1351
  `subfield`) contributes `q-1` such roots via `𝔽_q^*`. Both sets have cardinality `q-1`, so
  `𝕄 = 𝔽_q^*` by `caseV_finset_eq_of_card_of_pow_eq_one`; with `mattr2` and `0 ∈ ℕ`, `ℕ = 𝔽_q`.
* **Step 5 — conclusion (tex 2054).** Every element of `G̃` is `t_λ d_ω` or `t_λ d_ω w t_μ` with
  `λ, μ ∈ 𝔽_q`, `ω ∈ 𝔽_q^*`, so `G̃ ⊆ SL(2, 𝔽_q)`; as
  `|SL(2, 𝔽_q)| = q(q²-1) = |G̃|` (`caseV_card_SL2_GaloisField`), `G̃ = SL(2, 𝔽_q)`. Conjugacy
  `G̃ = vGv⁻¹` and the subfield realisation `R F p n ≃* GaloisField p n` give
  `G ≅ SL(2, GaloisField p n)` (`m := n`).

RESIDUALS (multi-session; not yet mechanised): Steps 1-3 (the entire projective-line normalization
and double-coset partition) must be transcribed through Ch5's `Projectivization` /
`SL2_triptrans_on_projectivization` API — the largest block, and shared with `caseV_b`; Step 4's
identification of the abstract `𝕄`, `ℕ` with concrete `Finset`s and of `𝔽_q^*` with `(R F p n)ˣ`;
and Step 5's subfield iso `R F p n ≃* GaloisField p n` plus the `SL(2,·)` transport
(`SL2_mulEquiv_of_ringEquiv`). The two helpers above (`caseV_finset_eq_of_card_of_pow_eq_one`,
`caseV_card_SL2_GaloisField`) discharge the root-count crux (Step 4) and the final cardinality
match (Step 5). -/
lemma caseV_a {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F]
    [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q ga gb k i n : ℕ)
    (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q)
    (A : Subgroup SL(2,F)) (hA_mem : A ∈ MaximalAbelianSubgroupsOf G)
    (hA_cyc : IsCyclic A) (hA_cop : Nat.Coprime (Nat.card A) p)
    (hA_card : Nat.card A = Nat.card (center SL(2,F)) * ga)
    (hA_relIndex : relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) = 2)
    (B : Subgroup SL(2,F)) (hB_mem : B ∈ MaximalAbelianSubgroupsOf G)
    (hB_cyc : IsCyclic B) (hB_cop : Nat.Coprime (Nat.card B) p)
    (hB_card : Nat.card B = Nat.card (center SL(2,F)) * gb)
    (hB_relIndex : relIndex (B.subgroupOf G) (normalizer (B.subgroupOf G : Set ↥G)) = 2)
    (K : Subgroup SL(2,F)) (hK_le : K ≤ G) (hK_cyc : IsCyclic K)
    (hK_card : Nat.card K = Nat.card (center SL(2,F)) * k)
    (hNQK : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G)
    (hQK_disj : Disjoint Q.toSubgroup (K.subgroupOf G))
    (hComplete : ∀ B' ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B' = A) ∨
      (∃ c ∈ G, conj c • B' = B) ∨ NumericClassEquation.IsSylowType p G B')
    (hkga : k = ga) (hga_ge : 2 ≤ ga) (hgb_ge : 2 ≤ gb)
    (hqpow : q = p ^ n) (hn0 : n ≠ 0) (hq4 : 4 ≤ q)
    (hei : Nat.card (center SL(2,F)) * i = 2)
    (hshape1 : 2 * ga = i * (q - 1)) (hshape2 : 2 * gb = i * (q + 1))
    (hshape3 : 2 * g = i * (q * (q ^ 2 - 1))) :
    ∃ m : ℕ+, Isomorphic G SL(2, GaloisField p m.val) := by
  sorry

section CaseVb

variable {k : ℕ+}

lemma caseV_vb_ringHom_inj : Function.Injective (GaloisField_ringHom p k) := by
  unfold GaloisField_ringHom
  exact RingHom.injective _

lemma caseV_vb_monoidHom_inj : Function.Injective (@SL2_monoidHom_SL2 p _ k) := by
  unfold SL2_monoidHom_SL2
  intro A B hAB
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have hc := congrArg (fun M : SL(2, GaloisField p (2*k.val)) =>
      (M : Matrix (Fin 2) (Fin 2) (GaloisField p (2*k.val))) i j) hAB
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at hc
  exact RingHom.injective _ hc

/-- Entry-access: the (i,j) entry of `SL2_monoidHom_SL2 A` is `GaloisField_ringHom` applied to
the (i,j) entry of `A`. -/
lemma caseV_vb_monoidHom_apply_entry (A : SL(2, GaloisField p k.val)) (i j : Fin 2) :
    (SL2_monoidHom_SL2 A : Matrix (Fin 2) (Fin 2) (GaloisField p (2*k.val))) i j
      = GaloisField_ringHom p k ((A : Matrix (Fin 2) (Fin 2) (GaloisField p k.val)) i j) := by
  unfold SL2_monoidHom_SL2 GaloisField_ringHom
  rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  rfl

/-- The image `M = SL2_monoidHom_SL2 '' SL(2,𝔽_q)` has the cardinality of `SL(2,𝔽_q)`. -/
lemma caseV_vb_card_image :
    Nat.card (Subgroup.map (@SL2_monoidHom_SL2 p _ k) ⊤)
      = Nat.card SL(2, GaloisField p k.val) := by
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective ⊤ _ caseV_vb_monoidHom_inj).toEquiv]
  exact Nat.card_congr (Subgroup.topEquiv).toEquiv

lemma caseV_vb_d_pi_notMem (π : (GaloisField p (2*k.val))ˣ) (hπ : SL2_join_d_pi_spec p k π) :
    d π ∉ Subgroup.map (@SL2_monoidHom_SL2 p _ k) ⊤ := by
  intro hmem
  rw [Subgroup.mem_map] at hmem
  obtain ⟨A, -, hA⟩ := hmem
  apply hπ.1
  refine ⟨(A : Matrix (Fin 2) (Fin 2) (GaloisField p k.val)) 0 0, ?_⟩
  have hentry : (SL2_monoidHom_SL2 A : Matrix (Fin 2) (Fin 2) (GaloisField p (2*k.val))) 0 0
      = (d π : Matrix (Fin 2) (Fin 2) (GaloisField p (2*k.val))) 0 0 := by rw [hA]
  rw [caseV_vb_monoidHom_apply_entry] at hentry
  rw [hentry]
  simp [d]

lemma caseV_vb_d_pi_sq_mem (π : (GaloisField p (2*k.val))ˣ) (hπ : SL2_join_d_pi_spec p k π) :
    (d π)^2 ∈ Subgroup.map (@SL2_monoidHom_SL2 p _ k) ⊤ := by
  obtain ⟨c, hc⟩ := hπ.2
  have hcne : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact (pow_ne_zero 2 (Units.ne_zero π)) hc.symm
  set γ : (GaloisField p k.val)ˣ := Units.mk0 c hcne with hγ
  rw [Subgroup.mem_map]
  refine ⟨d γ, Subgroup.mem_top _, ?_⟩
  have hsq : (d π)^2 = d (π^2) := by rw [sq, d_mul_d_eq_d_mul, sq]
  rw [hsq]
  apply Subtype.ext
  refine Matrix.fin_two_ext ?_ ?_ ?_ ?_
  · rw [caseV_vb_monoidHom_apply_entry]
    simp only [d, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val_zero, hγ,
      Units.val_mk0, Units.val_pow_eq_pow_val]
    exact hc
  · rw [caseV_vb_monoidHom_apply_entry]
    simp only [d, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact map_zero _
  · rw [caseV_vb_monoidHom_apply_entry]
    simp only [d, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    exact map_zero _
  · rw [caseV_vb_monoidHom_apply_entry]
    simp only [d, Matrix.SpecialLinearGroup.coe_mk, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Units.val_pow_eq_pow_val, hγ, Units.val_mk0]
    rw [map_inv₀]
    exact congrArg (·⁻¹) hc

-- range of the ring hom is closed under inverse
lemma caseV_vb_range_inv {x : GaloisField p (2*k.val)}
    (hx : x ∈ Set.range (GaloisField_ringHom p k)) :
    x⁻¹ ∈ Set.range (GaloisField_ringHom p k) := by
  obtain ⟨a, ha⟩ := hx
  exact ⟨a⁻¹, by rw [map_inv₀]; exact congrArg (·⁻¹) ha⟩

/-- Conjugation of `Y` by the diagonal `d ρ` scales the off-diagonal entries by `ρ^2`, `ρ^{-2}`. -/
lemma caseV_vb_conj_formula (ρ : (GaloisField p (2*k.val))ˣ) (Y : SL(2, GaloisField p (2*k.val))) :
    ((d ρ * Y * (d ρ)⁻¹ : SL(2, GaloisField p (2*k.val))) :
      Matrix (Fin 2) (Fin 2) (GaloisField p (2*k.val)))
      = !![Y.1 0 0, (ρ:GaloisField p (2*k.val))^2 * Y.1 0 1;
           ((ρ:GaloisField p (2*k.val))^2)⁻¹ * Y.1 1 0, Y.1 1 1] := by
  rw [inv_d_eq_d_inv]
  refine Matrix.fin_two_ext ?_ ?_ ?_ ?_ <;>
    simp only [Matrix.SpecialLinearGroup.coe_mul, d, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Units.val_inv_eq_inv_val, Matrix.cons_val', Matrix.empty_val',
      Matrix.cons_val_fin_one] <;> field_simp <;> ring

lemma caseV_vb_dpi_mem_normalizer (π : (GaloisField p (2*k.val))ˣ) (hπ : SL2_join_d_pi_spec p k π) :
    d π ∈ normalizer (Subgroup.map (@SL2_monoidHom_SL2 p _ k) ⊤) := by
  rw [mem_normalizer_iff_map_conj_eq]
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hxM, rfl⟩ := hy
    rw [Subgroup.mem_map] at hxM
    obtain ⟨A, -, rfl⟩ := hxM
    obtain ⟨c, hc⟩ := hπ.2
    have hcne : c ≠ 0 := by
      intro h; rw [h, map_zero] at hc; exact (pow_ne_zero 2 (Units.ne_zero π)) hc.symm
    have hdetA : (A : Matrix (Fin 2) (Fin 2) (GaloisField p k.val)) 0 0
        * (A : Matrix (Fin 2) (Fin 2) (GaloisField p k.val)) 1 1
        - (A : Matrix (Fin 2) (Fin 2) (GaloisField p k.val)) 0 1
        * (A : Matrix (Fin 2) (Fin 2) (GaloisField p k.val)) 1 0 = 1 := by
      have hA := A.property; rw [Matrix.det_fin_two] at hA; exact hA
    refine ⟨⟨!![A.1 0 0, c * A.1 0 1; c⁻¹ * A.1 1 0, A.1 1 1], ?_⟩, Subgroup.mem_top _, ?_⟩
    · rw [Matrix.det_fin_two]
      simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one]
      field_simp
      linear_combination hdetA
    · have hf : (MulAut.conj (d π) :
          SL(2, GaloisField p (2*k.val)) →* SL(2, GaloisField p (2*k.val)))
          (SL2_monoidHom_SL2 A) = d π * SL2_monoidHom_SL2 A * (d π)⁻¹ := rfl
      rw [hf]
      apply Subtype.ext
      rw [caseV_vb_conj_formula]
      refine Matrix.fin_two_ext ?_ ?_ ?_ ?_ <;>
        rw [caseV_vb_monoidHom_apply_entry] <;>
        simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, map_mul, map_inv₀, hc,
          caseV_vb_monoidHom_apply_entry] <;> rfl
  · apply le_of_eq
    exact Nat.card_congr (Subgroup.equivMapOfInjective (Subgroup.map (@SL2_monoidHom_SL2 p _ k) ⊤)
      (MulAut.conj (d π) : SL(2, GaloisField p (2*k.val)) →* SL(2, GaloisField p (2*k.val)))
      (MulEquiv.injective _)).toEquiv

lemma caseV_vb_card_SL2_join_d (π : (GaloisField p (2*k.val))ˣ) (hπ : SL2_join_d_pi_spec p k π) :
    Nat.card (SL2_join_d p k π) = 2 * Nat.card SL(2, GaloisField p k.val) := by
  set M := Subgroup.map (@SL2_monoidHom_SL2 p _ k) ⊤ with hM
  have hnorm : d π ∈ normalizer M := caseV_vb_dpi_mem_normalizer π hπ
  have hcl_le : Subgroup.closure {d π} ≤ normalizer M := by
    rw [Subgroup.closure_le]; intro x hx
    rw [Set.mem_singleton_iff] at hx; subst hx; exact hnorm
  have hJ : SL2_join_d p k π = M ⊔ Subgroup.closure {d π} := rfl
  have hdecomp : (↑(M ⊔ Subgroup.closure {d π}) : Set SL(2, GaloisField p (2*k.val)))
      = ↑M * ↑(Subgroup.closure {d π}) :=
    Subgroup.coe_mul_of_right_le_normalizer_left M (Subgroup.closure {d π}) hcl_le
  have hs2 : (d π ^ (2:ℤ)) ∈ M := by
    rw [show (d π : SL(2, GaloisField p (2*k.val))) ^ (2:ℤ) = (d π) ^ 2 from by
      rw [show (2:ℤ) = ((2:ℕ):ℤ) from rfl, zpow_natCast]]
    exact caseV_vb_d_pi_sq_mem π hπ
  have hz : ∀ z ∈ Subgroup.closure ({d π} : Set SL(2, GaloisField p (2*k.val))),
      z ∈ M ∨ z * d π ∈ M := by
    intro z hzmem
    rw [Subgroup.mem_closure_singleton] at hzmem
    obtain ⟨n, rfl⟩ := hzmem
    rcases Int.even_or_odd n with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left
      have heq : d π ^ (j + j) = (d π ^ (2:ℤ)) ^ j := by rw [← _root_.zpow_mul]; congr 1; ring
      rw [heq]; exact zpow_mem hs2 j
    · right
      have heq : d π ^ (2*j+1) * d π = (d π ^ (2:ℤ)) ^ (j+1) := by
        rw [← _root_.zpow_add_one, ← _root_.zpow_mul]; congr 1; ring
      rw [heq]; exact zpow_mem hs2 (j+1)
  have hrel : M.relIndex (SL2_join_d p k π) = 2 := by
    rw [hJ, Subgroup.relIndex_eq_two_iff_exists_notMem_and]
    refine ⟨d π, ?_, caseV_vb_d_pi_notMem π hπ, ?_⟩
    · exact (le_sup_right : Subgroup.closure {d π} ≤ M ⊔ Subgroup.closure {d π})
        (Subgroup.subset_closure (Set.mem_singleton (d π)))
    · intro b hb
      rw [← SetLike.mem_coe, hdecomp, Set.mem_mul] at hb
      obtain ⟨m, hm, z, hzc, rfl⟩ := hb
      rcases hz z hzc with h | h
      · right; exact mul_mem hm h
      · left; rw [mul_assoc]; exact mul_mem hm h
  have hMJ : M ≤ SL2_join_d p k π := by rw [hJ]; exact le_sup_left
  have hcard := Subgroup.card_mul_index (M.subgroupOf (SL2_join_d p k π))
  have hidx : (M.subgroupOf (SL2_join_d p k π)).index = 2 := hrel
  have hcM : Nat.card (M.subgroupOf (SL2_join_d p k π)) = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMJ).toEquiv
  rw [hidx, hcM, hM, caseV_vb_card_image] at hcard
  omega

end CaseVb

/-- (SORRY) Case Vb (and Vc at `q = 3`), Butler tex 2013-2043 (`i = 2 = e`, `|K| = 2(q-1)`):
`G ≅ ⟨SL(2,𝔽_q), d_π⟩` with `SL(2,𝔽_q) ◁ G`. **Gap:** same projective-line normalization as Va,
now with `ω ∈ 𝔽_{q²} \ 𝔽_q` and `π` a generator of the order-`2(q-1)` cyclic `𝕄`. -/
lemma caseV_b {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F]
    [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q ga gb k n : ℕ)
    (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q)
    (A : Subgroup SL(2,F)) (hA_mem : A ∈ MaximalAbelianSubgroupsOf G)
    (hA_cyc : IsCyclic A) (hA_cop : Nat.Coprime (Nat.card A) p)
    (hA_card : Nat.card A = Nat.card (center SL(2,F)) * ga)
    (hA_relIndex : relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) = 2)
    (B : Subgroup SL(2,F)) (hB_mem : B ∈ MaximalAbelianSubgroupsOf G)
    (hB_cyc : IsCyclic B) (hB_cop : Nat.Coprime (Nat.card B) p)
    (hB_card : Nat.card B = Nat.card (center SL(2,F)) * gb)
    (hB_relIndex : relIndex (B.subgroupOf G) (normalizer (B.subgroupOf G : Set ↥G)) = 2)
    (K : Subgroup SL(2,F)) (hK_le : K ≤ G) (hK_cyc : IsCyclic K)
    (hK_card : Nat.card K = Nat.card (center SL(2,F)) * k)
    (hNQK : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G)
    (hQK_disj : Disjoint Q.toSubgroup (K.subgroupOf G))
    (hComplete : ∀ B' ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B' = A) ∨
      (∃ c ∈ G, conj c • B' = B) ∨ NumericClassEquation.IsSylowType p G B')
    (hkga : k = ga) (hga_ge : 2 ≤ ga) (hgb_ge : 2 ≤ gb)
    (hqpow : q = p ^ n) (hn0 : n ≠ 0) (hq3 : 3 ≤ q)
    (he2 : Nat.card (center SL(2,F)) = 2)
    (hshape1 : ga = q - 1) (hshape2 : gb = q + 1)
    (hshape3 : g = q * (q ^ 2 - 1)) :
    ∃ m : ℕ+, ∃ π : (GaloisField p (2 * m.val))ˣ,
      SL2_join_d_pi_spec p m π ∧ Isomorphic G (SL2_join_d p m π) := by
  sorry

/-- Core dispatch: proven modulo the sorried sub-lemmas above. -/
private lemma caseV_core {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F]
    [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q) (ga gb k : ℕ)
    (A : Subgroup SL(2,F)) (hA_mem : A ∈ MaximalAbelianSubgroupsOf G)
    (hA_cyc : IsCyclic A) (hA_cop : Nat.Coprime (Nat.card A) p)
    (hA_card : Nat.card A = Nat.card (center SL(2,F)) * ga)
    (hA_relIndex : relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) = 2)
    (B : Subgroup SL(2,F)) (hB_mem : B ∈ MaximalAbelianSubgroupsOf G)
    (hB_cyc : IsCyclic B) (hB_cop : Nat.Coprime (Nat.card B) p)
    (hB_card : Nat.card B = Nat.card (center SL(2,F)) * gb)
    (hB_relIndex : relIndex (B.subgroupOf G) (normalizer (B.subgroupOf G : Set ↥G)) = 2)
    (K : Subgroup SL(2,F)) (hK_le : K ≤ G) (hK_cyc : IsCyclic K)
    (hK_card : Nat.card K = Nat.card (center SL(2,F)) * k)
    (hNQK : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G)
    (hQK_disj : Disjoint Q.toSubgroup (K.subgroupOf G))
    (hComplete : ∀ B' ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B' = A) ∨
      (∃ c ∈ G, conj c • B' = B) ∨ NumericClassEquation.IsSylowType p G B')
    (hkga : k = ga) (hga_ge : 2 ≤ ga) (hgb_ge : 2 ≤ gb) (hgpos : 1 ≤ g) (hq2 : 2 ≤ q)
    (heq' : ClassEquation g q k (s := 0) (t := 2) (fun i => i.elim0) ![ga, gb]) :
    (∃ m : ℕ+, Isomorphic G SL(2, GaloisField p m.val)) ∨
      (∃ m : ℕ+, ∃ π : (GaloisField p (2 * m.val))ˣ,
        SL2_join_d_pi_spec p m π ∧ Isomorphic G (SL2_join_d p m π)) ∨
      (p = 3 ∧ Isomorphic G SL(2, ZMod 5)) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  rw [hq] at hn
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    omega
  -- group-theoretic feeders for `caseV_arith`
  have horbit : ga ∣ q - 1 := hkga ▸
    caseV_k_dvd_q_sub_one G center_le_G Q q k hq K hK_le hK_cyc hK_card hNQK hQK_disj
  have hqk_dvd : q * ga ∣ g := hkga ▸
    caseV_q_mul_k_dvd_g G Q g q k hg hq K hK_le hK_card hNQK hQK_disj
  have hqk_ne : q * ga ≠ g := hkga ▸
    caseV_qk_ne_g G center_le_G Q g q k hg hq hq2 (by omega) A hA_mem hA_relIndex B hB_mem
      hB_relIndex K hK_le hK_cyc hK_card hNQK hQK_disj hComplete
  have hgb_dvd : 2 * gb ∣ g :=
    caseV_two_mul_dvd_g_of_relIndex_normalizer_eq_two G B hB_mem.right g gb hg hB_card
      hB_relIndex
  have hgb_cop_p : Nat.Coprime gb p :=
    Nat.Coprime.coprime_dvd_left ⟨Nat.card (center SL(2,F)), by rw [hB_card]; ring⟩ hB_cop
  have hcop : Nat.Coprime gb q := by rw [hn]; exact Nat.Coprime.pow_right n hgb_cop_p
  have heqga : ClassEquation g q ga (s := 0) (t := 2) (fun i => i.elim0) ![ga, gb] :=
    hkga ▸ heq'
  rcases caseV_arith g q ga gb hgpos hq2 hga_ge hgb_ge horbit hqk_dvd hqk_ne hgb_dvd hcop heqga
    with ⟨hq4, i, hi12, hs1, hs2, hs3⟩ | ⟨hq3, hga2, hcase⟩
  · -- `q ≥ 4`: Cases Va/Vb
    rcases hi12 with rfl | rfl
    · -- `i = 1`: forces `p ≠ 2`, `e = 2`, Case Va
      have hp_ne2 : p ≠ 2 := by
        rintro rfl
        have h2q : 2 ∣ q := by
          rw [hn]
          exact dvd_pow_self 2 hn0
        omega
      have h2ne : (2:F) ≠ 0 := by
        intro h2
        exact hp_ne2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
          ((CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h2)))
      haveI : NeZero (2:F) := ⟨h2ne⟩
      have he2 : Nat.card (center SL(2,F)) = 2 := by
        rw [SpecialSubgroups.center_SL2_eq_Z]
        exact SpecialSubgroups.card_Z_eq_two_of_two_ne_zero
      exact Or.inl (caseV_a G center_le_G Q g q ga gb k 1 n hg hq A hA_mem hA_cyc hA_cop
        hA_card hA_relIndex B hB_mem hB_cyc hB_cop hB_card hB_relIndex K hK_le hK_cyc hK_card
        hNQK hQK_disj hComplete hkga hga_ge hgb_ge hn hn0 hq4 (by simpa using he2) hs1 hs2 hs3)
    · -- `i = 2`: `p = 2` gives Case Va (`e = 1`), `p ≠ 2` gives Case Vb (`e = 2`)
      by_cases hp2 : p = 2
      · subst hp2
        have h2 : (2:F) = 0 := CharTwo.two_eq_zero
        have he1 : Nat.card (center SL(2,F)) = 1 := by
          rw [SpecialSubgroups.center_SL2_eq_Z]
          exact SpecialSubgroups.card_Z_eq_one_of_two_eq_zero h2
        exact Or.inl (caseV_a G center_le_G Q g q ga gb k 2 n hg hq A hA_mem hA_cyc hA_cop
          hA_card hA_relIndex B hB_mem hB_cyc hB_cop hB_card hB_relIndex K hK_le hK_cyc hK_card
          hNQK hQK_disj hComplete hkga hga_ge hgb_ge hn hn0 hq4 (by simp [he1]) hs1 hs2 hs3)
      · have h2ne : (2:F) ≠ 0 := by
          intro h2
          exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
            ((CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h2)))
        haveI : NeZero (2:F) := ⟨h2ne⟩
        have he2 : Nat.card (center SL(2,F)) = 2 := by
          rw [SpecialSubgroups.center_SL2_eq_Z]
          exact SpecialSubgroups.card_Z_eq_two_of_two_ne_zero
        refine Or.inr (Or.inl (caseV_b G center_le_G Q g q ga gb k n hg hq A hA_mem hA_cyc
          hA_cop hA_card hA_relIndex B hB_mem hB_cyc hB_cop hB_card hB_relIndex K hK_le hK_cyc
          hK_card hNQK hQK_disj hComplete hkga hga_ge hgb_ge hn hn0 (by omega) he2 ?_ ?_ ?_))
        · exact Nat.eq_of_mul_eq_mul_left (by norm_num) hs1
        · exact Nat.eq_of_mul_eq_mul_left (by norm_num) hs2
        · exact Nat.eq_of_mul_eq_mul_left (by norm_num) hs3
  · -- `q = 3`: Cases Vc/Vd
    have hp3 : p = 3 := by
      have hdvd : p ∣ 3 := by
        rw [← hq3, hn]
        exact dvd_pow_self p hn0
      exact (Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num)).mp hdvd
    have h2ne : (2:F) ≠ 0 := by
      intro h2
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
        ((CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h2))
      omega
    haveI : NeZero (2:F) := ⟨h2ne⟩
    have he2 : Nat.card (center SL(2,F)) = 2 := by
      rw [SpecialSubgroups.center_SL2_eq_Z]
      exact SpecialSubgroups.card_Z_eq_two_of_two_ne_zero
    rcases hcase with ⟨hgb4, hg24⟩ | ⟨hgb5, hg60⟩
    · -- Case Vc: exactly the Case Vb situation at `q = 3`
      refine Or.inr (Or.inl (caseV_b G center_le_G Q g q ga gb k n hg hq A hA_mem hA_cyc
        hA_cop hA_card hA_relIndex B hB_mem hB_cyc hB_cop hB_card hB_relIndex K hK_le hK_cyc
        hK_card hNQK hQK_disj hComplete hkga hga_ge hgb_ge hn hn0 (by omega) he2
        (by omega) (by omega) ?_))
      rw [hg24, hq3]
      norm_num
    · -- Case Vd: `|G| = 120`, `G/Z` simple of order 60, `G ≅ SL(2,5)`
      refine Or.inr (Or.inr ⟨hp3, ?_⟩)
      have hcard120 : Nat.card G = 120 := by
        rw [hg, he2, hg60]
      have huniq : ∃! x : ↥G, orderOf x = 2 := caseV_exists_unique_involution G center_le_G
      have hsimple : IsSimpleGroup (↥G ⧸ center ↥G) :=
        caseV_d_quotient_simple G center_le_G Q g q hg hq ga gb k A hA_mem hA_cyc hA_cop
          hA_card hA_relIndex B hB_mem hB_cyc hB_cop hB_card hB_relIndex K hK_le hK_cyc hK_card
          hNQK hQK_disj hComplete hp3 hq3 hga2 hgb5 hg60 hkga he2
      exact caseV_d_recognition hcard120 huniq hsimple

/-- **Butler Case V** (`s = 0`, `t = 2`; tex 1848-2113). With the two dihedral-type maximal
abelian classes `A1, A2` (normalizer relative index `2`), the cyclic complement `K` of the Sylow
`p`-subgroup `Q` in `N_G(Q)`, and Butler's `k ∈ {g₁, g₂}` bundle (`hKbundle`), the class-equation
arithmetic (`caseV_arith`, via `CaseArithmetic.case_0_2`) leaves four cases: `q ≥ 4` gives Va
(`caseV_a`, `G ≅ SL(2,𝔽_q)`) or Vb (`caseV_b`, `G ≅ ⟨SL(2,𝔽_q), d_π⟩`); `q ≤ 3` forces
`q = p = 3`, splitting into Vc (`g₂ = 4`, Vb-shaped) and Vd (`g₂ = 5`, `G ≅ SL(2,5)`;
`caseV_d_quotient_simple` + `caseV_d_recognition`). Dispatch is `caseV_core`. The
geometric/recognition feeders (`caseV_k_dvd_q_sub_one`, `caseV_qk_ne_g`, `caseV_a`, `caseV_b`,
`caseV_d_quotient_simple`, `caseV_d_recognition`) remain `sorry`; see their docstrings. -/
lemma case_V {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F] [DecidableEq F]
    [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q) (g1 g2 k : ℕ)
    (A1 : Subgroup SL(2,F)) (hA1_mem : A1 ∈ MaximalAbelianSubgroupsOf G)
    (hA1_cyc : IsCyclic A1) (hA1_cop : Nat.Coprime (Nat.card A1) p)
    (hA1_card : Nat.card A1 = Nat.card (center SL(2,F)) * g1)
    (hA1_relIndex : relIndex (A1.subgroupOf G) (normalizer (A1.subgroupOf G : Set ↥G)) = 2)
    (A2 : Subgroup SL(2,F)) (hA2_mem : A2 ∈ MaximalAbelianSubgroupsOf G)
    (hA2_cyc : IsCyclic A2) (hA2_cop : Nat.Coprime (Nat.card A2) p)
    (hA2_card : Nat.card A2 = Nat.card (center SL(2,F)) * g2)
    (hA2_relIndex : relIndex (A2.subgroupOf G) (normalizer (A2.subgroupOf G : Set ↥G)) = 2)
    (K : Subgroup SL(2,F)) (hK_le : K ≤ G) (hK_cyc : IsCyclic K)
    (hK_card : Nat.card K = Nat.card (center SL(2,F)) * k)
    (hNQK : normalizer (Q.toSubgroup : Set ↥G) = Q.toSubgroup ⊔ K.subgroupOf G)
    (hQK_disj : Disjoint Q.toSubgroup (K.subgroupOf G))
    (hKbundle : 1 < k → k = g1 ∨ k = g2)
    (hComplete : ∀ B ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B = A1) ∨
      (∃ c ∈ G, conj c • B = A2) ∨ NumericClassEquation.IsSylowType p G B)
    (heq : 1 ≤ k ∧ 2 ≤ g1 ∧ 2 ≤ g2 ∧ 2 * g1 ≤ g ∧ 2 * g2 ≤ g ∧
      ClassEquation g q k (s := 0) (t := 2) (fun i => i.elim0) ![g1, g2]) :
    (∃ k : ℕ+, Isomorphic G SL(2, GaloisField p k.val)) ∨
      (∃ k : ℕ+, ∃ π : (GaloisField p (2 * k.val))ˣ,
        SL2_join_d_pi_spec p k π ∧ Isomorphic G (SL2_join_d p k π)) ∨
      (p = 3 ∧ Isomorphic G SL(2, ZMod 5)) := by
  obtain ⟨hk_ge, hg1_ge, hg2_ge, hg_ge1, hg_ge2, heq'⟩ := heq
  have hgpos : 1 ≤ g := by omega
  have hqpos : 1 ≤ q := by
    have := Nat.card_pos (α := Q.toSubgroup)
    omega
  obtain ⟨hq1, hk1⟩ := case_0_2 g q k g1 g2 hgpos hqpos hk_ge hg1_ge hg2_ge hg_ge1 hg_ge2 heq'
  rcases hKbundle hk1 with hkg1 | hkg2
  · exact caseV_core G center_le_G Q g q hg hq g1 g2 k A1 hA1_mem hA1_cyc hA1_cop hA1_card
      hA1_relIndex A2 hA2_mem hA2_cyc hA2_cop hA2_card hA2_relIndex K hK_le hK_cyc hK_card hNQK
      hQK_disj hComplete hkg1 hg1_ge hg2_ge hgpos hq1 heq'
  · have hComplete' : ∀ B ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B = A2) ∨
        (∃ c ∈ G, conj c • B = A1) ∨ NumericClassEquation.IsSylowType p G B := by
      intro B hB
      rcases hComplete B hB with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    exact caseV_core G center_le_G Q g q hg hq g2 g1 k A2 hA2_mem hA2_cyc hA2_cop hA2_card
      hA2_relIndex A1 hA1_mem hA1_cyc hA1_cop hA1_card hA1_relIndex K hK_le hK_cyc hK_card hNQK
      hQK_disj hComplete' hkg2 hg2_ge hg1_ge hgpos hq1
      (caseV_classEquation_swap g q k g1 g2 heq')

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
-- The presentation itself, `BinaryOctahedralRelations`/`BinaryOctahedralGroup`
-- (`⟨x, y | x⁴ = y³ = (xy)²⟩` over its own symbol type), is defined once in
-- `Ch7_GroupRecognition` (namespace `Ch7GroupRecognition`, in scope here via
-- `open Ch7GroupRecognition`), next to its recognition lemma
-- `mulEquiv_of_card48_uniqueInvolution_quotientS4`; an earlier local duplicate here made
-- every bare reference ambiguous.

/-- **Butler's Sylow-conjugacy argument** (tex ~2149-2157), abstracted: in a `G` of order `24`
whose center has order `2`, any two maximal abelian subgroups of order `6` are conjugate in `G`:
each is `B ⊔ Z` for a Sylow `3`-subgroup `B` of `G` (`Z` the center, of coprime order `2`),
Sylow's second theorem conjugates the `B`s, and conjugation fixes the (normal) center. Needed by
`case_VI_core` below to eliminate the `(ga,gb,gc) = (2,3,3)` numerical solution: there the two
order-`3` classes `A_b, A_c` are forced conjugate, contradicting their distinctness. -/
private lemma caseVI_conj_of_card_six {F : Type*} [Field F]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (he2 : Nat.card (center SL(2,F)) = 2) (hG24 : Nat.card G = 24)
    (Ab : Subgroup SL(2,F)) (hAb_mem : Ab ∈ MaximalAbelianSubgroupsOf G)
    (hAb6 : Nat.card Ab = 6)
    (Ac : Subgroup SL(2,F)) (hAc_mem : Ac ∈ MaximalAbelianSubgroupsOf G)
    (hAc6 : Nat.card Ac = 6) :
    ∃ x ∈ G, conj x • Ab = Ac := by
  classical
  haveI hAb_fin : Finite Ab :=
    (Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hAb_mem.right).to_subtype
  haveI hAc_fin : Finite Ac :=
    (Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hAc_mem.right).to_subtype
  -- order-`3` elements `b ∈ Ab`, `c ∈ Ac` (Cauchy, `3 ∣ 6`).
  obtain ⟨b0, hb0⟩ := exists_prime_orderOf_dvd_card' (G := Ab) 3 (by rw [hAb6]; norm_num)
  obtain ⟨c0, hc0⟩ := exists_prime_orderOf_dvd_card' (G := Ac) 3 (by rw [hAc6]; norm_num)
  set b : SL(2,F) := (b0 : SL(2,F)) with hb_def
  set c : SL(2,F) := (c0 : SL(2,F)) with hc_def
  have hb_ord : orderOf b = 3 := by rw [hb_def, orderOf_coe]; exact hb0
  have hc_ord : orderOf c = 3 := by rw [hc_def, orderOf_coe]; exact hc0
  have hbG : b ∈ G := hAb_mem.right b0.2
  have hcG : c ∈ G := hAc_mem.right c0.2
  set b' : ↥G := ⟨b, hbG⟩ with hb'_def
  set c' : ↥G := ⟨c, hcG⟩ with hc'_def
  have hb'_ord : orderOf b' = 3 := by rw [← orderOf_coe b']; exact hb_ord
  have hc'_ord : orderOf c' = 3 := by rw [← orderOf_coe c']; exact hc_ord
  -- `zpowers b'` and `zpowers c'` are Sylow `3`-subgroups of `↥G` (`|G| = 24 = 2³·3`).
  have hcard_zb' : Nat.card (Subgroup.zpowers b') = 3 := by rw [Nat.card_zpowers, hb'_ord]
  have hcard_zc' : Nat.card (Subgroup.zpowers c') = 3 := by rw [Nat.card_zpowers, hc'_ord]
  obtain ⟨P, hPle⟩ := (IsPGroup.of_card (n := 1)
    (by rw [hcard_zb', pow_one]) : IsPGroup 3 (Subgroup.zpowers b')).exists_le_sylow
  obtain ⟨Q, hQle⟩ := (IsPGroup.of_card (n := 1)
    (by rw [hcard_zc', pow_one]) : IsPGroup 3 (Subgroup.zpowers c')).exists_le_sylow
  have hsylow_card : ∀ (R : Sylow 3 ↥G) (r : ↥G), orderOf r = 3 →
      Subgroup.zpowers r ≤ (R : Subgroup ↥G) → Nat.card (R : Subgroup ↥G) = 3 := by
    intro R r hr_ord hle
    obtain ⟨n, hn⟩ := R.2.exists_card_eq
    have hdvd24 : (3 : ℕ) ^ n ∣ 24 := by
      rw [← hn, ← hG24]; exact Subgroup.card_subgroup_dvd_card _
    have h3dvd : (3 : ℕ) ∣ 3 ^ n := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [Nat.card_zpowers, hr_ord, hn] at h
    have hn1 : n = 1 := by
      rcases n with _ | _ | m
      · norm_num at h3dvd
      · rfl
      · exfalso
        have h9 : (9 : ℕ) ∣ 24 := by
          refine dvd_trans ?_ hdvd24
          rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
          exact pow_dvd_pow 3 (by omega)
        norm_num at h9
    rw [hn, hn1, pow_one]
  have hPbeq : Subgroup.zpowers b' = (P : Subgroup ↥G) :=
    Subgroup.eq_of_le_of_card_ge hPle
      (by rw [hsylow_card P b' hb'_ord hPle, hcard_zb'])
  have hQceq : Subgroup.zpowers c' = (Q : Subgroup ↥G) :=
    Subgroup.eq_of_le_of_card_ge hQle
      (by rw [hsylow_card Q c' hc'_ord hQle, hcard_zc'])
  -- Sylow's second theorem: `P` and `Q` are conjugate in `↥G`.
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq (↥G) P Q
  have hPQ : conj x • (P : Subgroup ↥G) = (Q : Subgroup ↥G) := by
    rw [← Sylow.coe_subgroup_smul, hx]
  have hconj_z : Subgroup.zpowers (x * b' * x⁻¹) = Subgroup.zpowers c' := by
    rw [← conj_zpowers_eq x b', hPbeq, hPQ, ← hQceq]
  -- push the conjugacy of the two `zpowers` down to `SL(2,F)`.
  have hmap := congrArg (Subgroup.map G.subtype) hconj_z
  rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at hmap
  have hzpow_amb : Subgroup.zpowers ((x : SL(2,F)) * b * (x : SL(2,F))⁻¹)
      = Subgroup.zpowers c := by simpa using hmap
  -- `Ab = zpowers b ⊔ Z` and `Ac = zpowers c ⊔ Z` (both contain the order-`3` `zpowers` and the
  -- order-`2` center, so the join has order divisible by `6 = |Ab| = |Ac|`).
  have hZle_Ab : center SL(2,F) ≤ Ab := center_le G Ab hAb_mem center_le_G
  have hZle_Ac : center SL(2,F) ≤ Ac := center_le G Ac hAc_mem center_le_G
  have hjoin : ∀ (A : Subgroup SL(2,F)), Finite A → Nat.card A = 6 →
      ∀ a : SL(2,F), a ∈ A → orderOf a = 3 → center SL(2,F) ≤ A →
      Subgroup.zpowers a ⊔ center SL(2,F) = A := by
    intro A hA_fin hA6 a haA ha_ord hZle
    haveI := hA_fin
    have hle : Subgroup.zpowers a ⊔ center SL(2,F) ≤ A :=
      sup_le (Subgroup.zpowers_le.mpr haA) hZle
    have h3 : (3 : ℕ) ∣ Nat.card (Subgroup.zpowers a ⊔ center SL(2,F) : Subgroup SL(2,F)) := by
      have h := Subgroup.card_dvd_of_le
        (le_sup_left : Subgroup.zpowers a ≤ Subgroup.zpowers a ⊔ center SL(2,F))
      rwa [Nat.card_zpowers, ha_ord] at h
    have h2 : (2 : ℕ) ∣ Nat.card (Subgroup.zpowers a ⊔ center SL(2,F) : Subgroup SL(2,F)) := by
      have h := Subgroup.card_dvd_of_le
        (le_sup_right : center SL(2,F) ≤ Subgroup.zpowers a ⊔ center SL(2,F))
      rwa [he2] at h
    have h6 : (6 : ℕ) ∣ Nat.card (Subgroup.zpowers a ⊔ center SL(2,F) : Subgroup SL(2,F)) := by
      have hco : Nat.Coprime 2 3 := by decide
      have := hco.mul_dvd_of_dvd_of_dvd h2 h3
      norm_num at this
      exact this
    have hdvd6 : Nat.card (Subgroup.zpowers a ⊔ center SL(2,F) : Subgroup SL(2,F)) ∣ 6 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [hA6] at h
    have hcard_join : Nat.card (Subgroup.zpowers a ⊔ center SL(2,F) : Subgroup SL(2,F)) = 6 :=
      Nat.dvd_antisymm hdvd6 h6
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hA6, hcard_join])
  have hAb_dec : Subgroup.zpowers b ⊔ center SL(2,F) = Ab :=
    hjoin Ab hAb_fin hAb6 b b0.2 hb_ord hZle_Ab
  have hAc_dec : Subgroup.zpowers c ⊔ center SL(2,F) = Ac :=
    hjoin Ac hAc_fin hAc6 c c0.2 hc_ord hZle_Ac
  -- assemble: conjugation by `↑x` carries `Ab = zpowers b ⊔ Z` onto `zpowers c ⊔ Z = Ac`.
  refine ⟨(x : SL(2,F)), x.2, ?_⟩
  calc conj (x : SL(2,F)) • Ab
      = conj (x : SL(2,F)) • (Subgroup.zpowers b ⊔ center SL(2,F)) := by rw [hAb_dec]
    _ = (conj (x : SL(2,F)) • Subgroup.zpowers b) ⊔ (conj (x : SL(2,F)) • center SL(2,F)) :=
        Subgroup.smul_sup _ _ _
    _ = Subgroup.zpowers ((x : SL(2,F)) * b * (x : SL(2,F))⁻¹) ⊔ center SL(2,F) := by
        rw [conj_zpowers_eq, Subgroup.Normal.conj_smul_eq_self]
    _ = Subgroup.zpowers c ⊔ center SL(2,F) := by rw [hzpow_amb]
    _ = Ac := hAc_dec

/-- `G`-conjugacy of subgroups is symmetric (conjugate back by `c⁻¹`); lets `case_VI` below feed
its three pairwise non-conjugacy hypotheses to `case_VI_core` in either orientation, whichever
the `WLOG` ordering branch demands. -/
private lemma caseVI_nconj_symm {F : Type*} [Field F] (G : Subgroup SL(2,F))
    {A B : Subgroup SL(2,F)} (h : ¬ ∃ c ∈ G, conj c • A = B) :
    ¬ ∃ c ∈ G, conj c • B = A := by
  rintro ⟨c, hcG, hc⟩
  refine h ⟨c⁻¹, inv_mem hcG, ?_⟩
  rw [← hc, _root_.map_inv]
  exact inv_smul_smul (conj c) B

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
* **Cases VIb/VIc** (`gb = 3`, forcing `gc ∈ {3,4,5}` by the same style of bound): `gc = 3` is
  **eliminated** via Butler's Sylow-conjugacy argument (tex ~2149-2157, showing this numerical
  solution is *vacuous*): there `|G| = 24` and the two order-`6` classes `A_b, A_c` are forced
  to be `G`-conjugate (`caseVI_conj_of_card_six` above), contradicting `hAbAc_nconj` (which is
  why the *middle* witness `Ab` and the non-conjugacy fact now appear in the signature);
  `gc = 4` needs the `Ŝ₄`/`BinaryOctahedralGroup` representation-group argument
  (tex ~2173-2201), still sorried; `gc = 5` needs the `SL(2,5)`-relabelling argument citing
  (the also-sorried) Case Vd (tex ~2202-2205), still sorried. -/
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
    -- the *middle* class `A_b` (witness data added for the `(2,3,3)` elimination; like `Aa`,
    -- only the fields that elimination actually needs are carried):
    (Ab : Subgroup SL(2,F)) (hAb_mem : Ab ∈ MaximalAbelianSubgroupsOf G)
    (hAb_card : Nat.card Ab = Nat.card (center SL(2,F)) * gb)
    (Ac : Subgroup SL(2,F)) (hAc_mem : Ac ∈ MaximalAbelianSubgroupsOf G)
    (hAc_cyc : IsCyclic Ac) (hAc_cop : Nat.Coprime (Nat.card Ac) p)
    (hAc_card : Nat.card Ac = Nat.card (center SL(2,F)) * gc)
    (hAc_relIndex : relIndex (Ac.subgroupOf G) (normalizer (Ac.subgroupOf G : Set ↥G)) = 2)
    -- `A_b` and `A_c` represent *distinct* conjugacy classes (Theorem 6.8's `t`-classes; from
    -- `BridgeData`'s `hAt_distinct`, threaded through `case_VI`): the `(2,3,3)` elimination
    -- refutes exactly this.
    (hAbAc_nconj : ¬ ∃ c ∈ G, conj c • Ab = Ac)
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
  · -- **Cases VIb/VIc** (`ga = 2, gb = 3`): the arithmetic pins `gc ∈ {3,4,5}`. Butler
    -- eliminates `gc = 3` via a Sylow-conjugacy argument showing the two order-`3` classes
    -- `A_b`, `A_c` are forced to be conjugate (tex ~2149-2157), contradicting their
    -- distinctness (`hAbAc_nconj`) -- proven below via `caseVI_conj_of_card_six`. `gc = 4`
    -- (Case VIb, `Ŝ₄`) and `gc = 5` (Case VIc, `SL(2,5)`) are separate substantial arguments
    -- (tex ~2173-2205), not attempted here. See the docstring above.
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
    · -- `(ga,gb,gc) = (2,3,3)` is **vacuous** (Butler tex ~2149-2157): here `|G| = 24` with
      -- `|A_b| = |A_c| = 6`, and `caseVI_conj_of_card_six` (Sylow's second theorem on the
      -- Sylow `3`-subgroups `B_b ≤ A_b`, `B_c ≤ A_c`, plus `A_i = B_i ⊔ Z`) forces `A_b`
      -- and `A_c` to be `G`-conjugate -- contradicting `hAbAc_nconj`.
      exfalso
      apply hAbAc_nconj
      -- `2 ∣ |G|` (via `|Aa| = e·2 ∣ |G|`), so `p ≠ 2`, so `e = |Z(SL(2,F))| = 2`.
      have h2dvdG : (2 : ℕ) ∣ Nat.card G := by
        have h1 : Nat.card Aa ∣ Nat.card G := Subgroup.card_dvd_of_le hAa_mem.right
        have h2 : (2 : ℕ) ∣ Nat.card Aa := by
          rw [hAa_card, hga_eq2]; exact dvd_mul_left 2 _
        exact h2.trans h1
      have hp_ne_two : p ≠ 2 := fun hp2 => hp_ndvd (by rw [hp2]; exact h2dvdG)
      have he_le_two : Nat.card (center SL(2,F)) ≤ 2 := by
        rw [SpecialSubgroups.center_SL2_eq_Z]; exact SpecialSubgroups.card_Z_le_two
      have he_ne_one : Nat.card (center SL(2,F)) ≠ 1 := by
        intro he1
        have h2 : (2 : F) = 0 := by
          by_contra h2ne
          haveI : NeZero (2 : F) := ⟨h2ne⟩
          rw [SpecialSubgroups.center_SL2_eq_Z,
            SpecialSubgroups.card_Z_eq_two_of_two_ne_zero] at he1
          omega
        have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
        exact hp_ne_two (CharP.eq F (‹CharP F p› : CharP F p) hCharP2)
      have he2 : Nat.card (center SL(2,F)) = 2 := by
        have := Nat.card_pos (α := center SL(2,F)); omega
      -- `g = 12` from Butler's Equation `\eqref{case6b}` at `(2,3,3)`, so `|G| = 24`.
      have hgcQ3 : (gc : ℚ) = 3 := by exact_mod_cast hgc3
      have h1g : (1 : ℚ) / g = 1 / 12 := by
        have h6' : (1 : ℚ) / (2 * 3) = 1 / 6 := by norm_num
        rw [hgcQ3, h6'] at hkey2
        linarith
      have hg12 : g = 12 := by
        rw [div_eq_div_iff hgQpos.ne' (by norm_num : (12 : ℚ) ≠ 0)] at h1g
        have h12 : (g : ℚ) = 12 := by linarith
        exact_mod_cast h12
      have hG24 : Nat.card G = 24 := by rw [hg, he2, hg12]
      have hAb6 : Nat.card Ab = 6 := by rw [hAb_card, he2, hgb3]
      have hAc6 : Nat.card Ac = 6 := by rw [hAc_card, he2, hgc3]
      exact caseVI_conj_of_card_six G center_le_G he2 hG24 Ab hAb_mem hAb6 Ac hAc_mem hAc6
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
to `case_VI_core` above, which does the rest of the arithmetic, the `(2,3,3)` Sylow-conjugacy
elimination (fed by the three pairwise non-conjugacy hypotheses below -- themselves supplied
from `BridgeData`'s `hAt_distinct` at the call site -- flipped via `caseVI_nconj_symm` where the
ordering demands), and (for Case VIa) the full group-recognition argument. **Cases VIb/VIc
remain sorried** inside `case_VI_core`: see its own docstring for exactly what is missing (the
`Ŝ₄` representation-group argument and the `SL(2,5)`-relabelling argument respectively). -/
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
    -- pairwise non-conjugacy of the three `t`-classes (Theorem 6.8 / `BridgeData`'s
    -- `hAt_distinct`, restated on the unpacked witnesses): `case_VI_core`'s `(2,3,3)`
    -- elimination refutes conjugacy of its two order-`3` classes, so each `WLOG` branch below
    -- passes the corresponding (possibly `caseVI_nconj_symm`-flipped) pair.
    (hA12_nconj : ¬ ∃ c ∈ G, conj c • A1 = A2)
    (hA13_nconj : ¬ ∃ c ∈ G, conj c • A1 = A3)
    (hA23_nconj : ¬ ∃ c ∈ G, conj c • A2 = A3)
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
        A2 hA2_mem hA2_card
        A3 hA3_mem hA3_cyc hA3_cop hA3_card hA3_relIndex hA23_nconj (by linarith [hsum0])
    · rcases le_total g1 g3 with h13 | h13
      · -- `g1 ≤ g3 ≤ g2`
        exact case_VI_core G center_le_G g hg hgpos hp_ndvd g1 g3 g2 h13 h23
          hg1_ge hg3_ge hg2_ge A1 hA1_mem hA1_cop hA1_card hA1_relIndex
          A3 hA3_mem hA3_card
          A2 hA2_mem hA2_cyc hA2_cop hA2_card hA2_relIndex
          (caseVI_nconj_symm G hA23_nconj) (by linarith [hsum0])
      · -- `g3 ≤ g1 ≤ g2`
        exact case_VI_core G center_le_G g hg hgpos hp_ndvd g3 g1 g2 h13 h12
          hg3_ge hg1_ge hg2_ge A3 hA3_mem hA3_cop hA3_card hA3_relIndex
          A1 hA1_mem hA1_card
          A2 hA2_mem hA2_cyc hA2_cop hA2_card hA2_relIndex hA12_nconj (by linarith [hsum0])
  · rcases le_total g1 g3 with h13 | h13
    · -- `g2 ≤ g1 ≤ g3`
      exact case_VI_core G center_le_G g hg hgpos hp_ndvd g2 g1 g3 h12 h13
        hg2_ge hg1_ge hg3_ge A2 hA2_mem hA2_cop hA2_card hA2_relIndex
        A1 hA1_mem hA1_card
        A3 hA3_mem hA3_cyc hA3_cop hA3_card hA3_relIndex hA13_nconj (by linarith [hsum0])
    · rcases le_total g2 g3 with h23 | h23
      · -- `g2 ≤ g3 ≤ g1`
        exact case_VI_core G center_le_G g hg hgpos hp_ndvd g2 g3 g1 h23 h13
          hg2_ge hg3_ge hg1_ge A2 hA2_mem hA2_cop hA2_card hA2_relIndex
          A3 hA3_mem hA3_card
          A1 hA1_mem hA1_cyc hA1_cop hA1_card hA1_relIndex
          (caseVI_nconj_symm G hA13_nconj) (by linarith [hsum0])
      · -- `g3 ≤ g2 ≤ g1`
        exact case_VI_core G center_le_G g hg hgpos hp_ndvd g3 g2 g1 h23 h12
          hg3_ge hg2_ge hg1_ge A3 hA3_mem hA3_cop hA3_card hA3_relIndex
          A2 hA2_mem hA2_card
          A1 hA1_mem hA1_cyc hA1_cop hA1_card hA1_relIndex
          (caseVI_nconj_symm G hA12_nconj) (by linarith [hsum0])


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
          (hAt_distinct 0 1 (by decide)) (hAt_distinct 0 2 (by decide))
          (hAt_distinct 1 2 (by decide))
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

/-- A ring isomorphism `R ≃+* S` induces a group isomorphism `SL(2,R) ≃* SL(2,S)`
(`Matrix.SpecialLinearGroup.map` applied in both directions along `e`/`e.symm`, mutually
inverse since `e.symm.comp e.toRingHom = RingHom.id`). Needed to identify `SL(2,ZMod 3)` (the
concrete group `case_IV`'s Case IVb produces) with `SL(2,GaloisField 3 1)` (Butler Class II's
item (ix) shape `SL(2,𝔽_{p^k})` at `k = 1`), via `GaloisField.equivZmodP`. -/
noncomputable def SL2_mulEquiv_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) : SL(2,R) ≃* SL(2,S) where
  toFun := Matrix.SpecialLinearGroup.map e.toRingHom
  invFun := Matrix.SpecialLinearGroup.map e.symm.toRingHom
  left_inv A := by
    apply Subtype.ext
    ext <;> simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  right_inv A := by
    apply Subtype.ext
    ext <;> simp [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  map_mul' := (Matrix.SpecialLinearGroup.map e.toRingHom).map_mul

/-- Conjugation preserves the cardinality of a subgroup (`Subgroup.equivSMul` for the
`MulAut.conj` pointwise action). -/
lemma card_conj_smul_eq_card {L : Type*} [Group L] {B : Subgroup L} (c : L) :
    Nat.card (conj c • B : Subgroup L) = Nat.card B :=
  (Nat.card_congr (Subgroup.equivSMul (conj c) B).toEquiv).symm

/- ==========================================================================================
`caseV` Step-5 recognition endpoint (Butler tex 2054), frame-independent and shared by Cases Va/Vb.
Given the normalized-frame conclusion of Steps 1-4 — a conjugate of `G` sits inside (Va: equals)
the subfield copy `SL(2, R F p n)` — these lemmas transport it through the chain
`G ≃* vGv⁻¹ ≃* SL(2, R F p n) ≃* SL(2, GaloisField p n)` (conjugation `Subgroup.equivSMul`; the
subfield inclusion `Matrix.SpecialLinearGroup.map (R F p n).subtype` is injective, so its image on
`⊤` is `Subgroup.equivMapOfInjective`-isomorphic to `SL(2, R F p n)`; then the subfield ring iso of
`caseV_ringEquiv_R_GaloisField` via `SL2_mulEquiv_of_ringEquiv`). NB: these consume
`SL2_mulEquiv_of_ringEquiv`/`card_conj_smul_eq_card` above, so when `caseV_a` is mechanized this
block (together with those two) relocates before it. -/

/-- Step-5 recognition, equality form: if a conjugate of `G` *equals* the image of the whole
`SL(2, R F p n)` under the subfield inclusion, then `G ≅ SL(2, GaloisField p n)`. -/
lemma caseV_iso_of_conj_eq_map {F : Type*} [Field F] [IsAlgClosed F] {p : ℕ}
    [Fact (Nat.Prime p)] [CharP F p] (n : ℕ+) (G : Subgroup SL(2,F)) (c : SL(2,F))
    (hG : conj c • G =
      Subgroup.map (Matrix.SpecialLinearGroup.map (R F p n).subtype) ⊤) :
    Isomorphic G SL(2, GaloisField p n.val) := by
  obtain ⟨eR⟩ := caseV_ringEquiv_R_GaloisField (F := F) (p := p) n
  set φ : SL(2, R F p n) →* SL(2, F) := Matrix.SpecialLinearGroup.map (R F p n).subtype with hφ
  have hsub_inj : Function.Injective ⇑(R F p n).subtype := fun a b h => Subtype.ext h
  have hφinj : Function.Injective φ := by
    intro A B hAB
    apply Subtype.ext
    have h : (φ A).1 = (φ B).1 := Subtype.ext_iff.mp hAB
    simp only [hφ, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h
    exact Matrix.map_injective hsub_inj h
  let e1 : ↥G ≃* ↥(conj c • G) := Subgroup.equivSMul (conj c) G
  let e2 : ↥(conj c • G) ≃* ↥(Subgroup.map φ ⊤) := MulEquiv.subgroupCongr hG
  let e3 : ↥(Subgroup.map φ ⊤) ≃* SL(2, R F p n) :=
    (Subgroup.equivMapOfInjective ⊤ φ hφinj).symm.trans Subgroup.topEquiv
  exact ⟨((e1.trans e2).trans e3).trans (SL2_mulEquiv_of_ringEquiv eR)⟩

/-- Step-5 recognition, containment form (the route-map's actual Step-4 output, tex 2054): if a
conjugate of `G` is *contained* in the subfield copy `SL(2, R F p n)` and `|G| = q(q²-1)` with
`q = pⁿ`, then equality holds by cardinality and `G ≅ SL(2, GaloisField p n)`. -/
lemma caseV_iso_of_conj_le_map {F : Type*} [Field F] [IsAlgClosed F] {p : ℕ}
    [Fact (Nat.Prime p)] [CharP F p] (n : ℕ+) (G : Subgroup SL(2,F)) [Finite G] (c : SL(2,F))
    (hle : conj c • G ≤ Subgroup.map (Matrix.SpecialLinearGroup.map (R F p n).subtype) ⊤)
    (hcard : Nat.card G = ((p ^ (n : ℕ)) ^ 2 - 1) * p ^ (n : ℕ)) :
    Isomorphic G SL(2, GaloisField p n.val) := by
  set φ : SL(2, R F p n) →* SL(2, F) := Matrix.SpecialLinearGroup.map (R F p n).subtype with hφ
  have hsub_inj : Function.Injective ⇑(R F p n).subtype := fun a b h => Subtype.ext h
  have hφinj : Function.Injective φ := by
    intro A B hAB
    apply Subtype.ext
    have h : (φ A).1 = (φ B).1 := Subtype.ext_iff.mp hAB
    simp only [hφ, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h
    exact Matrix.map_injective hsub_inj h
  have hcardR : Nat.card (R F p n) = p ^ (n : ℕ) := caseV_card_R n
  haveI : Finite (R F p n) :=
    Nat.finite_of_card_ne_zero (by rw [hcardR]; exact pow_ne_zero _ (Fact.out : p.Prime).pos.ne')
  haveI : Fintype (R F p n) := Fintype.ofFinite _
  have hq1 : 1 < p ^ (n : ℕ) := Nat.one_lt_pow n.pos.ne' (Fact.out : p.Prime).one_lt
  have hfc : Fintype.card (R F p n) = p ^ (n : ℕ) := by rw [← hcardR, Nat.card_eq_fintype_card]
  let e3 : ↥(Subgroup.map φ ⊤) ≃* SL(2, R F p n) :=
    (Subgroup.equivMapOfInjective ⊤ φ hφinj).symm.trans Subgroup.topEquiv
  haveI : Finite ↥(Subgroup.map φ ⊤) := Finite.of_equiv _ e3.symm.toEquiv
  haveI : Finite ↥(conj c • G) := Finite.of_equiv _ (Subgroup.equivSMul (conj c) G).toEquiv
  have hcardImg : Nat.card (Subgroup.map φ ⊤) = ((p ^ (n : ℕ)) ^ 2 - 1) * p ^ (n : ℕ) := by
    rw [Nat.card_congr e3.toEquiv, Nat.card_eq_fintype_card]; exact SL_card hfc hq1
  have hcc : Nat.card (conj c • G : Subgroup SL(2,F)) = Nat.card G := card_conj_smul_eq_card c
  have hcardle : Nat.card (Subgroup.map φ ⊤) ≤ Nat.card (conj c • G : Subgroup SL(2,F)) :=
    le_of_eq (by rw [hcardImg, hcc, hcard])
  have heq : conj c • G = Subgroup.map φ ⊤ := Subgroup.eq_of_le_of_card_ge hle hcardle
  exact caseV_iso_of_conj_eq_map n G c (hφ ▸ heq)

/-- **Theorem 6.8(v), coprimality half.** If `K` is the (Schur–Zassenhaus, `S2_B.exists_IsCyclic_
K_normalizer_eq_Q_join_K`) complement to a Sylow `p`-subgroup `S₀` of `G` (`normalizer (S₀.
toSubgroup) = S₀.toSubgroup ⊔ K`, `Disjoint S₀.toSubgroup K`), then `Nat.card K` is coprime to
`p`: `S₀` is *already* a full Sylow `p`-subgroup of `G`, hence also of `N_G(S₀) = S₀ ⊔ K`
(cardinalities multiply, `IsComplement'.card_mul`, since `S₀`/`K` are complementary inside
`N_G(S₀)` -- `S₀` normal in its own normalizer, disjoint from `K` -- so `Nat.card (N_G(S₀)) =
Nat.card S₀ * Nat.card K = p ^ n * Nat.card K` where `n := (Nat.card G).factorization p`); since
`Nat.card (N_G(S₀)) ∣ Nat.card G` (Lagrange) and `n` is *exactly* the `p`-adic valuation of
`Nat.card G`, a further factor of `p` in `Nat.card K` would force `p ^ (n+1) ∣ Nat.card G`,
contradicting `n`'s maximality (`Nat.Prime.pow_dvd_iff_le_factorization`). -/
lemma coprime_card_complement_of_normalizer_eq_sylow_join {F : Type*} {p : ℕ} [Field F]
    [Fact (Nat.Prime p)] (G : Subgroup SL(2,F)) [Finite G] (S0 : Sylow p G) (K0 : Subgroup ↥G)
    (hQK0 : Disjoint S0.toSubgroup K0)
    (hNG0 : normalizer (S0.toSubgroup : Set ↥G) = S0.toSubgroup ⊔ K0) :
    Nat.Coprime (Nat.card K0) p := by
  set Nz : Subgroup ↥G := normalizer (S0.toSubgroup : Set ↥G) with hNz_def
  have hQ_le_Nz : S0.toSubgroup ≤ Nz := Subgroup.le_normalizer
  have hK_le_Nz : K0 ≤ Nz := by rw [hNG0]; exact le_sup_right
  set Qn : Subgroup ↥Nz := S0.toSubgroup.subgroupOf Nz with hQn_def
  set Kn : Subgroup ↥Nz := K0.subgroupOf Nz with hKn_def
  have hsup : Qn ⊔ Kn = ⊤ := by
    have h := congrArg (Subgroup.subgroupOf · Nz) hNG0
    rw [Subgroup.subgroupOf_self, Subgroup.subgroupOf_sup hQ_le_Nz hK_le_Nz] at h
    exact h.symm
  have hdisj : Qn ⊓ Kn = ⊥ := by
    have h := congrArg (Subgroup.subgroupOf · Nz) (disjoint_iff.mp hQK0)
    rwa [subgroupOf_inf_eq, Subgroup.bot_subgroupOf] at h
  haveI hQn_normal : Qn.Normal := Subgroup.normal_in_normalizer (H := S0.toSubgroup)
  have hcomplement : IsComplement' Qn Kn := by
    apply isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hdisj)
    have h := Subgroup.normal_mul Qn Kn
    rw [hsup, Subgroup.coe_top] at h
    exact h.symm
  have hcard_Nz : Nat.card Qn * Nat.card Kn = Nat.card Nz := hcomplement.card_mul
  have hcard_Qn : Nat.card Qn = Nat.card S0.toSubgroup :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ_le_Nz).toEquiv
  have hcard_Kn : Nat.card Kn = Nat.card K0 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK_le_Nz).toEquiv
  have hcard_QS : Nat.card S0.toSubgroup = p ^ (Nat.card G).factorization p :=
    Sylow.card_eq_multiplicity S0
  have hNz_dvd : Nat.card Nz ∣ Nat.card G := Subgroup.card_subgroup_dvd_card Nz
  have hGne : Nat.card G ≠ 0 := Nat.card_pos.ne'
  rw [Nat.coprime_comm, (Fact.out : Nat.Prime p).coprime_iff_not_dvd]
  intro hpdvd
  obtain ⟨m, hm⟩ := hpdvd
  have hp1dvd : p ^ ((Nat.card G).factorization p + 1) ∣ Nat.card Nz :=
    ⟨m, by rw [← hcard_Nz, hcard_Qn, hcard_Kn, hcard_QS, hm]; ring⟩
  have hp1dvdG : p ^ ((Nat.card G).factorization p + 1) ∣ Nat.card G := hp1dvd.trans hNz_dvd
  have hle := (Fact.out : Nat.Prime p).pow_dvd_iff_le_factorization hGne |>.mp hp1dvdG
  omega

/-- **Theorem 6.8(v), identification half.** With `S0`/`K0` as above and `1 < k` (i.e. `K0`
properly bigger than the center), `K0`'s image is a genuine coprime-type maximal abelian
subgroup of `G` (`S2_B.K_mem_MaximalAbelianSubgroups_of_center_lt_card_K`, using the coprimality
just proved), hence (`hComplete`, Theorem 6.8's numeric class equation) `G`-conjugate to some
`As i` or `At j` -- pinning `k` to `gs i` or `gt j` exactly (cardinality is conjugation-invariant,
`card_conj_smul_eq_card`); the third (`IsSylowType`) alternative is impossible since `K0`'s image
is coprime-type, contradicting `dvd_card_of_isSylowType` via the coprimality above. This is
exactly the "Theorem 6.8(v): a nontrivial complement is one of the recognized classes" fact each
`CaseArithmetic.case_1_0`/`case_0_0`/`case_1_1`/`case_0_3`'s own `hK`/`hKle` hypothesis needs --
closing it here (using `BridgeData`'s *real* `hSylow` witness) is what lets `dicksons_
classification_theorem_class_II` below dispatch those cases in full, rather than carrying `hK` as
an extra unproved hypothesis the way `case_I`/`case_II`/`case_IV`/`case_VI` above do. -/
lemma card_K_eq_of_one_lt_of_normalizer_eq_sylow_join {F : Type*} {p : ℕ} [Field F]
    [IsAlgClosed F] [DecidableEq F] [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (S0 : Sylow p G) (hSne : S0.toSubgroup ≠ ⊥)
    (K0 : Subgroup ↥G) (hK0cyc : IsCyclic K0)
    (hNG0 : normalizer (S0.toSubgroup : Set ↥G) = S0.toSubgroup ⊔ K0)
    (hQK0 : Disjoint S0.toSubgroup K0) (k : ℕ)
    (hK0card : Nat.card K0 = Nat.card (center SL(2,F)) * k)
    {s t : ℕ} (gs : Fin s → ℕ) (gt : Fin t → ℕ) (As : Fin s → Subgroup SL(2,F))
    (At : Fin t → Subgroup SL(2,F))
    (hAs_card : ∀ i, Nat.card (As i) = Nat.card (center SL(2,F)) * gs i)
    (hAt_card : ∀ i, Nat.card (At i) = Nat.card (center SL(2,F)) * gt i)
    (hComplete : ∀ B ∈ MaximalAbelianSubgroupsOf G,
      (∃ (i : Fin s) (c : SL(2,F)), c ∈ G ∧ conj c • B = As i) ∨
      (∃ (j : Fin t) (c : SL(2,F)), c ∈ G ∧ conj c • B = At j) ∨
      NumericClassEquation.IsSylowType p G B) :
    1 < k → (∃ i, k = gs i) ∨ (∃ j, k = gt j) := by
  intro hk1lt
  have he : 0 < Nat.card (center SL(2,F)) := Nat.card_pos
  have hK0Z : Nat.card (center SL(2,F)) < Nat.card K0 := by
    rw [hK0card]; exact (lt_mul_iff_one_lt_right he).mpr hk1lt
  have hcopK0 : Nat.Coprime (Nat.card K0) p :=
    coprime_card_complement_of_normalizer_eq_sylow_join G S0 K0 hQK0 hNG0
  haveI hK0Gfin : Finite (Subgroup.map G.subtype K0) :=
    (Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) (Subgroup.map_subtype_le K0)).to_subtype
  have hK0mem : Subgroup.map G.subtype K0 ∈ MaximalAbelianSubgroupsOf G :=
    K_mem_MaximalAbelianSubgroups_of_center_lt_card_K G S0 hSne K0 hK0cyc hNG0 hK0Z hcopK0
  have hcardK0 : Nat.card (Subgroup.map G.subtype K0) = Nat.card K0 :=
    Nat.card_congr (K0.equivMapOfInjective G.subtype (Subgroup.subtype_injective G)).toEquiv.symm
  rcases hComplete _ hK0mem with ⟨i, c, -, hc⟩ | ⟨j, c, -, hc⟩ | hsyl
  · left
    refine ⟨i, ?_⟩
    have hcard_eq : Nat.card (As i) = Nat.card (Subgroup.map G.subtype K0) := by
      rw [← hc]; exact card_conj_smul_eq_card c
    rw [hcardK0, hK0card, hAs_card i] at hcard_eq
    exact (Nat.eq_of_mul_eq_mul_left he hcard_eq).symm
  · right
    refine ⟨j, ?_⟩
    have hcard_eq : Nat.card (At j) = Nat.card (Subgroup.map G.subtype K0) := by
      rw [← hc]; exact card_conj_smul_eq_card c
    rw [hcardK0, hK0card, hAt_card j] at hcard_eq
    exact (Nat.eq_of_mul_eq_mul_left he hcard_eq).symm
  · exfalso
    have hpdvd : p ∣ Nat.card (Subgroup.map G.subtype K0) :=
      NumericClassEquation.dvd_card_of_isSylowType hsyl
    rw [hcardK0] at hpdvd
    exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcopK0.symm hpdvd

/-- **Arithmetic core of DIVERGENCES item 12, `(s,t) = (1,1)` shape** (Butler's Case II): with
`q = 1` the class equation `1 = 1/g + (g₁-1)/g₁ + (g₂-1)/(2g₂)` clears denominators to the
`ℕ`-identity `g⋅(2g₂ + g₁) = g₁⋅g₂⋅(g + 2)`; an odd prime `p` dividing `g` but neither `g₁` nor
`g₂` would then divide `g + 2`, hence `2` -- impossible. This is exactly why Butler's Case II
can only occur when `p ∤ |G|`. -/
lemma classII_arith_1_1_false {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (g k g1 g2 : ℕ)
    (hg : 1 ≤ g) (hg1 : 2 ≤ g1) (hg2 : 2 ≤ g2)
    (heq : ClassEquation g 1 k (s := 1) (t := 1) (fun _ => g1) (fun _ => g2))
    (hpg : p ∣ g) (hpg1 : ¬ p ∣ g1) (hpg2 : ¬ p ∣ g2) : False := by
  unfold ClassEquation at heq
  simp only [Fin.sum_univ_one, Nat.cast_one, sub_self, one_mul, zero_div, add_zero] at heq
  have hgQ : (0 : ℚ) < g := by exact_mod_cast (by omega : 0 < g)
  have hg1Q : (0 : ℚ) < g1 := by exact_mod_cast (by omega : 0 < g1)
  have hg2Q : (0 : ℚ) < g2 := by exact_mod_cast (by omega : 0 < g2)
  have hgne : (g : ℚ) ≠ 0 := ne_of_gt hgQ
  have hg1ne : (g1 : ℚ) ≠ 0 := ne_of_gt hg1Q
  have hg2ne : (g2 : ℚ) ≠ 0 := ne_of_gt hg2Q
  have hkey : (g : ℚ) * (2 * g2 + g1) = g1 * g2 * (g + 2) := by
    field_simp at heq
    ring_nf at heq ⊢
    linarith
  have hkeyN : g * (2 * g2 + g1) = g1 * g2 * (g + 2) := by exact_mod_cast hkey
  have hdvd : p ∣ g1 * g2 * (g + 2) := by
    rw [← hkeyN]; exact hpg.mul_right _
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h12 | h3
  · rcases (Nat.Prime.dvd_mul hp).mp h12 with h1 | h2
    · exact hpg1 h1
    · exact hpg2 h2
  · have h2dvd : p ∣ 2 := (Nat.dvd_add_right hpg).mp h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd)

/-- **Arithmetic core of DIVERGENCES item 12, `(s,t) = (0,3)` shape** (Butler's Case VI): with
`q = 1` the class equation `1 = 1/g + ∑_{j<3} (gⱼ-1)/(2gⱼ)` clears denominators to the
`ℕ`-identity `g⋅(g₂g₃ + g₁g₃ + g₁g₂) = g₁⋅g₂⋅g₃⋅(g + 2)`; an odd prime `p` dividing `g` but
none of the `gⱼ` would then divide `g + 2`, hence `2` -- impossible. This is exactly why
Butler's Case VI can only occur when `p ∤ |G|`. -/
lemma classII_arith_0_3_false {p : ℕ} (hp : Nat.Prime p) (hp2 : p ≠ 2) (g k g1 g2 g3 : ℕ)
    (hg : 1 ≤ g) (hg1 : 2 ≤ g1) (hg2 : 2 ≤ g2) (hg3 : 2 ≤ g3)
    (heq : ClassEquation g 1 k (s := 0) (t := 3) (fun i => i.elim0) ![g1, g2, g3])
    (hpg : p ∣ g) (hpg1 : ¬ p ∣ g1) (hpg2 : ¬ p ∣ g2) (hpg3 : ¬ p ∣ g3) : False := by
  unfold ClassEquation at heq
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Nat.cast_one, sub_self, one_mul, zero_div, add_zero] at heq
  have hgQ : (0 : ℚ) < g := by exact_mod_cast (by omega : 0 < g)
  have hg1Q : (0 : ℚ) < g1 := by exact_mod_cast (by omega : 0 < g1)
  have hg2Q : (0 : ℚ) < g2 := by exact_mod_cast (by omega : 0 < g2)
  have hg3Q : (0 : ℚ) < g3 := by exact_mod_cast (by omega : 0 < g3)
  have hgne : (g : ℚ) ≠ 0 := ne_of_gt hgQ
  have hg1ne : (g1 : ℚ) ≠ 0 := ne_of_gt hg1Q
  have hg2ne : (g2 : ℚ) ≠ 0 := ne_of_gt hg2Q
  have hg3ne : (g3 : ℚ) ≠ 0 := ne_of_gt hg3Q
  have hkey : (g : ℚ) * (g2 * g3 + g1 * g3 + g1 * g2) = g1 * g2 * g3 * (g + 2) := by
    field_simp at heq
    ring_nf at heq ⊢
    linarith
  have hkeyN : g * (g2 * g3 + g1 * g3 + g1 * g2) = g1 * g2 * g3 * (g + 2) := by
    exact_mod_cast hkey
  have hdvd : p ∣ g1 * g2 * g3 * (g + 2) := by
    rw [← hkeyN]; exact hpg.mul_right _
  rcases (Nat.Prime.dvd_mul hp).mp hdvd with h123 | h4
  · rcases (Nat.Prime.dvd_mul hp).mp h123 with h12 | h3
    · rcases (Nat.Prime.dvd_mul hp).mp h12 with h1 | h2
      · exact hpg1 h1
      · exact hpg2 h2
    · exact hpg3 h3
  · have h2dvd : p ∣ 2 := (Nat.dvd_add_right hpg).mp h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd)

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

Narrowing hypotheses `center_le_G`/`hp2 : p ≠ 2` added, mirroring `dicksons_classification_theorem_
class_I` above (needed by `S5_NumericClassEquation.exists_bridgeData`; `hG_ne` is now *derived*
rather than assumed, since `G = center SL(2,F)` would make `Nat.card G` coprime to `p`
(`NumericClassEquation.coprime_card_Z_prime`), contradicting `hp`).

Dispatch mirrors `class_I`'s six-way `case_enumeration` split, but with `p ∣ Nat.card G` in place
of `p ∤ Nat.card G`: `(1,1)` (`case_II`) and `(0,3)` (`case_VI`) always force `q = 1`
(`CaseArithmetic.case_1_1`/`case_0_3`, unconditionally, independent of `p`), and are indeed
impossible here (Butler's Case II/VI, not his `p ∣ |G|` Class II): in `hSylow`'s "no witness"
disjunct (`q = 1`) the class equation clears denominators to a `ℕ`-identity
(`classII_arith_1_1_false`/`classII_arith_0_3_false` above) forcing the odd prime `p` -- which
divides `g` by `hp` and `coprime_card_Z_prime` -- to divide one of the coprime-to-`p` class
sizes `gs i`/`gt j` or `2`, a contradiction; in the witness disjunct, `case_1_1`/`case_0_3`'s
`q = 1` contradicts the witness's `Q.subgroupOf G ≠ ⊥` (`DIVERGENCES.md` item 12, now closed).
The other four branches dispatch in full: `(1,0)` (`case_I`) and `(0,0)` (`case_III`) split on
`hSylow` themselves (its `q = 1` disjunct closes directly via coprimality of the witness
`As 0`/of `Nat.card G = Nat.card (center SL(2,F))` respectively, contradicting `hp`; its genuine-
witness disjunct feeds `case_I`/`case_III`, with `card_K_eq_of_one_lt_of_normalizer_eq_sylow_join`
above discharging their own `hK`/`hKle` hypotheses -- Theorem 6.8(v) -- in full); `(0,1)`
(`case_IV`) and `(0,2)` (`case_V`) force `1 < q` unconditionally (`case_0_1`/`case_0_2`), so
`hSylow`'s witness disjunct is immediate. `case_IV`'s `p = 2` output contradicts `hp2`; its `p = 3`
output (`Isomorphic G SL(2,ZMod 3)`) is bridged to item (ix) at `k = 1` via `SL2_mulEquiv_of_
ringEquiv`/`GaloisField.equivZmodP`. `case_V`'s three outputs map directly onto items (ix)/(x)/
(viii). -/
-- ANCHOR: dicksons_classification_theorem_class_II
theorem dicksons_classification_theorem_class_II {F : Type*} [Field F] [IsAlgClosed F]
    [DecidableEq F] {p : ℕ}
    [Fact (Nat.Prime p)] [CharP F p] (G : Subgroup (SL(2,F))) [Finite G] (hp : p ∣ Nat.card G)
    (center_le_G : center SL(2,F) ≤ G) (hp2 : p ≠ 2) :
    (∃ Q : Subgroup G, IsElementaryAbelian p Q ∧ Normal Q ∧
        ∃ K : Subgroup G, IsComplement' Q K ∧ IsCyclic K ∧ Nat.Coprime p (Nat.card K)) ∨
      (p = 2 ∧ ∃ n : ℕ, Odd n ∧ Isomorphic G (DihedralGroup n)) ∨
      (p = 3 ∧ Isomorphic G SL(2, ZMod 5)) ∨
      (∃ k : ℕ+, Isomorphic G SL(2, GaloisField p k.val)) ∨
      (∃ k : ℕ+, ∃ π : (GaloisField p (2 * k.val))ˣ,
        SL2_join_d_pi_spec p k π ∧ Isomorphic G (SL2_join_d p k π))
  := by
  have hG_ne : G ≠ center SL(2,F) := by
    intro hEq
    have hcop : Nat.Coprime (Nat.card (center SL(2,F))) p := by
      rw [SpecialSubgroups.center_SL2_eq_Z]
      exact NumericClassEquation.coprime_card_Z_prime
    rw [hEq] at hp
    exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop.symm hp
  obtain ⟨d⟩ := NumericClassEquation.exists_bridgeData G hp2 center_le_G hG_ne
  obtain ⟨g, q, k, s, t, gs, gt, As, At, hAs_mem, hAt_mem, hAs_card, hAt_card, hAs_relIndex,
    hAt_relIndex, hAs_cyclic, hAt_cyclic, hAs_coprime, hAt_coprime, hg, hSylow, hg_pos, hq_pos,
    hk_pos, hgs_ge, hgt_ge, heq, hComplete, hAs_distinct, hAt_distinct⟩ := d
  rcases case_enumeration g q k hg_pos hq_pos hk_pos gs gt hgs_ge hgt_ge heq with
    hst | hst | hst | hst | hst | hst
  · -- `(s,t) = (1,0)`: `case_I`.
    obtain ⟨hs, ht⟩ := hst
    subst hs; subst ht
    have hgs_eq : gs = fun _ : Fin 1 => gs 0 :=
      funext fun i => congrArg gs (Subsingleton.elim i 0)
    have hgt_eq : gt = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
    rw [hgs_eq, hgt_eq] at heq
    rcases hSylow with ⟨hq1, hk1⟩ |
      ⟨Q0, K0, S0, hQ0_le, hQ0eqS0, hQ0ne, hQ0card, hK0_le, hK0cyc, hNG0, hQK0, hK0card⟩
    · -- no genuine Sylow-type witness (`q = 1`): `case_1_0`'s `hK` bundle is vacuous (`k = 1`);
      -- its `q = 1` conclusion gives `Nat.card G = Nat.card (As 0)`, contradicting `hp`.
      exfalso
      have hKbundle : (1 < k → k = gs 0) := fun h => absurd h (by omega)
      obtain ⟨-, hgeq⟩ | ⟨hcontra, -, -⟩ :=
        case_1_0 g q k (gs 0) hg_pos hq_pos hk_pos (hgs_ge 0) hKbundle heq
      · have hGA : Nat.card G = Nat.card (As 0) := by rw [hg, hgeq, hAs_card 0]
        exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp (hGA ▸ hAs_coprime 0).symm hp
      · omega
    · -- genuine witness: `q = Nat.card S0.toSubgroup > 1`.
      have hqS0 : Nat.card S0.toSubgroup = q := by
        rw [← hQ0eqS0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0_le).toEquiv]
        exact hQ0card
      have hSne : S0.toSubgroup ≠ ⊥ := by rw [← hQ0eqS0]; exact hQ0ne
      have hQ0elemAb : IsElementaryAbelian p S0.toSubgroup := isElementaryAbelian_of_sylow G S0 hSne
      have hK0card' : Nat.card (K0.subgroupOf G) = Nat.card (center SL(2,F)) * k := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0_le).toEquiv]; exact hK0card
      have hdisj : Disjoint S0.toSubgroup (K0.subgroupOf G) := by rw [← hQ0eqS0]; exact hQK0
      have hNG0' : normalizer (S0.toSubgroup : Set ↥G) = S0.toSubgroup ⊔ K0.subgroupOf G := by
        rw [← hQ0eqS0]; exact hNG0
      have hKbundle : (1 < k → k = gs 0) := by
        intro hklt
        rcases card_K_eq_of_one_lt_of_normalizer_eq_sylow_join G S0 hSne (K0.subgroupOf G)
            ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hK0_le)).mpr hK0cyc) hNG0' hdisj k
            hK0card' gs gt As At hAs_card
            hAt_card hComplete hklt with ⟨i, hi⟩ | ⟨j, -⟩
        · rwa [Subsingleton.elim i 0] at hi
        · exact j.elim0
      obtain ⟨hq1c, -⟩ | ⟨-, hkeq, hgeq⟩ :=
        case_1_0 g q k (gs 0) hg_pos hq_pos hk_pos (hgs_ge 0) hKbundle heq
      · exfalso; rw [hq1c] at hqS0
        exact hQ0ne (Subgroup.card_eq_one.mp (by rw [hQ0eqS0, hqS0]))
      · left
        have hcard_eq : Nat.card S0.toSubgroup * Nat.card (K0.subgroupOf G) = Nat.card G := by
          rw [hqS0, hK0card', hg, hgeq]; ring
        have hcomp : IsComplement' S0.toSubgroup (K0.subgroupOf G) :=
          isComplement'_of_card_mul_and_disjoint hcard_eq hdisj
        have hNz_top : normalizer (S0.toSubgroup : Set ↥G) = ⊤ := by
          rw [hNG0']; exact hcomp.sup_eq_top
        refine ⟨S0.toSubgroup, hQ0elemAb, normalizer_eq_top_iff.mp hNz_top,
          K0.subgroupOf G, hcomp,
          (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hK0_le)).mpr hK0cyc, ?_⟩
        have hindex_eq : S0.toSubgroup.index = Nat.card (K0.subgroupOf G) := hcomp.symm.index_eq_card
        have hp_dvd_Q : p ∣ Nat.card S0.toSubgroup :=
          hQ0elemAb.dvd_card (bot_lt_iff_ne_bot.mpr hSne)
        have hcop_index : Nat.Coprime (Nat.card S0.toSubgroup) (S0.toSubgroup).index :=
          Sylow.card_coprime_index S0
        rw [hindex_eq] at hcop_index
        exact hcop_index.coprime_dvd_left hp_dvd_Q
  · -- `(s,t) = (1,1)`: Butler's own Case II, occurring only for `p ∤ |G|` -- impossible here.
    -- `hSylow`'s no-witness disjunct (`q = 1`) makes the class equation itself contradict
    -- `p ∣ g` (`classII_arith_1_1_false`); its witness disjunct dies via `case_1_1`'s `q = 1`
    -- against the witness's `Q0.subgroupOf G ≠ ⊥` (`DIVERGENCES.md` item 12, now closed).
    exfalso
    obtain ⟨hs, ht⟩ := hst
    subst hs; subst ht
    have hgs_eq : gs = fun _ : Fin 1 => gs 0 :=
      funext fun i => congrArg gs (Subsingleton.elim i 0)
    have hgt_eq : gt = fun _ : Fin 1 => gt 0 :=
      funext fun i => congrArg gt (Subsingleton.elim i 0)
    rw [hgs_eq, hgt_eq] at heq
    -- `p ∣ g`: `p ∣ |G| = |Z|⋅g` with `p` coprime to `|Z|`.
    have hcopZ : Nat.Coprime (Nat.card (center SL(2,F))) p := by
      rw [SpecialSubgroups.center_SL2_eq_Z]
      exact NumericClassEquation.coprime_card_Z_prime
    have hpg : p ∣ g := by
      have h := hp
      rw [hg] at h
      exact (hcopZ.symm).dvd_of_dvd_mul_left h
    have hnd_gs : ¬ p ∣ gs 0 := by
      have h1 := hAs_coprime 0
      rw [hAs_card 0] at h1
      exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp
        ((Nat.Coprime.coprime_dvd_left (dvd_mul_left (gs 0) _) h1).symm)
    have hnd_gt : ¬ p ∣ gt 0 := by
      have h1 := hAt_coprime 0
      rw [hAt_card 0] at h1
      exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp
        ((Nat.Coprime.coprime_dvd_left (dvd_mul_left (gt 0) _) h1).symm)
    rcases hSylow with ⟨hq1, -⟩ |
      ⟨Q0, K0, S0, hQ0_le, hQ0eqS0, hQ0ne, hQ0card, hK0_le, hK0cyc, hNG0, hQK0, hK0card⟩
    · -- no Sylow-type witness (`q = 1`): the class equation itself contradicts `p ∣ g`.
      rw [hq1] at heq
      exact classII_arith_1_1_false (Fact.out : Nat.Prime p) hp2 g k (gs 0) (gt 0)
        hg_pos (hgs_ge 0) (hgt_ge 0) heq hpg hnd_gs hnd_gt
    · -- genuine witness: `case_1_1` forces `q = 1`, contradicting `Q0.subgroupOf G ≠ ⊥`.
      have hqS0 : Nat.card S0.toSubgroup = q := by
        rw [← hQ0eqS0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0_le).toEquiv]
        exact hQ0card
      have hSne : S0.toSubgroup ≠ ⊥ := by rw [← hQ0eqS0]; exact hQ0ne
      have hK0card' : Nat.card (K0.subgroupOf G) = Nat.card (center SL(2,F)) * k := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0_le).toEquiv]; exact hK0card
      have hdisj : Disjoint S0.toSubgroup (K0.subgroupOf G) := by rw [← hQ0eqS0]; exact hQK0
      have hNG0' : normalizer (S0.toSubgroup : Set ↥G) = S0.toSubgroup ⊔ K0.subgroupOf G := by
        rw [← hQ0eqS0]; exact hNG0
      have hKbundle : gt 0 < k → k = gs 0 := by
        intro hklt
        have hklt1 : 1 < k := by have := hgt_ge 0; omega
        rcases card_K_eq_of_one_lt_of_normalizer_eq_sylow_join G S0 hSne (K0.subgroupOf G)
            ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hK0_le)).mpr hK0cyc) hNG0' hdisj k
            hK0card' gs gt As At hAs_card
            hAt_card hComplete hklt1 with ⟨i, hi⟩ | ⟨j, hj⟩
        · rwa [Subsingleton.elim i 0] at hi
        · rw [Subsingleton.elim j 0] at hj; omega
      obtain ⟨hq1, -⟩ := case_1_1 g q k (gs 0) (gt 0) hg_pos hq_pos hk_pos (hgs_ge 0)
        (hgt_ge 0) hKbundle heq
      rw [hq1] at hqS0
      exact hQ0ne (Subgroup.card_eq_one.mp (by rw [hQ0eqS0, hqS0]))
  · -- `(s,t) = (0,0)`: `case_III`.
    obtain ⟨hs, ht⟩ := hst
    subst hs; subst ht
    have hgs_eq : gs = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
    have hgt_eq : gt = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
    rw [hgs_eq, hgt_eq] at heq
    rcases hSylow with ⟨hq1, hk1⟩ |
      ⟨Q0, K0, S0, hQ0_le, hQ0eqS0, hQ0ne, hQ0card, hK0_le, hK0cyc, hNG0, hQK0, hK0card⟩
    · -- `q = 1, k = 1`: `case_0_0` gives `g = q = 1`, so `Nat.card G = Nat.card (center SL(2,F))`,
      -- contradicting `hp` via `coprime_card_Z_prime`.
      exfalso
      have hKle : k ≤ 1 := le_of_eq hk1
      obtain ⟨-, hgq⟩ := case_0_0 g q k hg_pos hq_pos hk_pos hKle heq
      have hG1 : Nat.card G = Nat.card (center SL(2,F)) := by rw [hg, hgq, hq1, mul_one]
      have hcop : Nat.Coprime (Nat.card G) p := by
        rw [hG1, SpecialSubgroups.center_SL2_eq_Z]; exact NumericClassEquation.coprime_card_Z_prime
      exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop.symm hp
    · -- genuine witness: `k ≤ 1` since `s = t = 0` leaves no coprime-type class for a nontrivial
      -- `K0` to be conjugate to (`card_K_eq_of_one_lt_of_normalizer_eq_sylow_join`).
      have hqS0 : Nat.card S0.toSubgroup = q := by
        rw [← hQ0eqS0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0_le).toEquiv]
        exact hQ0card
      have hSne : S0.toSubgroup ≠ ⊥ := by rw [← hQ0eqS0]; exact hQ0ne
      have hQ0elemAb : IsElementaryAbelian p S0.toSubgroup := isElementaryAbelian_of_sylow G S0 hSne
      have hK0card' : Nat.card (K0.subgroupOf G) = Nat.card (center SL(2,F)) * k := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0_le).toEquiv]; exact hK0card
      have hdisj : Disjoint S0.toSubgroup (K0.subgroupOf G) := by rw [← hQ0eqS0]; exact hQK0
      have hNG0' : normalizer (S0.toSubgroup : Set ↥G) = S0.toSubgroup ⊔ K0.subgroupOf G := by
        rw [← hQ0eqS0]; exact hNG0
      have hKle : k ≤ 1 := by
        by_contra hcon
        have hklt : 1 < k := by omega
        rcases card_K_eq_of_one_lt_of_normalizer_eq_sylow_join G S0 hSne (K0.subgroupOf G)
            ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hK0_le)).mpr hK0cyc) hNG0' hdisj k
            hK0card' gs gt As At hAs_card
            hAt_card hComplete hklt with ⟨i, -⟩ | ⟨j, -⟩
        · exact i.elim0
        · exact j.elim0
      obtain ⟨hk1, hgq⟩ := case_0_0 g q k hg_pos hq_pos hk_pos hKle heq
      left
      have hcard_eq : Nat.card S0.toSubgroup * Nat.card (K0.subgroupOf G) = Nat.card G := by
        rw [hqS0, hK0card', hg, hgq, hk1]; ring
      have hcomp : IsComplement' S0.toSubgroup (K0.subgroupOf G) :=
        isComplement'_of_card_mul_and_disjoint hcard_eq hdisj
      have hNz_top : normalizer (S0.toSubgroup : Set ↥G) = ⊤ := by
        rw [hNG0']; exact hcomp.sup_eq_top
      refine ⟨S0.toSubgroup, hQ0elemAb, normalizer_eq_top_iff.mp hNz_top,
        K0.subgroupOf G, hcomp,
        (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hK0_le)).mpr hK0cyc, ?_⟩
      have hindex_eq : S0.toSubgroup.index = Nat.card (K0.subgroupOf G) := hcomp.symm.index_eq_card
      have hp_dvd_Q : p ∣ Nat.card S0.toSubgroup := hQ0elemAb.dvd_card (bot_lt_iff_ne_bot.mpr hSne)
      have hcop_index : Nat.Coprime (Nat.card S0.toSubgroup) (S0.toSubgroup).index :=
        Sylow.card_coprime_index S0
      rw [hindex_eq] at hcop_index
      exact hcop_index.coprime_dvd_left hp_dvd_Q
  · -- `(s,t) = (0,1)`: `case_IV`. `q ∈ {2,3}` unconditionally (`case_0_1`), so `1 < q` always.
    obtain ⟨hs, ht⟩ := hst
    subst hs; subst ht
    have hgs_eq : gs = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
    have hgt_eq : gt = fun _ : Fin 1 => gt 0 := funext fun i => congrArg gt (Subsingleton.elim i 0)
    rw [hgs_eq, hgt_eq] at heq
    have hg_ge : 2 * gt 0 ≤ g := by
      have h2card : 2 * Nat.card (At 0) ≤ Nat.card G :=
        two_card_le_of_relIndex_normalizer_eq_two G (At 0) (hAt_mem 0).right (hAt_relIndex 0)
      rw [hAt_card 0, hg] at h2card
      have he : 0 < Nat.card (center SL(2,F)) := Nat.card_pos
      have hrw : 2 * (Nat.card (center SL(2,F)) * gt 0)
          = Nat.card (center SL(2,F)) * (2 * gt 0) := by ring
      rw [hrw] at h2card
      exact le_of_mul_le_mul_left h2card he
    obtain ⟨-, hcase⟩ := case_0_1 g q k (gt 0) hg_pos hq_pos hk_pos (hgt_ge 0) hg_ge heq
    have hq_gt1 : 1 < q := by rcases hcase with ⟨hq2, -⟩ | ⟨hq3, -, -⟩ <;> omega
    rcases hSylow with ⟨hq1, -⟩ |
      ⟨Q0, K0, S0, hQ0_le, hQ0eqS0, hQ0ne, hQ0card, hK0_le, hK0cyc, hNG0, hQK0, hK0card⟩
    · omega
    · have hqS0 : Nat.card S0.toSubgroup = q := by
        rw [← hQ0eqS0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0_le).toEquiv]
        exact hQ0card
      have hComplete' : ∀ B ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B = At 0) ∨
          NumericClassEquation.IsSylowType p G B := by
        intro B hB
        rcases hComplete B hB with ⟨i, -, -, -⟩ | ⟨j, c, hcG, hc⟩ | hsyl
        · exact i.elim0
        · rw [Subsingleton.elim j 0] at hc; exact Or.inl ⟨c, hcG, hc⟩
        · exact Or.inr hsyl
      rcases case_IV G center_le_G S0 g q hg hqS0 (gt 0) k (At 0) (hAt_mem 0) (hAt_cyclic 0)
          (hAt_coprime 0) (hAt_card 0) (hAt_relIndex 0) hComplete'
          ⟨hk_pos, hgt_ge 0, hg_ge, heq⟩ with ⟨hp2eq, -⟩ | ⟨hp3, hiso⟩
      · exact absurd hp2eq hp2
      · -- `p = 3`: bridge `Isomorphic G SL(2,ZMod 3)` to item (ix) at `k := 1`
        -- (`SL(2,GaloisField 3 1) ≃* SL(2,ZMod 3)` via `GaloisField.equivZmodP`).
        subst hp3
        right; right; right; left
        obtain ⟨e⟩ := hiso
        exact ⟨(1 : ℕ+),
          ⟨e.trans (SL2_mulEquiv_of_ringEquiv (GaloisField.equivZmodP (p := 3)).toRingEquiv).symm⟩⟩
  · -- `(s,t) = (0,2)`: `case_V`. `1 < q` unconditionally (`case_0_2`).
    obtain ⟨hs, ht⟩ := hst
    subst hs; subst ht
    have hgs_eq : gs = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
    have hgt_eq : gt = ![gt 0, gt 1] := by funext i; fin_cases i <;> simp
    rw [hgs_eq, hgt_eq] at heq
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
    rcases hSylow with ⟨hq1, -⟩ |
      ⟨Q0, K0, S0, hQ0_le, hQ0eqS0, hQ0ne, hQ0card, hK0_le, hK0cyc, hNG0, hQK0, hK0card⟩
    · omega
    · have hqS0 : Nat.card S0.toSubgroup = q := by
        rw [← hQ0eqS0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0_le).toEquiv]
        exact hQ0card
      have hSne : S0.toSubgroup ≠ ⊥ := by rw [← hQ0eqS0]; exact hQ0ne
      have hNG0' : normalizer (S0.toSubgroup : Set ↥G) = S0.toSubgroup ⊔ K0.subgroupOf G := by
        rw [← hQ0eqS0]; exact hNG0
      have hdisj : Disjoint S0.toSubgroup (K0.subgroupOf G) := by
        rw [← hQ0eqS0]; exact hQK0
      have hK0card' : Nat.card (K0.subgroupOf G) = Nat.card (center SL(2,F)) * k := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0_le).toEquiv]; exact hK0card
      have hKbundle : 1 < k → k = gt 0 ∨ k = gt 1 := by
        intro hklt
        rcases card_K_eq_of_one_lt_of_normalizer_eq_sylow_join G S0 hSne (K0.subgroupOf G)
            ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hK0_le)).mpr hK0cyc) hNG0' hdisj k
            hK0card' gs gt As At hAs_card hAt_card hComplete hklt with ⟨i, -⟩ | ⟨j, hj⟩
        · exact i.elim0
        · fin_cases j
          · exact Or.inl hj
          · exact Or.inr hj
      have hComplete' : ∀ B ∈ MaximalAbelianSubgroupsOf G, (∃ c ∈ G, conj c • B = At 0) ∨
          (∃ c ∈ G, conj c • B = At 1) ∨ NumericClassEquation.IsSylowType p G B := by
        intro B hB
        rcases hComplete B hB with ⟨i, -, -, -⟩ | ⟨j, c, hcG, hc⟩ | hsyl
        · exact i.elim0
        · fin_cases j
          · exact Or.inl ⟨c, hcG, hc⟩
          · exact Or.inr (Or.inl ⟨c, hcG, hc⟩)
        · exact Or.inr (Or.inr hsyl)
      rcases case_V G center_le_G S0 g q hg hqS0 (gt 0) (gt 1) k
          (At 0) (hAt_mem 0) (hAt_cyclic 0) (hAt_coprime 0) (hAt_card 0) (hAt_relIndex 0)
          (At 1) (hAt_mem 1) (hAt_cyclic 1) (hAt_coprime 1) (hAt_card 1) (hAt_relIndex 1)
          K0 hK0_le hK0cyc hK0card hNG0' hdisj hKbundle hComplete'
          ⟨hk_pos, hgt_ge 0, hgt_ge 1, hg_ge1, hg_ge2, heq⟩ with h9 | h10 | h8
      · exact Or.inr (Or.inr (Or.inr (Or.inl h9)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h10)))
      · exact Or.inr (Or.inr (Or.inl h8))
  · -- `(s,t) = (0,3)`: Butler's own Case VI, occurring only for `p ∤ |G|` -- impossible here,
    -- by the same two-pronged argument as the `(1,1)` branch above (`classII_arith_0_3_false`
    -- for `hSylow`'s no-witness disjunct, `case_0_3`'s `q = 1` against the witness's
    -- `Q0.subgroupOf G ≠ ⊥` for the other; `DIVERGENCES.md` item 12, now closed).
    exfalso
    obtain ⟨hs, ht⟩ := hst
    subst hs; subst ht
    have hgs_eq : gs = fun i : Fin 0 => i.elim0 := funext fun i => i.elim0
    have hgt_eq : gt = ![gt 0, gt 1, gt 2] := by funext i; fin_cases i <;> simp
    rw [hgs_eq, hgt_eq] at heq
    -- `p ∣ g`: `p ∣ |G| = |Z|⋅g` with `p` coprime to `|Z|`.
    have hcopZ : Nat.Coprime (Nat.card (center SL(2,F))) p := by
      rw [SpecialSubgroups.center_SL2_eq_Z]
      exact NumericClassEquation.coprime_card_Z_prime
    have hpg : p ∣ g := by
      have h := hp
      rw [hg] at h
      exact (hcopZ.symm).dvd_of_dvd_mul_left h
    have hnd_gt : ∀ j : Fin 3, ¬ p ∣ gt j := by
      intro j
      have h1 := hAt_coprime j
      rw [hAt_card j] at h1
      exact (Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp
        ((Nat.Coprime.coprime_dvd_left (dvd_mul_left (gt j) _) h1).symm)
    rcases hSylow with ⟨hq1, -⟩ |
      ⟨Q0, K0, S0, hQ0_le, hQ0eqS0, hQ0ne, hQ0card, hK0_le, hK0cyc, hNG0, hQK0, hK0card⟩
    · -- no Sylow-type witness (`q = 1`): the class equation itself contradicts `p ∣ g`.
      rw [hq1] at heq
      exact classII_arith_0_3_false (Fact.out : Nat.Prime p) hp2 g k (gt 0) (gt 1) (gt 2)
        hg_pos (hgt_ge 0) (hgt_ge 1) (hgt_ge 2) heq hpg (hnd_gt 0) (hnd_gt 1) (hnd_gt 2)
    · -- genuine witness: `case_0_3` forces `q = 1`, contradicting `Q0.subgroupOf G ≠ ⊥`.
      have hqS0 : Nat.card S0.toSubgroup = q := by
        rw [← hQ0eqS0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQ0_le).toEquiv]
        exact hQ0card
      have hSne : S0.toSubgroup ≠ ⊥ := by rw [← hQ0eqS0]; exact hQ0ne
      have hK0card' : Nat.card (K0.subgroupOf G) = Nat.card (center SL(2,F)) * k := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0_le).toEquiv]; exact hK0card
      have hdisj : Disjoint S0.toSubgroup (K0.subgroupOf G) := by rw [← hQ0eqS0]; exact hQK0
      have hNG0' : normalizer (S0.toSubgroup : Set ↥G) = S0.toSubgroup ⊔ K0.subgroupOf G := by
        rw [← hQ0eqS0]; exact hNG0
      have hKbundle : 1 < k → k = gt 0 ∨ k = gt 1 ∨ k = gt 2 := by
        intro hklt1
        rcases card_K_eq_of_one_lt_of_normalizer_eq_sylow_join G S0 hSne (K0.subgroupOf G)
            ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hK0_le)).mpr hK0cyc) hNG0' hdisj k
            hK0card' gs gt As At hAs_card
            hAt_card hComplete hklt1 with ⟨i, -⟩ | ⟨j, hj⟩
        · exact i.elim0
        · fin_cases j
          · exact Or.inl hj
          · exact Or.inr (Or.inl hj)
          · exact Or.inr (Or.inr hj)
      have hq1 := case_0_3 g q k (gt 0) (gt 1) (gt 2) hg_pos hq_pos hk_pos (hgt_ge 0)
        (hgt_ge 1) (hgt_ge 2) hKbundle heq
      rw [hq1] at hqS0
      exact hQ0ne (Subgroup.card_eq_one.mp (by rw [hQ0eqS0, hqS0]))
-- ANCHOR_END: dicksons_classification_theorem_class_II



variable (n : Type*) [DecidableEq n] [Fintype n] (R : Type*) [CommRing R]

open Matrix LinearMap Subgroup

open scoped MatrixGroups


/-- A projective general linear group is the quotient of a special linear group by its center. -/
abbrev ProjectiveGeneralLinearGroup' : Type _ :=
    GL n R ⧸ center (GL n R)


/-! ### Descent from `SL(2, F̄_p)` to `PGL(2, F̄_p)`

`FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod` below is obtained from
`dicksons_classification_theorem_class_I/II` by pulling a finite subgroup `G ≤ PGL(2, F̄_p)`
back along the 2-to-1 covering `SL(2, F̄_p) → PGL(2, F̄_p)` (surjective with kernel
`center SL(2,F̄_p) = {±1}` since `F̄_p` is algebraically closed,
`Ch4_PGLIsoPSLOverAlgClosedField`) and pushing each disjunct of the `SL₂`-classification of the
pullback down through the quotient by the order-`2` kernel. The `pgl_descent_*` lemmas below are
the per-disjunct quotient identifications; two genuinely missing recognition facts remain
isolated as documented `sorry`s (`pgl_descent_binaryOctahedral_quotient`,
`pgl_descent_SL2_join_d_quotient`); `pgl_descent_PSL2_ZMod3_iso_alternating` and
`pgl_descent_PSL2_ZMod5_iso_alternating` are fully proven (Waves 18/20). -/

/-- In a field of characteristic `p ≠ 2`, `2 ≠ 0`. -/
lemma pgl_descent_neZero_two (K : Type*) [Field K] (p : ℕ) [Fact (Nat.Prime p)] [CharP K p]
    (hp2 : p ≠ 2) : NeZero (2 : K) := by
  refine ⟨fun h => hp2 ?_⟩
  have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp h2
  exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hdvd

/-! ### `SL(2, 𝔽₅)` and `PSL(2, 𝔽₅)` are perfect (transvection generation)

These feed the `PSL(2,5) ≅ A₅` leaf (`pgl_descent_PSL2_ZMod5_iso_alternating`): the sign
character of any permutation representation of `PSL(2,5)` is trivial, so the image lands in the
alternating group. -/

/-- coe of the mathlib upper transvection to `!![1,c;0,1]`. -/
lemma pgl_descent_uc_coe {F : Type*} [Field F] (c : F) :
    ((SpecialLinearGroup.transvection (zero_ne_one) c : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F) = !![1, c; 0, 1] := by
  rw [SpecialLinearGroup.transvection_coe]
  apply Matrix.ext; intro i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]

/-- coe of `w` to `!![0,1;-1,0]`. -/
lemma pgl_descent_w_coe {F : Type*} [Field F] :
    ((SpecialMatrices.w : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

/-- `w * uc c * w⁻¹ = s (-c)` : conjugating the upper shear by `w` gives a lower shear. -/
lemma pgl_descent_s_eq_conj {F : Type*} [Field F] (c : F) :
    SpecialMatrices.s (-c) =
      SpecialMatrices.w * (SpecialLinearGroup.transvection (zero_ne_one) c) *
        (SpecialMatrices.w)⁻¹ := by
  rw [SpecialMatrices.inv_w_eq_neg_w]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialMatrices.s, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_neg, pgl_descent_uc_coe, pgl_descent_w_coe, Matrix.neg_apply]

/-- `uc 1 * s(-1) * uc 1 = w`. -/
lemma pgl_descent_w_eq_prod {F : Type*} [Field F] :
    (SpecialMatrices.w : SL(2, F)) =
      (SpecialLinearGroup.transvection (zero_ne_one) 1) * SpecialMatrices.s (-1) *
        (SpecialLinearGroup.transvection (zero_ne_one) 1) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialMatrices.s, SpecialMatrices.w, SpecialLinearGroup.transvection_coe,
      Matrix.single_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.add_apply, Matrix.one_apply]

/-- `uc δ * s(-δ⁻¹) * uc δ = dw δ`. -/
lemma pgl_descent_dw_eq_prod {F : Type*} [Field F] (δ : Fˣ) :
    (SpecialMatrices.dw δ : SL(2, F)) =
      (SpecialLinearGroup.transvection (zero_ne_one) (δ : F)) *
        SpecialMatrices.s (-((δ : F)⁻¹)) *
        (SpecialLinearGroup.transvection (zero_ne_one) (δ : F)) := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialMatrices.s, SpecialMatrices.dw, SpecialLinearGroup.transvection_coe,
      Matrix.single_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.add_apply, Matrix.one_apply,
      mul_inv_cancel₀ δ.ne_zero]

/-- **Generation / perfectness of `SL(2, F)`.** If `F` has an element `a ≠ 0` with `a² ≠ 1`
(i.e. `F` is not `𝔽₂` or `𝔽₃`), then `SL(2, F)` is perfect: every element is a product of
transvections and det-`1` diagonals (mathlib Gaussian elimination
`Matrix.diagonal_transvection_induction`), the upper transvections lie in the commutator subgroup
(`transvection_mem_commutator`), and lower transvections/diagonals follow by normality of the
commutator together with an explicit shear decomposition. -/
theorem pgl_descent_SL2_commutator_eq_top {F : Type*} [Field F]
    (a : F) (ha : a ≠ 0) (ha2 : a ^ 2 ≠ 1) :
    commutator SL(2, F) = ⊤ := by
  haveI hN : (commutator SL(2, F)).Normal := inferInstance
  have huc : ∀ c : F, (SpecialLinearGroup.transvection (zero_ne_one) c : SL(2, F)) ∈
      commutator SL(2, F) :=
    fun c => transvection_mem_commutator a ha ha2 c
  have hs : ∀ σ : F, (SpecialMatrices.s σ : SL(2, F)) ∈ commutator SL(2, F) := by
    intro σ
    have := hN.conj_mem _ (huc (-σ)) SpecialMatrices.w
    rw [← pgl_descent_s_eq_conj (-σ), neg_neg] at this
    exact this
  have hw : (SpecialMatrices.w : SL(2, F)) ∈ commutator SL(2, F) := by
    rw [pgl_descent_w_eq_prod]
    exact (commutator SL(2, F)).mul_mem
      ((commutator SL(2, F)).mul_mem (huc 1) (hs (-1))) (huc 1)
  have hd : ∀ δ : Fˣ, (SpecialMatrices.d δ : SL(2, F)) ∈ commutator SL(2, F) := by
    intro δ
    have hdw : (SpecialMatrices.dw δ : SL(2, F)) ∈ commutator SL(2, F) := by
      rw [pgl_descent_dw_eq_prod]
      exact (commutator SL(2, F)).mul_mem
        ((commutator SL(2, F)).mul_mem (huc _) (hs _)) (huc _)
    have hid : SpecialMatrices.d δ = SpecialMatrices.dw δ * (SpecialMatrices.w)⁻¹ := by
      rw [← SpecialMatrices.d_mul_w_eq_dw, mul_assoc, mul_inv_cancel, mul_one]
    rw [hid]
    exact (commutator SL(2, F)).mul_mem hdw ((commutator SL(2, F)).inv_mem hw)
  -- generation via Gaussian elimination
  rw [eq_top_iff]
  intro A _
  obtain ⟨S, hScoe, hmem⟩ := Matrix.diagonal_transvection_induction
    (fun M => ∃ S : SL(2, F), (S : Matrix (Fin 2) (Fin 2) F) = M ∧ S ∈ commutator SL(2, F))
    (A : Matrix (Fin 2) (Fin 2) F)
    (fun D hD => by
      have hdet : D 0 * D 1 = 1 := by
        have hd1 : (Matrix.diagonal D).det = 1 := by rw [hD]; exact A.2
        rwa [Matrix.det_diagonal, Fin.prod_univ_two] at hd1
      have hD0 : D 0 ≠ 0 := by
        rintro h0; rw [h0, zero_mul] at hdet; exact zero_ne_one hdet
      refine ⟨SpecialMatrices.d (Units.mk0 (D 0) hD0), ?_, hd _⟩
      rw [SpecialMatrices.d_coe_eq]
      apply Matrix.ext; intro i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Units.val_mk0]
      · rw [inv_eq_one_div, div_eq_iff hD0, mul_comm]; exact hdet.symm)
    (fun t => by
      obtain ⟨i, j, hij, c⟩ := t
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · refine ⟨SpecialLinearGroup.transvection (zero_ne_one) c, ?_, huc c⟩
        rw [pgl_descent_uc_coe]
        apply Matrix.ext; intro a b
        fin_cases a <;> fin_cases b <;>
          simp [TransvectionStruct.toMatrix, Matrix.transvection, Matrix.single_apply]
      · refine ⟨SpecialMatrices.s c, ?_, hs c⟩
        apply Matrix.ext; intro a b
        fin_cases a <;> fin_cases b <;>
          simp [SpecialMatrices.s, TransvectionStruct.toMatrix, Matrix.transvection,
            Matrix.single_apply]
      · exact absurd rfl hij)
    (fun A' B' hA' hB' => by
      obtain ⟨SA, hSA, hmA⟩ := hA'
      obtain ⟨SB, hSB, hmB⟩ := hB'
      refine ⟨SA * SB, ?_, (commutator SL(2, F)).mul_mem hmA hmB⟩
      rw [← hSA, ← hSB]
      exact Matrix.SpecialLinearGroup.coe_mul SA SB)
  have hSA : S = A :=
    (Matrix.SpecialLinearGroup.ext_iff S A).mpr (fun i j => congrFun (congrFun hScoe i) j)
  rwa [hSA] at hmem

/-- `SL(2, ZMod 5)` is perfect. -/
theorem pgl_descent_SL2_ZMod5_isPerfect : Group.IsPerfect SL(2, ZMod 5) :=
  (Group.isPerfect_def).mpr
    (pgl_descent_SL2_commutator_eq_top (2 : ZMod 5) (by decide) (by decide))

/-- `PSL(2, ZMod 5)` is perfect (quotient of a perfect group by its center). -/
theorem pgl_descent_PSL2_ZMod5_isPerfect : Group.IsPerfect (PSL (Fin 2) (ZMod 5)) := by
  haveI := pgl_descent_SL2_ZMod5_isPerfect
  infer_instance

/-- **Sign character is trivial on `PSL(2,5)`.** Any homomorphism `PSL(2,5) →* Perm (Fin m)` has
its range inside the alternating group: the sign character `sign ∘ g : PSL(2,5) →* ℤˣ` kills the
commutator subgroup, which by perfectness is all of `PSL(2,5)`. -/
theorem pgl_descent_PSL2_ZMod5_range_le_alternatingGroup {m : ℕ}
    (g : PSL (Fin 2) (ZMod 5) →* Equiv.Perm (Fin m)) :
    g.range ≤ alternatingGroup (Fin m) := by
  haveI := pgl_descent_PSL2_ZMod5_isPerfect
  set χ : PSL (Fin 2) (ZMod 5) →* ℤˣ := Equiv.Perm.sign.comp g with hχ
  have hker : commutator (PSL (Fin 2) (ZMod 5)) ≤ χ.ker := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro p _ q _
    rw [MonoidHom.mem_ker, _root_.map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)
  intro y hy
  obtain ⟨x, rfl⟩ := hy
  have hx : x ∈ χ.ker := hker (Group.IsPerfect.mem_commutator)
  rw [MonoidHom.mem_ker] at hx
  rw [Equiv.Perm.mem_alternatingGroup]
  have hval : χ x = Equiv.Perm.sign (g x) := rfl
  rw [hval] at hx
  exact hx

/-- A subgroup of order `2` is generated by an involution. -/
lemma pgl_descent_exists_involution_generator {T : Type*} [Group T] (W : Subgroup T)
    (hW : Nat.card W = 2) :
    ∃ z : T, z ∈ W ∧ z ≠ 1 ∧ z ^ 2 = 1 ∧ W = Subgroup.zpowers z := by
  haveI : Finite W := Nat.finite_of_card_ne_zero (by rw [hW]; norm_num)
  haveI : Nontrivial W := by
    obtain ⟨x, y, hxy, -⟩ := Nat.card_eq_two_iff.mp hW
    exact ⟨⟨x, y, hxy⟩⟩
  obtain ⟨z, hzne⟩ := exists_ne (1 : W)
  have hord : orderOf z = 2 := by
    have hdvd : orderOf z ∣ 2 := hW ▸ orderOf_dvd_natCard z
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hzne
    · exact h2
  have hz2 : z ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one z
  refine ⟨z.1, z.2, ?_, ?_, ?_⟩
  · intro h
    exact hzne (Subtype.ext (by rw [h]; rfl))
  · simpa using congrArg Subtype.val hz2
  · have hle : Subgroup.zpowers z.1 ≤ W := Subgroup.zpowers_le.mpr z.2
    have hoz : orderOf z.1 = 2 := by
      rw [← hord]
      exact orderOf_injective W.subtype (Subgroup.subtype_injective W) z
    have hcard : Nat.card W ≤ Nat.card (Subgroup.zpowers z.1) := by
      rw [hW, Nat.card_zpowers, hoz]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

/-- The unique involution of `SL(2,F)` (char `F ≠ 2`) is `-1` (Butler Lemma 1.4,
`SpecialSubgroups.exists_unique_orderOf_eq_two`). -/
lemma pgl_descent_involution_eq_neg_one {F : Type*} [Field F] [NeZero (2 : F)]
    {z : SL(2,F)} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) : z = -1 := by
  obtain ⟨w, hword, huniq⟩ := SpecialSubgroups.exists_unique_orderOf_eq_two (F := F)
  have h1 : z = w := huniq z (orderOf_eq_prime hz2 hz1)
  have h2 : (-1 : SL(2,F)) = w := huniq (-1) SpecialSubgroups.orderOf_neg_one_eq_two
  rw [h1, ← h2]

/-- An order-`2` subgroup of `SL(2,F)` (char `F ≠ 2`) is the center `{±1}`. -/
lemma pgl_descent_card_two_eq_center_SL2 {F : Type*} [Field F] [NeZero (2 : F)]
    (W : Subgroup SL(2,F)) (hW : Nat.card W = 2) : W = center SL(2,F) := by
  obtain ⟨z, hzW, hz1, hz2, hWz⟩ := pgl_descent_exists_involution_generator W hW
  have hzneg : z = -1 := pgl_descent_involution_eq_neg_one hz2 hz1
  haveI : Finite (center SL(2,F)) := by
    rw [SpecialSubgroups.center_SL2_eq_Z]
    infer_instance
  apply Subgroup.eq_of_le_of_card_ge
  · rw [hWz, Subgroup.zpowers_le, hzneg, SpecialSubgroups.center_SL2_eq_Z]
    exact SpecialSubgroups.neg_one_mem_Z
  · rw [hW, SpecialSubgroups.center_SL2_eq_Z, SpecialSubgroups.card_Z_eq_two_of_two_ne_zero]

/-- If `m ∣ i.val` for `i : ZMod (2*m)`, then `i = 0` or `i = m`. -/
private lemma pgl_descent_zmod_val_aux {m : ℕ} [NeZero m] {i : ZMod (2 * m)}
    (hdvd : m ∣ i.val) : i = 0 ∨ i = (m : ZMod (2 * m)) := by
  haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  obtain ⟨c, hc⟩ := hdvd
  have hlt : i.val < 2 * m := ZMod.val_lt i
  have h1 : m * c < m * 2 := by rw [← hc, mul_comm m 2]; exact hlt
  have hc2 : c < 2 := Nat.lt_of_mul_lt_mul_left h1
  have hc01 : c = 0 ∨ c = 1 := by omega
  rcases hc01 with rfl | rfl
  · left
    rw [← ZMod.natCast_zmod_val i, hc, mul_zero, Nat.cast_zero]
  · right
    rw [← ZMod.natCast_zmod_val i, hc, mul_one]

/-- The unique involution of the dicyclic group `QuaternionGroup m` (`m ≥ 1`) is `a m`. -/
lemma pgl_descent_quaternion_involution {m : ℕ} [NeZero m] {z : QuaternionGroup m}
    (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) : z = QuaternionGroup.a ((m : ZMod (2 * m))) := by
  haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  rcases z with i | i
  · rw [pow_two, QuaternionGroup.a_mul_a, ← QuaternionGroup.a_zero] at hz2
    injection hz2 with h
    have h2 : ((i.val + i.val : ℕ) : ZMod (2 * m)) = 0 := by
      rw [Nat.cast_add, ZMod.natCast_zmod_val, h]
    have h3 : 2 * m ∣ i.val + i.val := (CharP.cast_eq_zero_iff (ZMod (2 * m)) (2 * m) _).mp h2
    have hdvd : m ∣ i.val := by
      rw [← two_mul] at h3
      exact (mul_dvd_mul_iff_left (two_ne_zero (α := ℕ))).mp h3
    rcases pgl_descent_zmod_val_aux hdvd with h0 | hm
    · exact absurd (by rw [h0]; exact QuaternionGroup.a_zero) hz1
    · rw [hm]
  · have h4 : orderOf (QuaternionGroup.xa i) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
    rw [QuaternionGroup.orderOf_xa] at h4
    norm_num at h4

private def pgl_descent_quatToDihFun (m : ℕ) : QuaternionGroup m → DihedralGroup m
  | .a i => .r ((ZMod.castHom (dvd_mul_left m 2) (ZMod m)) i)
  | .xa i => .sr ((ZMod.castHom (dvd_mul_left m 2) (ZMod m)) i)

/-- The canonical projection of the dicyclic group onto the dihedral group,
`a i ↦ r i`, `x a i ↦ s r i` (kernel: the central `⟨a m⟩ = {1, a m}`). -/
def pgl_descent_quaternionToDihedral (m : ℕ) : QuaternionGroup m →* DihedralGroup m :=
  MonoidHom.mk' (pgl_descent_quatToDihFun m) (by
    rintro (i | i) (j | j) <;>
      simp [pgl_descent_quatToDihFun, DihedralGroup.r_mul_r, DihedralGroup.r_mul_sr,
        DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr])

lemma pgl_descent_quaternionToDihedral_surjective (m : ℕ) [NeZero m] :
    Function.Surjective (pgl_descent_quaternionToDihedral m) := by
  haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  rintro (j | j)
  · exact ⟨QuaternionGroup.a ((j.val : ZMod (2 * m))), by
      show DihedralGroup.r _ = _
      rw [map_natCast, ZMod.natCast_zmod_val]⟩
  · exact ⟨QuaternionGroup.xa ((j.val : ZMod (2 * m))), by
      show DihedralGroup.sr _ = _
      rw [map_natCast, ZMod.natCast_zmod_val]⟩

lemma pgl_descent_quaternionToDihedral_ker (m : ℕ) [NeZero m] :
    (pgl_descent_quaternionToDihedral m).ker
      = Subgroup.zpowers (QuaternionGroup.a ((m : ZMod (2 * m)))) := by
  haveI : NeZero (2 * m) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  apply le_antisymm
  · intro z hz
    rw [MonoidHom.mem_ker] at hz
    rcases z with i | i
    · have h1 : DihedralGroup.r ((ZMod.castHom (dvd_mul_left m 2) (ZMod m)) i) = 1 := hz
      rw [DihedralGroup.one_def] at h1
      injection h1 with hci
      have h2 : ((i.val : ℕ) : ZMod m) = 0 := by
        have h3 : (ZMod.castHom (dvd_mul_left m 2) (ZMod m)) ((i.val : ZMod (2 * m))) = 0 := by
          rw [ZMod.natCast_zmod_val i]; exact hci
        rwa [map_natCast] at h3
      have hdvd : m ∣ i.val := (CharP.cast_eq_zero_iff (ZMod m) m i.val).mp h2
      rcases pgl_descent_zmod_val_aux hdvd with h0 | hm
      · rw [h0, QuaternionGroup.a_zero]
        exact Subgroup.one_mem _
      · rw [hm]
        exact Subgroup.mem_zpowers _
    · have h1 : DihedralGroup.sr ((ZMod.castHom (dvd_mul_left m 2) (ZMod m)) i) = 1 := hz
      rw [DihedralGroup.one_def] at h1
      injection h1
  · rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    show DihedralGroup.r ((ZMod.castHom (dvd_mul_left m 2) (ZMod m)) ((m : ZMod (2 * m)))) = 1
    rw [map_natCast, ZMod.natCast_self]
    exact DihedralGroup.r_zero

/-- `QuaternionGroup m` modulo any order-`2` subgroup is `DihedralGroup m`: the order-`2`
subgroup is forced to be the central `⟨a m⟩` (unique involution,
`pgl_descent_quaternion_involution`), and `pgl_descent_quaternionToDihedral` realizes the
quotient. This is the Class I item (ii) → dihedral step of the `PGL₂` descent (tex 2213-2254,
README item 3: `D_{2r}`). -/
lemma pgl_descent_quaternion_quotient (m : ℕ) [NeZero m] (W : Subgroup (QuaternionGroup m))
    [W.Normal] (hW : Nat.card W = 2) :
    Nonempty ((QuaternionGroup m ⧸ W) ≃* DihedralGroup m) := by
  obtain ⟨z, hzW, hz1, hz2, hWz⟩ := pgl_descent_exists_involution_generator W hW
  have hza : z = QuaternionGroup.a ((m : ZMod (2 * m))) :=
    pgl_descent_quaternion_involution hz2 hz1
  have hker : W = (pgl_descent_quaternionToDihedral m).ker := by
    rw [hWz, hza, pgl_descent_quaternionToDihedral_ker]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective _
      (pgl_descent_quaternionToDihedral_surjective m))⟩

/-- The image of an elementary abelian subgroup under any homomorphism is elementary abelian
(cf. `IsElementaryAbelian_map_of_injective` above; injectivity is in fact unnecessary since
both commutativity and exponent `p` pass to images). -/
lemma pgl_descent_isElementaryAbelian_map {G₁ G₂ : Type*} [Group G₁] [Group G₂] {p : ℕ}
    [Fact (Nat.Prime p)] {Q : Subgroup G₁} (hQ : IsElementaryAbelian p Q) (f : G₁ →* G₂) :
    IsElementaryAbelian p (Q.map f) := by
  obtain ⟨hcomm, horder⟩ := hQ
  constructor
  · refine ⟨⟨?_⟩⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    have hxy : x * y = y * x := Subtype.ext_iff.mp (hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    exact Subtype.ext (by
      show f x * f y = f y * f x
      rw [← _root_.map_mul, ← _root_.map_mul, hxy])
  · rintro ⟨h, hh⟩ hne
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hh
    refine orderOf_eq_prime ?_ hne
    have hxp : x ^ p = 1 := by
      by_cases hx1 : (⟨x, hx⟩ : Q) = 1
      · have hx1' : x = 1 := by simpa using Subtype.ext_iff.mp hx1
        rw [hx1', one_pow]
      · have h1 : orderOf (⟨x, hx⟩ : Q) = p := horder ⟨x, hx⟩ hx1
        have h2 : (⟨x, hx⟩ : Q) ^ p = 1 := by rw [← h1]; exact pow_orderOf_eq_one _
        simpa using Subtype.ext_iff.mp h2
    exact Subtype.ext (by
      show (f x) ^ p = 1
      rw [← _root_.map_pow, hxp, _root_.map_one])

/-- Descent of Dickson's Class II item (vi) (tex 2227-2254) along a surjection: if `G₁` has an
elementary abelian normal subgroup `Q` with cyclic complement `K` of order coprime to `p`, so
does any surjective image of `G₁` (image of `Q` + Schur-Zassenhaus complement). This is the
README item 1 ("conjugate to a subgroup of the upper triangular matrices") step of the `PGL₂`
descent, rendered abstractly exactly as in `dicksons_classification_theorem_class_II`. -/
lemma pgl_descent_elementaryAbelian_of_surjective {p : ℕ} [Fact (Nat.Prime p)]
    {G₁ H : Type*} [Group G₁] [Group H] [Finite G₁] (ψ : G₁ →* H)
    (hψ : Function.Surjective ψ) (Q : Subgroup G₁) (hQ : IsElementaryAbelian p Q)
    (hQn : Q.Normal) (K : Subgroup G₁) (hQK : IsComplement' Q K) (hK : IsCyclic K)
    (hKcop : Nat.Coprime p (Nat.card K)) :
    ∃ Q' : Subgroup H, IsElementaryAbelian p Q' ∧ Q'.Normal ∧
      ∃ K' : Subgroup H, IsComplement' Q' K' ∧ IsCyclic K' ∧
        Nat.Coprime p (Nat.card K') := by
  haveI : Finite H := Finite.of_surjective ψ hψ
  have hQ'e : IsElementaryAbelian p (Q.map ψ) := pgl_descent_isElementaryAbelian_map hQ ψ
  have hQ'n : (Q.map ψ).Normal := Subgroup.Normal.map hQn ψ hψ
  haveI := hQ'n
  set χ : K →* H ⧸ (Q.map ψ) := (QuotientGroup.mk' (Q.map ψ)).comp (ψ.comp K.subtype)
    with hχdef
  have hχ_surj : Function.Surjective χ := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (Q.map ψ) x
    obtain ⟨w, hw⟩ := hψ g
    obtain ⟨⟨q0, k0⟩, hqk⟩ := ((Subgroup.isComplement'_def.mp hQK).existsUnique w).exists
    refine ⟨⟨k0.1, k0.2⟩, ?_⟩
    have h1 : (QuotientGroup.mk' (Q.map ψ)) (ψ q0.1) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_map_of_mem ψ q0.2)
    have h2 : χ ⟨k0.1, k0.2⟩ = (QuotientGroup.mk' (Q.map ψ)) (ψ k0.1) := rfl
    rw [h2, ← hw, ← hqk, _root_.map_mul ψ, _root_.map_mul (QuotientGroup.mk' (Q.map ψ)), h1,
      one_mul]
  have hidx_dvd : (Q.map ψ).index ∣ Nat.card K := by
    have h3 : (Q.map ψ).index = Nat.card (H ⧸ Q.map ψ) := rfl
    rw [h3]
    exact Subgroup.card_dvd_of_surjective χ hχ_surj
  have hcop_idx : Nat.Coprime p (Q.map ψ).index := hKcop.coprime_dvd_right hidx_dvd
  have hcop' : Nat.Coprime (Nat.card (Q.map ψ)) (Q.map ψ).index := by
    rcases eq_or_ne (Q.map ψ) ⊥ with hbot | hne
    · rw [hbot, Subgroup.card_bot]
      exact Nat.coprime_one_left _
    · obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp
        (IsElementaryAbelian.IsPGroup p Fact.out (Q.map ψ) hQ'e (bot_lt_iff_ne_bot.mpr hne))
      rw [hn]
      exact Nat.Coprime.pow_left n hcop_idx
  obtain ⟨K', hK'compl⟩ := Subgroup.exists_right_complement'_of_coprime hcop'
  haveI := hK
  haveI hquot_cyc : IsCyclic (H ⧸ Q.map ψ) := isCyclic_of_surjective χ hχ_surj
  let e' : (H ⧸ Q.map ψ) ≃* K' := hK'compl.symm.QuotientMulEquiv
  have hK'cyc : IsCyclic K' := isCyclic_of_surjective e'.toMonoidHom e'.surjective
  have hK'cop : Nat.Coprime p (Nat.card K') := by
    have hcards : Nat.card K' = Nat.card (H ⧸ Q.map ψ) := (Nat.card_congr e'.toEquiv).symm
    rw [hcards]
    exact hKcop.coprime_dvd_right (Subgroup.card_dvd_of_surjective χ hχ_surj)
  exact ⟨Q.map ψ, hQ'e, hQ'n, K', hK'compl, hK'cyc, hK'cop⟩

lemma pgl_descent_ker_map_normal {G₁ H T : Type*} [Group G₁] [Group H] [Group T]
    (ψ : G₁ →* H) (e2 : G₁ ≃* T) : (ψ.ker.map e2.toMonoidHom).Normal :=
  Subgroup.Normal.map inferInstance e2.toMonoidHom (MulEquiv.surjective e2)

lemma pgl_descent_ker_map_card {G₁ H T : Type*} [Group G₁] [Group H] [Group T]
    (ψ : G₁ →* H) (e2 : G₁ ≃* T) :
    Nat.card (ψ.ker.map e2.toMonoidHom) = Nat.card ψ.ker :=
  (Nat.card_congr (Subgroup.equivMapOfInjective ψ.ker e2.toMonoidHom
    (MulEquiv.injective e2)).toEquiv).symm

/-- Transfer a quotient description along an isomorphism: if `ψ : G₁ →* H` is surjective and
`e2 : G₁ ≃* T`, then `H ≅ T ⧸ e2(ker ψ)`. -/
lemma pgl_descent_quotient_transfer {G₁ H T : Type*} [Group G₁] [Group H] [Group T]
    (ψ : G₁ →* H) (hψ : Function.Surjective ψ) (e2 : G₁ ≃* T)
    [hn : (ψ.ker.map e2.toMonoidHom).Normal] :
    Nonempty (H ≃* T ⧸ ψ.ker.map e2.toMonoidHom) :=
  ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψ).symm.trans
    (QuotientGroup.congr ψ.ker (ψ.ker.map e2.toMonoidHom) e2 rfl)⟩

/-- `(2 : ZMod 3) ≠ 0` (as a named lemma so `decide` runs with a concrete, non-metavariable
proposition; used to supply the `NeZero (2 : ZMod 3)` instance below). -/
lemma pgl_descent_two_ne_ZMod3 : (2 : ZMod 3) ≠ 0 := by decide

/-- `|SL(2,3)| = 24`. Proven by `decide`, but forcing the *computable* `Subtype.fintype`
instance for `SL(2, ZMod 3)`: in this file's import environment the ambient `Fintype` instance
does not kernel-reduce, so a bare `decide` on `Fintype.card SL(2, ZMod 3)` gets stuck. -/
lemma pgl_descent_card_SL2_ZMod3 : Nat.card SL(2, ZMod 3) = 24 := by
  letI : Fintype SL(2, ZMod 3) := Subtype.fintype _
  rw [Nat.card_eq_fintype_card]; decide

/-- `PSL(2,3) ≅ A₄` (classical; feeds Class I item (iii), tex ~2246 "Case IIb: This leads to
Class I (iii)", through the descent -- README item 3 lists `A₄` among the exceptional images).

Proof: `SL(2,3)` acts on the four points of `ℙ¹(𝔽₃) = Projectivization (ZMod 3) (Fin 2 → ZMod 3)`
(mathlib `Projectivization.PSLAction.toPermHom`); the induced map on `PSL(2,3) = SL(2,3)/{±1}` is
injective (`Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective`), so transporting the
`4`-element projective line to `Fin 4` gives an embedding `g : PSL(2,3) ↪ S₄`. Its image has
order `|PSL(2,3)| = |SL(2,3)|/|Z| = 24/2 = 12`, hence index `2` in `S₄`. Every `3`-cycle has odd
order, so lands in any index-`2` subgroup; since the `3`-cycles generate `A₄`
(`closure_three_cycles_eq_alternating`), `A₄ ≤ g.range`, and equal cardinality (`12`) forces
`g.range = A₄`. Thus `PSL(2,3) ≃* g.range = A₄`. -/
lemma pgl_descent_PSL2_ZMod3_iso_alternating :
    Nonempty (PSL (Fin 2) (ZMod 3) ≃* alternatingGroup (Fin 4)) := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  haveI : NeZero (2 : ZMod 3) := ⟨pgl_descent_two_ne_ZMod3⟩
  -- The projective line `ℙ¹(𝔽₃)` has 4 points.
  haveI : Fintype (Projectivization (ZMod 3) (Fin 2 → ZMod 3)) := Fintype.ofFinite _
  have hcardP : Nat.card (Projectivization (ZMod 3) (Fin 2 → ZMod 3)) = 4 := by
    have h2 : Module.finrank (ZMod 3) (Fin 2 → ZMod 3) = 2 := Module.finrank_fin_fun (ZMod 3)
    have hk : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
    rw [Projectivization.card_of_finrank_two (ZMod 3) (Fin 2 → ZMod 3) h2, hk]
  have hcardP' : Fintype.card (Projectivization (ZMod 3) (Fin 2 → ZMod 3)) = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact hcardP
  let eP : Projectivization (ZMod 3) (Fin 2 → ZMod 3) ≃ Fin 4 := Fintype.equivFinOfCardEq hcardP'
  -- The faithful action of PSL(2,3) on ℙ¹.
  let f : PSL (Fin 2) (ZMod 3) →* Equiv.Perm (Projectivization (ZMod 3) (Fin 2 → ZMod 3)) :=
    Projectivization.PSLAction.toPermHom
  have hf_inj : Function.Injective f :=
    Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective (K := ZMod 3) (ι := Fin 2)
  -- Transport to permutations of `Fin 4`.
  let g : PSL (Fin 2) (ZMod 3) →* Equiv.Perm (Fin 4) := (eP.permCongrHom.toMonoidHom).comp f
  have hg_inj : Function.Injective g := fun a b hab =>
    hf_inj (eP.permCongrHom.injective hab)
  -- Cardinalities.
  have hcardPSL : Nat.card (PSL (Fin 2) (ZMod 3)) = 12 := by
    have hZ : Nat.card (center SL(2, ZMod 3)) = 2 := by
      rw [SpecialSubgroups.center_SL2_eq_Z, SpecialSubgroups.card_Z_eq_two_of_two_ne_zero]
    have hidx : Nat.card (center SL(2, ZMod 3)) * (center SL(2, ZMod 3)).index
        = Nat.card SL(2, ZMod 3) := Subgroup.card_mul_index _
    have hPSLidx : Nat.card (PSL (Fin 2) (ZMod 3)) = (center SL(2, ZMod 3)).index := rfl
    rw [hZ, pgl_descent_card_SL2_ZMod3] at hidx
    rw [hPSLidx]; omega
  have hperm : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  have hcardA : Nat.card (alternatingGroup (Fin 4)) = 12 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 4)
    rw [hperm] at h; omega
  have hcardR : Nat.card (g.range) = 12 :=
    (Nat.card_congr (MonoidHom.ofInjective hg_inj).toEquiv).symm.trans hcardPSL
  -- `g.range` has index 2, hence is normal.
  have hRidx : g.range.index = 2 := by
    have h := Subgroup.index_mul_card (g.range)
    rw [hcardR, hperm] at h; omega
  haveI hRnormal : (g.range).Normal := Subgroup.normal_of_index_eq_two hRidx
  -- Every 3-cycle lies in `g.range`.
  have h3cyc : ∀ c : Equiv.Perm (Fin 4), c.IsThreeCycle → c ∈ g.range := by
    intro c hc
    have hord : orderOf c = 3 := hc.orderOf
    have h1 : orderOf (QuotientGroup.mk' (g.range) c) ∣ 3 := by
      have := orderOf_map_dvd (QuotientGroup.mk' (g.range)) c
      rwa [hord] at this
    have hQcard : Nat.card (Equiv.Perm (Fin 4) ⧸ g.range) = 2 := hRidx
    have h2 : orderOf (QuotientGroup.mk' (g.range) c) ∣ 2 := by
      have := _root_.orderOf_dvd_natCard (QuotientGroup.mk' (g.range) c)
      rwa [hQcard] at this
    have hg1 : orderOf (QuotientGroup.mk' (g.range) c) ∣ Nat.gcd 3 2 := Nat.dvd_gcd h1 h2
    have hgcd : Nat.gcd 3 2 = 1 := by decide
    rw [hgcd] at hg1
    have h3 : orderOf (QuotientGroup.mk' (g.range) c) = 1 := Nat.dvd_one.mp hg1
    have hqc : QuotientGroup.mk' (g.range) c = 1 := orderOf_eq_one_iff.mp h3
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hqc
    exact hqc
  -- `A₄ ≤ g.range`, hence equal by cardinality.
  have hAle : alternatingGroup (Fin 4) ≤ g.range := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
    intro c hc
    exact h3cyc c hc
  have hle : Nat.card (g.range) ≤ Nat.card (alternatingGroup (Fin 4)) :=
    le_of_eq (hcardR.trans hcardA.symm)
  have hRA : g.range = alternatingGroup (Fin 4) :=
    (Subgroup.eq_of_le_of_card_ge hAle hle).symm
  exact ⟨(MonoidHom.ofInjective hg_inj).trans (MulEquiv.subgroupCongr hRA)⟩

/-- `(2 : ZMod 5) ≠ 0` (as a named lemma so `decide` runs with a concrete, non-metavariable
proposition; used to supply the `NeZero (2 : ZMod 5)` instance below). -/
lemma pgl_descent_two_ne_ZMod5 : (2 : ZMod 5) ≠ 0 := by decide

set_option maxRecDepth 40000 in
/-- `|SL(2,5)| = 120`. Proven by `decide`, but forcing the *computable* `Subtype.fintype`
instance for `SL(2, ZMod 5)` (as in `pgl_descent_card_SL2_ZMod3`), and raising `maxRecDepth`
for the kernel reduction of the `120`-element enumeration. -/
lemma pgl_descent_card_SL2_ZMod5 : Nat.card SL(2, ZMod 5) = 120 := by
  letI : Fintype SL(2, ZMod 5) := Subtype.fintype _
  rw [Nat.card_eq_fintype_card]; decide

/-- `PSL(2,5) ≅ A₅` (feeds Class I item (iv) / Class II item (viii), tex ~2088-2113: Butler's
Case Vd identifies `G/Z` as a simple group of order `60`, and every simple group of order `60`
is `≅ A₅`).

Proof (Waves 19-20): `|SL(2,5)| = 120` (`pgl_descent_card_SL2_ZMod5`), hence `|PSL(2,5)| = 60`
(`center_SL2_eq_Z`, `card_Z_eq_two_of_two_ne_zero`, `card_mul_index`); `ℙ¹(𝔽₅)` has `6` points
(`Projectivization.card_of_finrank_two`), giving an injective
`g : PSL(2,5) →* Equiv.Perm (Fin 6)` (`PSLAction.toPermHom`, `toPermHom_injective`,
`Equiv.permCongrHom`). Unlike the `A₄` sibling the image has order `60`, index `12` in `S₆`, so
the index-2 trick does not finish: instead `g.range ≤ alternatingGroup (Fin 6)` by the sign
trick (`pgl_descent_PSL2_ZMod5_range_le_alternatingGroup`, via perfectness of `PSL(2,5)`), the
corestriction of `g` to `A₆` has range of order `60` and hence index `360 / 60 = 6`, and every
index-`6` subgroup of `A₆` is `≅ A₅` (`Ch7SimpleGroup60.isoAlternatingGroupFive_of_index_six`,
via the coset action and simplicity of `A₆`). -/
lemma pgl_descent_PSL2_ZMod5_iso_alternating :
    Nonempty (PSL (Fin 2) (ZMod 5) ≃* alternatingGroup (Fin 5)) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  haveI : NeZero (2 : ZMod 5) := ⟨pgl_descent_two_ne_ZMod5⟩
  -- The projective line `ℙ¹(𝔽₅)` has 6 points.
  haveI : Fintype (Projectivization (ZMod 5) (Fin 2 → ZMod 5)) := Fintype.ofFinite _
  have hcardP : Nat.card (Projectivization (ZMod 5) (Fin 2 → ZMod 5)) = 6 := by
    have h2 : Module.finrank (ZMod 5) (Fin 2 → ZMod 5) = 2 := Module.finrank_fin_fun (ZMod 5)
    have hk : Nat.card (ZMod 5) = 5 := by rw [Nat.card_eq_fintype_card, ZMod.card]
    rw [Projectivization.card_of_finrank_two (ZMod 5) (Fin 2 → ZMod 5) h2, hk]
  have hcardP' : Fintype.card (Projectivization (ZMod 5) (Fin 2 → ZMod 5)) = 6 := by
    rw [← Nat.card_eq_fintype_card]; exact hcardP
  let eP : Projectivization (ZMod 5) (Fin 2 → ZMod 5) ≃ Fin 6 := Fintype.equivFinOfCardEq hcardP'
  -- The faithful action of PSL(2,5) on ℙ¹, transported to `Fin 6`.
  let f : PSL (Fin 2) (ZMod 5) →* Equiv.Perm (Projectivization (ZMod 5) (Fin 2 → ZMod 5)) :=
    Projectivization.PSLAction.toPermHom
  have hf_inj : Function.Injective f :=
    Matrix.ProjectiveSpecialLinearGroup.toPermHom_injective (K := ZMod 5) (ι := Fin 2)
  let g : PSL (Fin 2) (ZMod 5) →* Equiv.Perm (Fin 6) := (eP.permCongrHom.toMonoidHom).comp f
  have hg_inj : Function.Injective g := fun a b hab =>
    hf_inj (eP.permCongrHom.injective hab)
  -- `|PSL(2,5)| = 60`.
  have hcardPSL : Nat.card (PSL (Fin 2) (ZMod 5)) = 60 := by
    have hZ : Nat.card (center SL(2, ZMod 5)) = 2 := by
      rw [SpecialSubgroups.center_SL2_eq_Z, SpecialSubgroups.card_Z_eq_two_of_two_ne_zero]
    have hidx : Nat.card (center SL(2, ZMod 5)) * (center SL(2, ZMod 5)).index
        = Nat.card SL(2, ZMod 5) := Subgroup.card_mul_index _
    have hPSLidx : Nat.card (PSL (Fin 2) (ZMod 5)) = (center SL(2, ZMod 5)).index := rfl
    rw [hZ, pgl_descent_card_SL2_ZMod5] at hidx
    rw [hPSLidx]; omega
  -- `g.range ≤ A₆` (sign trick via perfectness), so corestrict `g` to `A₆`.
  have hmem : ∀ a, g a ∈ alternatingGroup (Fin 6) := fun a =>
    pgl_descent_PSL2_ZMod5_range_le_alternatingGroup g (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  let g' : PSL (Fin 2) (ZMod 5) →* alternatingGroup (Fin 6) :=
    g.codRestrict (alternatingGroup (Fin 6)) hmem
  have hg'inj : Function.Injective g' :=
    (MonoidHom.injective_codRestrict g (alternatingGroup (Fin 6)) hmem).mpr hg_inj
  -- `g'.range` has order `60`, hence index `6` in `A₆` (order `360`).
  have hcardH : Nat.card ↥(g'.range) = 60 :=
    (Nat.card_congr (MonoidHom.ofInjective hg'inj).toEquiv).symm.trans hcardPSL
  have hperm : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]; rfl
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
    rw [hperm] at h; omega
  have hHindex : g'.range.index = 6 := by
    have h := Subgroup.card_mul_index g'.range
    rw [hcardH, hcardA] at h; omega
  -- Any index-`6` subgroup of `A₆` is `≅ A₅`.
  exact ⟨(MonoidHom.ofInjective hg'inj).trans
    (Ch7SimpleGroup60.isoAlternatingGroupFive_of_index_six g'.range hHindex)⟩

/-- `SL(2,3)` modulo any order-`2` subgroup is `A₄` (the subgroup is forced to be the center
`{±1}` by `pgl_descent_card_two_eq_center_SL2`; the residual gap is exactly
`pgl_descent_PSL2_ZMod3_iso_alternating`). -/
lemma pgl_descent_SL2_ZMod3_quotient (W : Subgroup SL(2, ZMod 3)) [W.Normal]
    (hW : Nat.card W = 2) :
    Nonempty ((SL(2, ZMod 3) ⧸ W) ≃* alternatingGroup (Fin 4)) := by
  haveI : NeZero (2 : ZMod 3) := ⟨by decide⟩
  obtain ⟨e⟩ := pgl_descent_PSL2_ZMod3_iso_alternating
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (pgl_descent_card_two_eq_center_SL2 W hW)).trans e⟩

/-- `SL(2,5)` modulo any order-`2` subgroup is `A₅` (the subgroup is forced to be the center
`{±1}` by `pgl_descent_card_two_eq_center_SL2`, then apply
`pgl_descent_PSL2_ZMod5_iso_alternating`). -/
lemma pgl_descent_SL2_ZMod5_quotient (W : Subgroup SL(2, ZMod 5)) [W.Normal]
    (hW : Nat.card W = 2) :
    Nonempty ((SL(2, ZMod 5) ⧸ W) ≃* alternatingGroup (Fin 5)) := by
  haveI : NeZero (2 : ZMod 5) := ⟨by decide⟩
  obtain ⟨e⟩ := pgl_descent_PSL2_ZMod5_iso_alternating
  exact ⟨(QuotientGroup.quotientMulEquivOfEq
    (pgl_descent_card_two_eq_center_SL2 W hW)).trans e⟩

/-- The binary octahedral group `2O = Ŝ₄` modulo its order-`2` (necessarily central, by
uniqueness of the involution) subgroup is `S₄` (feeds Class I item (v) through the descent;
tex ~2173-2201, Butler's Case VIb, proves the `SL₂`-side counterpart `G/Z ≅ S₄`). Missing
infrastructure: `Ch7GroupRecognition.mulEquiv_of_card48_uniqueInvolution_quotientS4` goes the
*other* way (a card-48 group with unique involution and quotient `S₄` is `≅ 2O`); the forward
facts (`|2O| = 48`, unique involution, `2O ⧸ ⟨z⟩ ≃* S₄`) about the `PresentedGroup` are not
yet formalized. Sorried pending those. -/
lemma pgl_descent_binaryOctahedral_quotient (W : Subgroup BinaryOctahedralGroup) [W.Normal]
    (hW : Nat.card W = 2) :
    Nonempty ((BinaryOctahedralGroup ⧸ W) ≃* Equiv.Perm (Fin 4)) := by
  sorry

/-- The center of `GL(2, 𝔽_q)` is the scalar torus, of order `q-1`
(`GeneralLinearGroup.center_eq_range_scalar` + `Matrix.scalar` injective + `Fintype.card_units`).
A `pgl_descent_` cardinality helper (Wave 20), reusable for `|PGL(2,q)|`. -/
lemma pgl_descent_card_center_GL_two {F : Type*} [Field F] [Fintype F] :
    Nat.card (center (GL (Fin 2) F)) = Fintype.card F - 1 := by
  classical
  have hinj : Function.Injective (GeneralLinearGroup.scalar (Fin 2) (R := F)) := by
    intro a b hab
    have hab' : Matrix.scalar (Fin 2) (a : F) = Matrix.scalar (Fin 2) (b : F) :=
      congrArg Units.val hab
    exact Units.ext (Matrix.scalar_inj.mp hab')
  have h2 : Nat.card (Fˣ) = Fintype.card F - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
  rw [GeneralLinearGroup.center_eq_range_scalar]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).symm.toEquiv).trans h2

/-- `|PGL(2,𝔽_q)| · (q-1) = |GL(2,𝔽_q)|`, since `PGL(2,q) = GL(2,q)/Z` and `|Z| = q-1`
(`pgl_descent_card_center_GL_two`, `Subgroup.index_mul_card`). Hence
`|PGL(2,q)| = q(q²-1) = |SL(2,q)|`, matching the right-hand order of the target below. A
`pgl_descent_` cardinality helper (Wave 20). -/
lemma pgl_descent_card_PGL_two_mul {F : Type*} [Field F] [Fintype F] :
    Nat.card (PGL (Fin 2) F) * (Fintype.card F - 1) = Nat.card (GL (Fin 2) F) := by
  have hc : Nat.card (center (GL (Fin 2) F)) = Fintype.card F - 1 :=
    pgl_descent_card_center_GL_two
  have hidx : Nat.card (PGL (Fin 2) F) = (center (GL (Fin 2) F)).index := rfl
  rw [hidx, ← hc]
  exact Subgroup.index_mul_card _

/-- `⟨SL(2,𝔽_q), d_π⟩ ⧸ {±1} ≅ PGL(2,𝔽_q)` (feeds Class II item (x), tex 2213-2254; README
item 2: `H` conjugate to `PGL₂(𝔽_{ℓ^r})`), where `q = p^k`, `SL2_join_d` embeds `SL(2,q)` into
`SL(2,q²)` and adjoins `d_π = diag(π, π⁻¹)`.

STATEMENT REPAIRED (Wave 20 integration): the original form quantified `π` universally and was
false; it now requires `hπ : SL2_join_d_pi_spec p k π` (`π ∉ 𝔽_q`, `π² ∈ 𝔽_q`), threaded from
`caseV_b` through `caseV_core`/`case_V`/`class_II` item (x) to the dispatch here. Original
falseness analysis, kept for the record: Butler's Vb constructs a *specific* `π`: a generator
of the order
`2(q-1)` cyclic torus with `π² ∈ 𝔽_q` a nonsquare, so `d_π² = diag(π²,π⁻²) ∈ SL(2,q)` and
`⟨SL(2,q), d_π⟩ = SL(2,q) ⊔ SL(2,q)·d_π` has order `2·|SL(2,q)|`, its quotient by `{±1}` order
`q(q²-1) = |PGL(2,q)|`. But this leaf quantifies `π : 𝔽_{q²}ˣ` *universally* with no `π² ∈ 𝔽_q`
constraint; the caller (`dicksons_classification_theorem_class_II`, item (x)) only ever feeds
Butler's `π`. Counterexample to the statement as written: `p = 3`, `k = 1` (`q = 3`), `π` a
generator of `𝔽_9ˣ` (order 8, `π² ∉ 𝔽_3`). Then `d_π` does not normalize `SL(2,3)` (diagonal
conjugation scales the off-diagonal by `π²∉𝔽_3`): `d_π·!![1,1;0,1]·d_π⁻¹ = !![1,π²;0,1]` lies in a
third `SL(2,3)`-coset, so `[⟨SL(2,3),d_π⟩ : SL(2,3)] ≥ 3`, `|⟨SL(2,3),d_π⟩| ≥ 72`; with `W = {±1}`
(normal, order 2 — hypotheses satisfied) the quotient has order `≥ 36 ≠ 24 = |PGL(2,3)|`, so no
isomorphism exists. Provable only after narrowing the statement with `π² ∈ 𝔽_q` nonsquare — which
the wave protocol forbids (statement must not change).

INFRASTRUCTURE (corrects the prior "no `PGL(2,𝔽_q)` machinery exists in repo or mathlib"
assessment): mathlib v4.32 now has `Matrix.ProjGenLinGroup` (`PGL(n,R) := GL n R ⧸ center (GL n R)`,
defeq to this repo's Ch4 `PGL`) with `ProjGenLinGroup.map (f : R →+* S) : PGL(n,R) →* PGL(n,S)`
(field-extension functoriality), `SpecialLinearGroup.toPGL`, `ProjectiveSpecialLinearGroup.toPGL` +
`toPGL_injective`, and `toPGL_surj_iff [Nonempty n] : Surjective toPGL ↔ ∀ r:Rˣ, ∃ k, k^(card n)=r`.
For `n = 2` over a finite field of odd order the RHS fails on nonsquares, so `PSL(2,q) ↪ PGL(2,q)`
has cokernel `𝔽_qˣ/(𝔽_qˣ)²` of order 2 (`FiniteField.unit_isSquare_iff`, `hp2`) — the index-2 fact.

TRUE ROUTE (narrowed statement, `π²∈𝔽_q` nonsquare): `⟨SL(2,q),d_π⟩ = SL(2,q) ⊔ SL(2,q)·d_π` maps
to `PGL(2,q)` by `s ↦ [s]`, `s·d_π ↦ [s·diag(1,π⁻²)]` (each element is an `𝔽_{q²}ˣ`-scalar multiple
of a `GL(2,q)` matrix; the `PGL(2,q)`-class kills the scalar). Surjective (image ⊇ `PSL(2,q) =
SL(2,q).toPGL.range` and the extra generator `[diag(1,π⁻²)] ∉ PSL` by the index-2 fact), kernel
`{±1}`; finish with `quotientKerEquivOfSurjective`. Remaining true gaps (the statement
narrowing itself is now done):
(1) building this coset-wise hom out of a subgroup of `SL(2,q²)` into `PGL(2,q)` by hand — no
mathlib `map` covers the field-*descent* `q²→q`;
(2) `[diag(1,π⁻²)] ∉ PSL(2,q)` / index-2: assemblable from `toPGL_surj_iff` + `unit_isSquare_iff`
but not packaged as a `PGL/PSL ≅ 𝔽_qˣ/sq` cokernel lemma;
(3) `W = {±1}` forced (normal order-2 ⟹ central; `-1` the unique involution of `SL(2,q²)`,
`char ≠ 2`) — as in the sibling `pgl_descent_card_two_eq_center_SL2`.

LANDED (Wave 20; `#print axioms`-clean): `pgl_descent_card_center_GL_two` (`|Z(GL(2,q))| = q-1`) and
`pgl_descent_card_PGL_two_mul` (`|PGL(2,q)|·(q-1) = |GL(2,q)|`, giving `|PGL(2,q)| = |SL(2,q)|` — the
target's right-hand order). Sorried pending gaps (1)/(2). -/
lemma pgl_descent_SL2_join_d_quotient {p : ℕ} [Fact (Nat.Prime p)] (hp2 : p ≠ 2) (k : ℕ+)
    (π : (GaloisField p (2 * k.val))ˣ) (hπ : SL2_join_d_pi_spec p k π)
    (W : Subgroup (SL2_join_d p k π)) [W.Normal]
    (hW : Nat.card W = 2) :
    Nonempty ((↥(SL2_join_d p k π) ⧸ W) ≃* PGL (Fin 2) (GaloisField p k.val)) := by
  sorry

/-- Pull a finite subgroup of `PGL(2, F̄_p)` back to a finite subgroup of `SL(2, F̄_p)`
containing the center, together with the induced surjection with kernel of order `2`
(`SL(2,F̄_p) → PGL(2,F̄_p)` is onto with kernel `center = {±1}` over the algebraically closed
`F̄_p`, `Ch4_PGLIsoPSLOverAlgClosedField`). -/
lemma pgl_descent_setup (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (G : Subgroup (PGL (Fin 2) (AlgebraicClosure (ZMod p)))) [Finite G] :
    ∃ (Ghat : Subgroup SL(2, AlgebraicClosure (ZMod p))) (ψ : Ghat →* G),
      Finite Ghat ∧ center SL(2, AlgebraicClosure (ZMod p)) ≤ Ghat ∧
        Function.Surjective ψ ∧ Nat.card ψ.ker = 2 := by
  haveI : NeZero (2 : AlgebraicClosure (ZMod p)) :=
    pgl_descent_neZero_two _ p hp2
  set φ : SL(2, AlgebraicClosure (ZMod p)) →* PGL (Fin 2) (AlgebraicClosure (ZMod p)) :=
    SL_monoidHom_PGL (Fin 2) (AlgebraicClosure (ZMod p)) with hφdef
  have hφ_surj : Function.Surjective φ := by
    intro x
    obtain ⟨y, hy⟩ := Surjective_PSL_monoidHom_PGL (Fin 2) (AlgebraicClosure (ZMod p)) x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact ⟨s, hy⟩
  have hφ_ker : φ.ker = center SL(2, AlgebraicClosure (ZMod p)) :=
    ker_SL_monoidHom_PGL_eq_center (AlgebraicClosure (ZMod p)) (Fin 2)
      (AlgebraicClosure (ZMod p))
  have hker_le : φ.ker ≤ G.comap φ := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact G.one_mem
  have hZ_le : center SL(2, AlgebraicClosure (ZMod p)) ≤ G.comap φ := hφ_ker ▸ hker_le
  set ψ : (G.comap φ) →* G := φ.subgroupComap G with hψdef
  have hψ_surj : Function.Surjective ψ := φ.subgroupComap_surjective_of_surjective G hφ_surj
  have hψ_ker : ψ.ker = φ.ker.subgroupOf (G.comap φ) := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subtype.ext_iff, hψdef,
      MonoidHom.subgroupComap_apply_coe, OneMemClass.coe_one]
  have hψ_ker_card : Nat.card ψ.ker = 2 := by
    rw [hψ_ker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker_le).toEquiv, hφ_ker,
      SpecialSubgroups.center_SL2_eq_Z, SpecialSubgroups.card_Z_eq_two_of_two_ne_zero]
  haveI : Finite ψ.ker := Nat.finite_of_card_ne_zero (by rw [hψ_ker_card]; norm_num)
  haveI : Finite ((G.comap φ) ⧸ ψ.ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivOfSurjective ψ hψ_surj).toEquiv.symm
  have hfin : Finite (G.comap φ) :=
    Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := ψ.ker)).symm
  exact ⟨G.comap φ, ψ, hfin, hZ_le, hψ_surj, hψ_ker_card⟩



/-- The PGL₂ classification (README, "If `H` is a finite subgroup of `PGL_2(F̄_p)` ..."; this is
Dickson's theorem for `PGL(2,F)`, obtained from `dicksons_classification_theorem_class_I/II` for
`SL(2,F)` by passing to the quotient by the center `{±1}`). Every finite subgroup of
`PGL(Fin 2, 𝔽_p-bar)` (`p` an odd prime) is cyclic, dihedral, elementary-abelian-by-cyclic (the
isomorphism type of a subgroup of the upper triangular matrices, README item 1), `A₄`, `S₄`,
`A₅`, or `PSL(2,𝕂)`/`PGL(2,𝕂)` for *some* finite field `𝕂` of characteristic `p`.

RESTATED (Wave 17), in addition to the two earlier fixes recorded below:
(a) the original statement universally quantified a finite field
`(𝕂 : Type*) [Field 𝕂] [CharP 𝕂 p] [Finite 𝕂]` and asserted
`... ∨ Isomorphic G (PSL (Fin 2) 𝕂) ∨ Isomorphic G (PGL (Fin 2) 𝕂)` for that *fixed* `𝕂` --
false as stated: for `𝕂 = 𝔽_p` and `G` the image in `PGL₂(F̄_p)` of `SL(2,𝔽_{p²})` (i.e.
`G ≅ PSL(2,p²)`, nonabelian simple of order `p²(p⁴-1)/2`) no disjunct holds. Dickson produces
*some* finite field of characteristic `p` (README item 2: "for some `r ∈ Z_{>0}`"), so the
fixed `𝕂` is replaced by `∃ k : ℕ+, ... (GaloisField p k.val)`, matching how
`dicksons_classification_theorem_class_II` items (ix)/(x) render their fields;
(b) the original statement omitted README item 1 ("`H` is conjugate to a subgroup of the upper
triangular matrices") entirely -- also making it false: the unipotent subgroup `(ℤ/p)²` (image
of the shear subgroup over `𝔽_{p²}`) is a finite subgroup of `PGL₂(F̄_p)` that is not cyclic,
dihedral, `A₄`, `S₄`, `A₅`, nor any `PSL₂`/`PGL₂`. It is restored here in the same abstract,
conjugation-free form used for item (vi) of `dicksons_classification_theorem_class_II`: an
elementary abelian normal `p`-subgroup with cyclic complement of order coprime to `p`;
(c) narrowing hypothesis `hp2 : p ≠ 2` added (replacing the dropped `𝕂` binders): the README
assumes "`ℓ` is an odd prime", and both `dicksons_classification_theorem_class_I/II` carry the
same hypothesis (their `p = 2` gap traces to `case_IV`, `DIVERGENCES.md` item 1).
Earlier fixes kept from the previous revision: (d) each disjunct after the first was wrapped
under a single `∃ n, _ ∨ _ ∨ ⋯` -- logically harmless but misleadingly scoped -- and (e)
`Equiv.Perm (Fin 5)` (`S₅`, order `120`) stood in place of `Equiv.Perm (Fin 4)` (`S₄`): `S₅` is
not one of Dickson's exceptional subgroups of `PGL₂` (see README).

Status: descent fully implemented. The pullback along `SL(2,F̄_p) → PGL(2,F̄_p)`
(`pgl_descent_setup`) feeds `dicksons_classification_theorem_class_I/II`, and each disjunct is
pushed down through the order-`2` quotient: cyclic → cyclic, dicyclic → dihedral
(`pgl_descent_quaternion_quotient`, fully proven), item (vi) → item (vi)
(`pgl_descent_elementaryAbelian_of_surjective`, fully proven), `SL(2,𝔽_q)` → `PSL(2,𝔽_q)`
(`pgl_descent_card_two_eq_center_SL2`, fully proven), `PSL(2,3) ≅ A₄` and `PSL(2,5) ≅ A₅`
(fully proven, Waves 18/20). Remaining gaps are exactly the two documented recognition
`sorry`s above (`2O/{±1} ≅ S₄`, `⟨SL(2,𝔽_q),d_π⟩/{±1} ≅ PGL(2,𝔽_q)`) plus whatever
`dicksons_classification_theorem_class_I/II` themselves still carry internally. -/
-- ANCHOR: FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod
theorem FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod {p : ℕ}
    [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (G : Subgroup (PGL (Fin 2) (AlgebraicClosure (ZMod p)))) [hG : Finite G] :
    IsCyclic G ∨
      (∃ n, Isomorphic G (DihedralGroup n)) ∨
      (∃ Q : Subgroup G, IsElementaryAbelian p Q ∧ Q.Normal ∧
        ∃ K : Subgroup G, IsComplement' Q K ∧ IsCyclic K ∧ Nat.Coprime p (Nat.card K)) ∨
      Isomorphic G (alternatingGroup (Fin 4)) ∨
      Isomorphic G (Equiv.Perm (Fin 4)) ∨
      Isomorphic G (alternatingGroup (Fin 5)) ∨
      (∃ k : ℕ+, Isomorphic G (PSL (Fin 2) (GaloisField p k.val))) ∨
      (∃ k : ℕ+, Isomorphic G (PGL (Fin 2) (GaloisField p k.val))) := by
  letI : DecidableEq (AlgebraicClosure (ZMod p)) := Classical.decEq _
  obtain ⟨Ghat, ψ, hGhatFin, hZle, hψ_surj, hψ_ker_card⟩ := pgl_descent_setup p hp2 G
  haveI := hGhatFin
  by_cases hdvd : p ∣ Nat.card Ghat
  · -- Class II: `p` divides the order of the pullback.
    rcases dicksons_classification_theorem_class_II Ghat hdvd hZle hp2 with
      ⟨Q, hQe, hQn, K, hQK, hKc, hKcop⟩ | ⟨hp2', -⟩ | ⟨-, h35⟩ | ⟨k, h3q⟩ | ⟨k, π, hπs, h3j⟩
    · -- (vi) elementary-abelian-by-cyclic descends to the same structure
      exact Or.inr (Or.inr (Or.inl
        (pgl_descent_elementaryAbelian_of_surjective ψ hψ_surj Q hQe hQn K hQK hKc hKcop)))
    · -- (vii) requires `p = 2`
      exact absurd hp2' hp2
    · -- (viii) `SL(2,5)` (at `p = 3`) descends to `A₅`
      obtain ⟨e2⟩ := h35
      haveI := pgl_descent_ker_map_normal ψ e2
      obtain ⟨e3⟩ := pgl_descent_quotient_transfer ψ hψ_surj e2
      obtain ⟨e4⟩ := pgl_descent_SL2_ZMod5_quotient _
        ((pgl_descent_ker_map_card ψ e2).trans hψ_ker_card)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e3.trans e4⟩)))))
    · -- (ix) `SL(2,𝔽_q)` descends to `PSL(2,𝔽_q)`
      obtain ⟨e2⟩ := h3q
      haveI := pgl_descent_ker_map_normal ψ e2
      obtain ⟨e3⟩ := pgl_descent_quotient_transfer ψ hψ_surj e2
      haveI : NeZero (2 : GaloisField p k.val) := pgl_descent_neZero_two _ p hp2
      have hWc := pgl_descent_card_two_eq_center_SL2 _
        ((pgl_descent_ker_map_card ψ e2).trans hψ_ker_card)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k,
        ⟨e3.trans (QuotientGroup.quotientMulEquivOfEq hWc)⟩⟩))))))
    · -- (x) `⟨SL(2,𝔽_q), d_π⟩` descends to `PGL(2,𝔽_q)`
      obtain ⟨e2⟩ := h3j
      haveI := pgl_descent_ker_map_normal ψ e2
      obtain ⟨e3⟩ := pgl_descent_quotient_transfer ψ hψ_surj e2
      obtain ⟨e4⟩ := pgl_descent_SL2_join_d_quotient hp2 k π hπs _
        ((pgl_descent_ker_map_card ψ e2).trans hψ_ker_card)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨k, ⟨e3.trans e4⟩⟩))))))
  · -- Class I: the order of the pullback is coprime to `p`.
    have hp' : p = 0 ∨ Nat.Coprime (Nat.card Ghat) p :=
      Or.inr (((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mpr hdvd).symm)
    rcases dicksons_classification_theorem_class_I (Fact.out : Nat.Prime p).prime Ghat hp'
      hZle hp2 with hcyc | ⟨m, hquat⟩ | h23 | h25 | h2O
    · -- (i) cyclic descends to cyclic
      haveI := hcyc
      exact Or.inl (isCyclic_of_surjective ψ hψ_surj)
    · -- (ii) dicyclic `⟨x,y | x^n = y², yxy⁻¹ = x⁻¹⟩` descends to dihedral
      obtain ⟨e2⟩ := hquat
      haveI : NeZero m := ⟨by
        rintro rfl
        haveI : Finite (QuaternionGroup 0) := Finite.of_equiv _ e2.toEquiv
        haveI : Finite (DihedralGroup 0) := Finite.of_equiv _
          QuaternionGroup.quaternionGroupZeroEquivDihedralGroupZero.toEquiv
        exact not_finite (DihedralGroup 0)⟩
      haveI := pgl_descent_ker_map_normal ψ e2
      obtain ⟨e3⟩ := pgl_descent_quotient_transfer ψ hψ_surj e2
      obtain ⟨e4⟩ := pgl_descent_quaternion_quotient m _
        ((pgl_descent_ker_map_card ψ e2).trans hψ_ker_card)
      exact Or.inr (Or.inl ⟨m, ⟨e3.trans e4⟩⟩)
    · -- (iii) `SL(2,3)` descends to `A₄`
      obtain ⟨e2⟩ := h23
      haveI := pgl_descent_ker_map_normal ψ e2
      obtain ⟨e3⟩ := pgl_descent_quotient_transfer ψ hψ_surj e2
      obtain ⟨e4⟩ := pgl_descent_SL2_ZMod3_quotient _
        ((pgl_descent_ker_map_card ψ e2).trans hψ_ker_card)
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e3.trans e4⟩)))
    · -- (iv) `SL(2,5)` descends to `A₅`
      obtain ⟨e2⟩ := h25
      haveI := pgl_descent_ker_map_normal ψ e2
      obtain ⟨e3⟩ := pgl_descent_quotient_transfer ψ hψ_surj e2
      obtain ⟨e4⟩ := pgl_descent_SL2_ZMod5_quotient _
        ((pgl_descent_ker_map_card ψ e2).trans hψ_ker_card)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e3.trans e4⟩)))))
    · -- (v) the binary octahedral group `2O = Ŝ₄` descends to `S₄`
      obtain ⟨e2⟩ := h2O
      haveI := pgl_descent_ker_map_normal ψ e2
      obtain ⟨e3⟩ := pgl_descent_quotient_transfer ψ hψ_surj e2
      obtain ⟨e4⟩ := pgl_descent_binaryOctahedral_quotient _
        ((pgl_descent_ker_map_card ψ e2).trans hψ_ker_card)
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨e3.trans e4⟩))))
-- ANCHOR_END: FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod

#min_imports
