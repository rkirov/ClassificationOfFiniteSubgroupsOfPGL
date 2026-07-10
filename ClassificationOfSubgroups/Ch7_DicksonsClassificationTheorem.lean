import ClassificationOfSubgroups.Ch4_PGLIsoPSLOverAlgClosedField.ProjectiveGeneralLinearGroup
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_A_MaximalAbelianSubgroup
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S4_CaseArithmetic
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S5_NumericClassEquation
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

open Matrix Subgroup LinearMap

open scoped MatrixGroups Pointwise


/- Lemma 3.1 -/
-- The original statement here was false: `H < K` gives `H ≤ K ≤ normalizer K`
-- (`Subgroup.le_normalizer`), directly contradicting `¬ H ≤ normalizer K`.
-- Restated to match Butler's actual Lemma 3.1 (`case2q`, tex ~line 1277): a proper
-- subgroup of a finite `p`-group `K` is strictly contained in its normalizer inside `K`.
lemma IsPGroup.lt_normalizer_subgroupOf {F : Type*} [Field F] {p : ℕ} [Fact (Nat.Prime p)]
  [CharP F p] (G : Subgroup SL(2,F)) (H K : Subgroup ↥G) [Finite ↥K] (hK : IsPGroup p ↥K)
  (H_lt_K : H < K) :
    H.subgroupOf K < normalizer ((H.subgroupOf K : Subgroup ↥K) : Set ↥K) := by
  have hnc : NormalizerCondition ↥K := Group.normalizerCondition_of_isNilpotent (G := ↥K)
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
Status: statement faithful to paper; **FAILED** -- proof attempted, blocked (analysis below), sorry
restored. Attempted for ~3 sessions' worth of exploration of the available `S2_A`/`S2_B`/`S5`
machinery; here is exactly where it breaks down.

TODO / failure analysis:
* The easy half (`(⊤ : Subgroup G) ≠ Q.toSubgroup`) *is* pure arithmetic and goes through in both
  branches of `CaseArithmetic.case_1_0`'s conclusion `(q = 1 ∧ g = g1) ∨ (1 < q ∧ k = g1 ∧
  g = q * k)`: in branch 1, `q = 1 < g1 ≤ g` (from `2 ≤ g1`); in branch 2, `q < q * k = g` (since
  `k = g1 ≥ 2`); either way `q = Nat.card Q.toSubgroup < g` while `Nat.card G = e * g` forces
  `Nat.card (⊤ : Subgroup G) = Nat.card G > Nat.card Q.toSubgroup` (this exact pattern is what makes
  the analogous step of `case_III` above go through). This part alone is genuinely provable.
* Everything else needs Butler's *concrete* `K = C_G(x) ⊓ G` (`x` a noncentral element of the
  Sylow subgroup `Q`) and the cyclic maximal abelian subgroup `A₁` realizing `g₁ = |A₁| / e`, both
  of which are only asserted to *exist abstractly* via the numeral `k`/`g1` in `heq` -- there is no
  witness subgroup in the hypotheses to attach `IsCyclic`/coprimality/complement facts to. The
  available machinery (`S2_B.exists_IsCyclic_K_normalizer_eq_Q_join_K`,
  `S5.sylow_class_data`) *does* produce a concrete cyclic complement `K` to `Q` with
  `normalizer Q.toSubgroup = Q.toSubgroup ⊔ K.subgroupOf G`, but critically **not** tied to the
  numeral `k` from `heq`: `S5.sylow_class_data` only gives the divisibility
  `Nat.card (center SL(2,F)) ∣ Nat.card K`, not the equality `Nat.card K = Nat.card (center
  SL(2,F)) * k` that Butler's proof (tex "`|K| = ek = eg₁ = |N_G(Q)|`") crucially uses to conclude
  `|N_G(Q)| = |G|` (hence `Q ⊴ G`) via the class-equation arithmetic. That equality is exactly
  `main_bridge`'s *construction* of `k` (`S5_NumericClassEquation.lean` ~942: `k := Nat.card K / e`
  for *this specific* `K`) -- i.e. the bridge from the abstract numeral `k` in `heq` back to a
  concrete `K` is a genuine (nontrivial, not yet built) *inverse* of `main_bridge`'s forward
  construction, not a bookkeeping gap. Concretely: `heq` is a bare existential over `k` with no
  handle on *which* subgroup realizes it, so `k = g1` (branch 2 of `case_1_0`) cannot be transported
  to `Nat.card K = Nat.card (center SL(2,F)) * g1` for the specific `K` `sylow_class_data` hands
  back, without additional hypotheses threading that identification through (which would require
  either (a) re-deriving `heq` from `main_bridge` applied to this very `G` so the same `K` is used
  throughout -- not available compositionally at this lemma's level -- or (b) strengthening
  `case_I`'s hypotheses to carry the witness `K`/`A₁` and the identifying equalities explicitly,
  which is a substantially larger restatement than a "minimal fix" and was judged out of scope
  here (it effectively promotes this lemma to redo the `K`-identification half of `main_bridge`
  bespoke for the `s=1,t=0` case).
* Separately, in branch 1 (`q = 1`, i.e. `Q = ⊥` trivial, `p ∤ Nat.card G`), the required conclusion
  is that `G` itself (`= K`, the complement to the trivial `Q`) is cyclic of order coprime to `p`.
  This is *Butler's actual content* of Case Ia (tex: "`G/Q = G = A₁`, which indeed is a cyclic
  group") -- i.e. it requires identifying `G` with the abstract `A₁` witnessing `g = g1`, which is
  precisely the same missing bridge (there is no `A₁` witness subgroup in `heq` to identify `G`
  with). This is not a corollary of anything currently proved in `S2_A`/`S2_B`/`S5`: it is, in
  effect, the base case of Butler's whole classification of the coprime-order groups (feeding into
  `dicksons_classification_theorem_class_I`), so proving it here would essentially require
  restating much of that theorem's content locally.
* Adding `[IsAlgClosed F] [DecidableEq F]` (needed by every one of the `S2_B`/`S5` lemmas cited
  above; `case_I` as given has neither) is a legitimate, well-justified *minimal* fix in the spirit
  of the other restatements in this file (matching the ambient hypotheses used everywhere else in
  `S2_A`/`S2_B`/`S5`, and matching `dicksons_classification_theorem_class_I`'s own hypotheses), but
  does not by itself close the gap above; it was not applied since it doesn't change the outcome. -/
lemma case_I {F : Type*} {p : ℕ} [Field F] [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q)
    (heq : ∃ k g1, 1 ≤ k ∧ 2 ≤ g1 ∧ (1 < k → k = g1) ∧
      ClassEquation g q k (s := 1) (t := 0) (fun _ => g1) (fun i => i.elim0)) :
    (⊤ : Subgroup G) ≠ Q.toSubgroup ∧ IsElementaryAbelian p Q.toSubgroup ∧
      Normal Q.toSubgroup ∧
      ∃ K : Subgroup G, IsComplement' Q.toSubgroup K ∧ IsCyclic K ∧
        Nat.Coprime p (Nat.card K) := by
  -- TODO: see failure analysis in the docstring above -- the `(⊤ : Subgroup G) ≠ Q.toSubgroup`
  -- conjunct alone is provable by the same numeric argument as `case_III` (`q < g`, both branches
  -- of `CaseArithmetic.case_1_0`), but the remaining three conjuncts need a concrete witness for
  -- Butler's `K`/`A₁` tied to the abstract `k`/`g1` in `heq`, which is not threaded through to
  -- this lemma (see analysis above for exactly what would need to change).
  sorry

/-- Butler Case II (tex 1453-1640): `s = 1, t = 1`. Forces `p ∤ |G|` (`q = 1`) and pins down
`g₁ ∈ {2,3}`; Case IIa (`g₁ = 2`) constructs the dicyclic group of order `4n` (`n` odd) presented
as `⟨x,y | x^n = y^2, yxy⁻¹ = x⁻¹⟩` (tex ~1550-1580) -- this is exactly mathlib's
`QuaternionGroup n` (order `4n`, presentation `⟨a,x | a^{2n}=1, x^2=a^n, x⁻¹ax=a⁻¹⟩`, which
matches Butler's `x ↦ a`, `y ↦ x`); Case IIb (`g₁ = 3`) constructs an explicit isomorphism with
`SL(2,3)` (tex ~1600-1640).
Status: statement faithful to paper; proof pending (needs Theorem 6.8 to identify Butler's `K`,
`A₁`, `A₂` with concrete subgroups of `G`, `CaseArithmetic.case_1_1`, then the genuinely
group-theoretic generator/relation argument of Case IIa/IIb). -/
lemma case_II {F : Type*} {p : ℕ} [Field F] [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q)
    (heq : ∃ k g1 g2, 1 ≤ k ∧ 2 ≤ g1 ∧ 2 ≤ g2 ∧ (g2 < k → k = g1) ∧
      ClassEquation g q k (s := 1) (t := 1) (fun _ => g1) (fun _ => g2)) :
    Isomorphic G SL(2, ZMod 3) ∨ ∃ n, Odd n ∧ Isomorphic G (QuaternionGroup n) := by sorry

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

/-- Butler Case IV (tex 1681-1745): `s = 0, t = 1`. Forces `k = 1` and `q ∈ {2,3}`. Case IVa
(`q = 2`, so `p = 2`) constructs `G ≅ D_n` (dihedral of order `2n`, `n` odd -- note `Z` is
trivial in characteristic `2`, so this is genuinely a dihedral, not dicyclic, group here); Case
IVb (`q = 3`, so `p = 3`) constructs an isomorphism with `SL(2,3)` by an argument "analogous to
Case IIb" (tex ~1785).
Status: statement faithful to paper; proof pending (needs Theorem 6.8 to identify `A₁` with a
concrete subgroup of `G`, `CaseArithmetic.case_0_1`, then the Case IVa/IVb generator arguments). -/
lemma case_IV {F : Type*} {p : ℕ} [Field F] [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q)
    (heq : ∃ k g1, 1 ≤ k ∧ 2 ≤ g1 ∧ 2 * g1 ≤ g ∧
      ClassEquation g q k (s := 0) (t := 1) (fun i => i.elim0) (fun _ => g1)) :
    (p = 2 ∧ ∃ n, Odd n ∧ Isomorphic G (DihedralGroup n)) ∨
      (p = 3 ∧ Isomorphic G SL(2, ZMod 3)) := by sorry


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

/-- Butler Case VI (tex 2115-2160): `s = 0, t = 3`. Forces `q = 1` (`CaseArithmetic.case_0_3`)
and, via a further elementary argument (tex ~2145-2160), `g₁ = 2` with
`(g₂,g₃) ∈ {(2,n), (3,4), (3,5)}`. Case VIa (`g₂ = 2`) gives the dicyclic group of order `4n`
(`n` even) as `QuaternionGroup n`; Case VIb (`g₂ = 3, g₃ = 4`) gives `Ŝ₄`, the representation
group of `S₄` in which transpositions have order `4` -- Butler notes `Ŝ₄ ≅ GL(2,3)`, so this is
`GL (Fin 2) (ZMod 3)`; Case VIc (`g₂ = 3, g₃ = 5`) gives `G ≅ SL(2,5)`, this time with `p ∤ |G|`
(unlike the isomorphic-but-distinct Case Vd, where `p = 3 = q`).
Status: statement faithful to paper; proof pending (needs `CaseArithmetic.case_0_3` plus the
Sylow-conjugacy argument ruling out `g₂ = g₃ = 3` and the `S₄`-representation-group argument of
Case VIb, tex ~2178-2201). -/
lemma case_VI {F : Type*} {p : ℕ} [Fact (Nat.Prime p)] [Field F] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (Q : Sylow p G) (g q : ℕ) (hg : Nat.card G = Nat.card (center SL(2,F)) * g)
    (hq : Nat.card Q.toSubgroup = q)
    (heq : ∃ k g1 g2 g3, 2 ≤ g1 ∧ 2 ≤ g2 ∧ 2 ≤ g3 ∧ (1 < k → k = g1 ∨ k = g2 ∨ k = g3) ∧
      ClassEquation g q k (s := 0) (t := 3) (fun i => i.elim0) ![g1, g2, g3]) :
    (∃ n, Even n ∧ Isomorphic G (QuaternionGroup n)) ∨
      Isomorphic G (GL (Fin 2) (ZMod 3)) ∨
      (¬ p ∣ Nat.card G ∧ Isomorphic G SL(2, ZMod 5)) := by sorry


 -- (v) Ŝ₄ , the representation group of S4 in which the transpositions correspond to
-- the elements of order 4.

instance five_prime : Fact (Nat.Prime 5) := { out := by decide }

/-- **Theorem 3.6, Class I** (tex 2213-2226, "Class I: when `p = 0` or `|G|` is relatively prime
to `p`"). Every finite subgroup `G ≤ SL(2,F)` of order coprime to `p` (or with `p = 0`) is
isomorphic to one of: a cyclic group; the dicyclic group `⟨x,y | x^n = y^2, yxy⁻¹ = x⁻¹⟩` of order
`4n` for *arbitrary* `n` (mathlib's `QuaternionGroup n`, tex Class I (ii), covering both Case IIa
`n` odd and Case VIa `n` even); `SL(2,3)`; `SL(2,5)`; or `Ŝ₄` (the representation group of `S₄`
with transpositions of order `4`, tex Class I (v)), which Butler identifies with `GL(2,3)`.
Note: the original statement here had `DihedralGroup n` for a file-level auto-bound `n : Type*`
(ill-typed/vacuously-scoped), and used the *dihedral* group where `SL(2,F)` (with `p ≠ 2`, having
a unique involution) actually only ever produces the *dicyclic*/quaternion group; both bugs are
fixed here.
Status: statement faithful to paper; proof pending (needs the full case-by-case matching of tex
2237-2254, i.e. `case_I` ... `case_VI` above, plus the `Z ⊄ G ⟹ |G|` odd `⟹` Case I/III branch). -/
-- ANCHOR: dicksons_classification_theorem_class_I
theorem dicksons_classification_theorem_class_I {F : Type*} [Field F] [IsAlgClosed F]
    {p : ℕ} [CharP F p] (hp : Prime p) (G : Subgroup (SL(2,F))) [Finite G]
    (hp' : p = 0 ∨ Nat.Coprime (Nat.card G) p) :
    IsCyclic G ∨
      (∃ n, Isomorphic G (QuaternionGroup n)) ∨
      Isomorphic G SL(2, ZMod 3) ∨
      Isomorphic G SL(2, ZMod 5) ∨
      Isomorphic G (GL (Fin 2) (ZMod 3))
  := by sorry
-- ANCHOR_END: dicksons_classification_theorem_class_I

-- Ŝ₄ is isomorphic to GL₂(F₃)

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
