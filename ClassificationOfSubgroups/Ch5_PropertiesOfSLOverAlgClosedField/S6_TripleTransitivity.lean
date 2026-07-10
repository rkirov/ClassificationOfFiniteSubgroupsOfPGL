import Mathlib

open scoped MatrixGroups
namespace Projectivization

variable {F : Type*} [Field F] [IsAlgClosed F]
variable {V: Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
variable (hV : Module.rank F V = 2)

-- Definition of triply transitive:
def triptrans_on (G : Type*) [Group G] (X : Type*) [MulAction G X]: Prop :=
  ∀ (x1 x2 x3 y1 y2 y3 : X),
  x1 ≠ x2 → x1 ≠ x3 → x2 ≠ x3 → y1 ≠ y2 → y1 ≠ y3 → y2 ≠ y3
  → ∃ (g : G ), g • x1 = y1 ∧ g • x2 = y2 ∧ g • x3 = y3

-- choosing an arbitrary baris of V:
noncomputable abbrev coord: (Fin 2 → F) ≃ₗ[F] V := (finDimVectorspaceEquiv 2 hV).symm
noncomputable abbrev f1: (Fin 2 → F) →ₗ[F] V := (coord (V:=V) hV).toLinearMap
noncomputable abbrev f2: V →ₗ[F] (Fin 2 → F) := (coord (V:=V) hV).symm.toLinearMap

-- In the following we define the group action of SL(2,F) on the projective line:
@[simps]
noncomputable def mulVV (z : SL(2,F)) : V →ₗ[F] V where
  toFun v := f1 hV ((z.val).mulVecLin (f2 hV v))
  map_add' := by
    intro x y
    show f1 hV ((z.val).mulVecLin (f2 hV (x + y))) =
      f1 hV ((z.val).mulVecLin (f2 hV x)) + f1 hV ((z.val).mulVecLin (f2 hV y))
    rw [map_add, map_add, map_add]
  map_smul' := by
    intro m x
    rw [LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul]
    simp


noncomputable def mulVP (z : SL(2,F)) (v : {u : V // u ≠ 0}) :
    Projectivization F V :=
  @Projectivization.mk F V _ _ _ ((mulVV hV z).toFun v.val)
  (by
    simp only [ne_eq, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, mulVV_apply, LinearEquiv.coe_coe,
      LinearEquiv.symm_symm, EmbeddingLike.map_eq_zero_iff]
    intro h
    have hneq_0: ((finDimVectorspaceEquiv 2 hV) v.val) ≠ 0 := by
      simp only [ne_eq, EmbeddingLike.map_eq_zero_iff]
      exact v.prop
    have hinj: Function.Injective (z.val).mulVec:= by
      exact Matrix.mulVec_injective_of_isUnit
        (by simp_rw [Matrix.isUnit_iff_isUnit_det, z.prop,
          isUnit_iff_ne_zero, ne_eq, one_ne_zero, not_false_eq_true])
    have hrw : (z.val).mulVecLin ((finDimVectorspaceEquiv 2 hV) v.val) = 0
      ↔ ((finDimVectorspaceEquiv 2 hV) v.val) = 0 := by
      constructor
      · rw [LinearMap.map_eq_zero_iff (z.val).mulVecLin ?_]
        · simp
        · exact hinj
      · exact fun a ↦ h
    rw[hrw] at h
    exact hneq_0 h
  )

noncomputable abbrev mulPP (z : SL(2, F)) (p : Projectivization F V) :
    Projectivization F V :=
  @Projectivization.lift F V _ _ _ (Projectivization F V) (f := (fun v => mulVP hV z v))
    (by
      intro a b f ha
      unfold mulVP
      rw [mk_eq_mk_iff']
      use f
      refine (LinearEquiv.eq_symm_apply (finDimVectorspaceEquiv 2 hV)).mpr ?_
      simp [ha]
      ) p


lemma mullVV_inj {F : Type u_1} [Field F] [IsAlgClosed F] {V : Type u_2} [AddCommGroup V]
  [Module F V] [FiniteDimensional F V]
    (hV : Module.rank F V = 2) (z : SL(2, F)): Function.Injective ⇑(mulVV hV z) := by
  refine LinearMap.injective_of_comp_eq_id (mulVV hV z) (mulVV hV z⁻¹) ?_
  ext v
  have mulVV_mul (g h : SL(2,F)) (v : V) : mulVV hV (g * h) v = (mulVV hV g) (mulVV hV h v) := by
    simp [mulVV, LinearMap.comp_apply]
  rw[LinearMap.comp_apply, ← mulVV_mul]
  simp


-- The above defined multiplication actually is a group action:
noncomputable def MyMulAct:
    MulAction (SL(2,F)) (Projectivization F V) where
  smul (g : SL(2,F)) (v : Projectivization F V) := mulPP hV g v
  one_smul b := by
    induction b with
    | h v h => simp [(· • ·), mulVP]
  mul_smul := by
    intro g h p
    refine Quot.induction_on p fun v =>
      (Projectivization.mk_eq_mk_iff F
      (mulVV hV (g*h) v.val) (mulVV hV g (mulVV hV h v.val)) ?_ ?_).2 ?_
    · intro h0
      rw [LinearMap.map_eq_zero_iff (mulVV hV (g * h)) (mullVV_inj hV (g*h))] at h0
      exact v.prop h0
    · intro h0
      rw [LinearMap.map_eq_zero_iff (mulVV hV g)
      (mullVV_inj hV g), LinearMap.map_eq_zero_iff (mulVV hV h) (mullVV_inj hV h)] at h0
      exact v.prop h0
    · let ax : Fˣ:= {
      val := 1
      inv := 1
      val_inv := by simp
      inv_val := by simp
      }
      use ax
      simp [ax]

-- lemmas, needed for the main proof:
lemma linind {F : Type*} [Field F] {V: Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (P Q:  Projectivization F V) (p q : V) (hPQ: P ≠ Q)
    (hp: p = Projectivization.rep P) (hq: q = Projectivization.rep Q):
    LinearIndependent F ![p, q] := by
  have: Projectivization.rep ∘ ![P, Q] =
    ![Projectivization.rep P, Projectivization.rep Q] := List.ofFn_inj.mp rfl
  rw [← independent_pair_iff_ne P Q, independent_iff, this] at hPQ
  rw [hp, hq]
  exact hPQ

lemma neq_0 {F : Type*} [Field F] {V: Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (Q R: Projectivization F V) (p q r: V) (a b : F) (hPQ: Q ≠ R)
    (hq: q = Projectivization.rep Q) (hr: r = Projectivization.rep R)
    (hab : a • p + b • q = r) : a ≠ 0 := by
  by_contra! has
  have: Projectivization.rep ∘ ![Q, R]
    = ![Projectivization.rep Q, Projectivization.rep R] := List.ofFn_inj.mp rfl
  rw[← independent_pair_iff_ne Q R, independent_iff, this] at hPQ
  rw[hq, hr, has] at hab
  have: ¬ (LinearIndependent F ![Q.rep, R.rep]) := by
    rw[← hab, LinearIndependent.pair_iff]
    intro h
    specialize h (-b) 1
    simp at h
  exact this hPQ

lemma hspan_eq {F : Type*} [Field F] {V: Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V]
    (a b : F) (ha: a ≠ 0) (hb: b ≠ 0)  (p q : V):
    Submodule.span F {b • q, a • p} = Submodule.span F {p, q} := by
  apply le_antisymm
  · rw [Submodule.span_le, Set.pair_subset_iff]
    constructor
    · exact Submodule.mem_span_pair.mpr (by use 0, b ; simp)
    · exact Submodule.mem_span_pair.mpr (by use a, 0 ; simp)
  · rw [Submodule.span_le, Set.pair_subset_iff]
    constructor
    · refine Submodule.mem_span_pair.mpr ?_
      use 0, a⁻¹
      rw [inv_smul_smul₀, zero_smul, zero_add]
      exact ha
    · refine Submodule.mem_span_pair.mpr ?_
      use b⁻¹, 0
      rw [inv_smul_smul₀, zero_smul, add_zero ]
      exact hb

lemma r_lincomb {F : Type*} [Field F] {V: Type*} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] (P Q R:  Projectivization F V) (p q r: V) (hp: p = Projectivization.rep P)
  (hq: q = Projectivization.rep Q) (hr: r = Projectivization.rep R)
  (hQR : Q ≠ R) (hPR : P ≠ R)
  (hspan: Submodule.span F (Set.range ![p, q]) = ⊤):
    ∃ (α β : F),  (α ≠ 0) ∧ ( β ≠ 0) ∧  r = α • p + β • q := by
    have h : r ∈ Submodule.span F (Set.range ![p, q]) := by simp only [hspan, Submodule.mem_top]
    have: ∃ (α β : F), α • p + β • q = r:= by
      rw[← Submodule.mem_span_pair]
      refine Set.mem_of_mem_of_subset h ?_
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
        Set.union_empty, Set.union_singleton, SetLike.coe_subset_coe]
      gcongr
      rw [Set.pair_subset_iff]
      exact ⟨Set.mem_insert_of_mem p rfl, Set.mem_insert p {q}⟩
    obtain ⟨α, β, hab⟩ := this
    use α, β, (neq_0 Q R p q r α β hQR hq hr hab),
      (neq_0 P R q p r β α hPR hp hr (by rw[add_comm]; exact hab))
    exact hab.symm

--Theorem 1.10 (in "Christopher Butler - Classification Of Finite Subgroups
-- Of The Two-Dimensional Special Linear Group
-- Over An Algebraically Closed Field (2019)")
example: @triptrans_on (SL(2,F)) _ (Projectivization F V) (MyMulAct hV) := by
  intro P1 P2 P3 Q1 Q2 Q3 hp12 hp13 hp23 hq12 hq13 hq23
  let p1 := Projectivization.rep P1
  let p2 := Projectivization.rep P2
  let p3 := Projectivization.rep P3
  let q1 := Projectivization.rep Q1
  let q2 := Projectivization.rep Q2
  let q3 := Projectivization.rep Q3

  have hli_p := linind P1 P2 p1 p2 hp12 rfl rfl
  have hli_q := linind Q1 Q2 q1 q2 hq12 rfl rfl
  have hspan_p := LinearIndependent.span_eq_top_of_card_eq_finrank hli_p
    (Eq.symm (Module.finrank_eq_of_rank_eq hV))
  have hspan_q := LinearIndependent.span_eq_top_of_card_eq_finrank hli_q
    (Eq.symm (Module.finrank_eq_of_rank_eq hV))

  -- We can write p3 (or q3) as a linear combination of p1 and p2 (pr q1 and q2):
  have hp3 := r_lincomb P1 P2 P3 p1 p2 p3 rfl rfl rfl hp23 hp13 hspan_p
  have hq3 := r_lincomb Q1 Q2 Q3 q1 q2 q3 rfl rfl rfl hq23 hq13 hspan_q

  obtain ⟨α, β, ha, hb, hp⟩ := hp3
  obtain ⟨γ, δ, hg, hd, hq⟩ := hq3

-- ![α • p1, β •p2] is a basis of V (span and linear independent):
  have hsp_sc_p: ⊤ ≤ Submodule.span F (Set.range ![α • p1, β •p2]) := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton, top_le_iff, (hspan_eq α β  ha hb  p1 p2)]
    rw [Matrix.range_cons_cons_empty p1 p2 ![]] at hspan_p
    exact hspan_p
  have hli_sc_p: LinearIndependent F ![α • p1, β •p2] := by
    rw [LinearIndependent.pair_iff] at ⊢ hli_p
    intro s t hst
    rw [← smul_assoc, ← smul_assoc] at hst
    specialize (hli_p (s • α) (t • β)) hst
    simp [ha, hb] at hli_p
    exact hli_p
  let vBasis := (Module.Basis.mk hli_sc_p hsp_sc_p)
--analogue for ![γ • q1, δ • q2]:
  have hspa_sc_q: ⊤ ≤ Submodule.span F (Set.range ![γ • q1, δ • q2]) := by
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton, top_le_iff, (hspan_eq γ δ hg hd  q1 q2)]
    rw [Matrix.range_cons_cons_empty q1 q2 ![]] at hspan_q
    exact hspan_q
  have hli_sc_q :  LinearIndependent F ![γ • q1, δ • q2] := by
    rw [LinearIndependent.pair_iff] at ⊢ hli_q
    intro s t hst
    rw [← smul_assoc,←  smul_assoc] at hst
    specialize (hli_q (s • γ) (t • δ)) hst
    simp [hg, hd] at hli_q
    exact hli_q

-- construct the Basis ![α • p1, β •p2] for V:
  let heq: (Fin 2 → V) ≃ₗ[F] V →ₗ[F] V := vBasis.constr  F
-- π maps the first basis element to  γ • q1, and the second to δ • q2. Therefor it maps p3 to q3:
  let π: V →ₗ[F] V := heq.toLinearMap ![γ • q1, δ • q2]
  have h_pi_1: π (α • p1) = γ • q1 := by
    have := vBasis.constr_basis F ![γ • q1, δ • q2] 0
    rw [Module.Basis.mk_apply hli_sc_p hsp_sc_p 0] at this
    exact this
  have h_pi_2: π (β • p2) = δ • q2 := by
    have := (Module.Basis.mk hli_sc_p hsp_sc_p).constr_basis F ![γ • q1, δ • q2] 1
    rw [Module.Basis.mk_apply hli_sc_p hsp_sc_p 1] at this
    exact this
  have h_pi_3: π p3 = q3 := by
    rw [hp, hq, LinearMap.map_add π (α • p1) (β • p2), h_pi_1, h_pi_2]
/-
  We will contruct a map φ: V → V, as a multiple of π.
  For the definition of triply transitive, we need a matrix Φ ∈ SL(2,F), that satisfies some porperties.
  φ it the map that coincides with the group action of Φ on V.
-/
  obtain ⟨n, hn⟩ := IsAlgClosed.exists_eq_mul_self (1 / π.det)
  let φ: V →ₗ[F] V := {
    toFun := n • π
    map_add' := by
      intro v w
      simp only [Pi.smul_apply, map_add, smul_add]
    map_smul' := by
      intro f x
      simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
      exact smul_comm n f (π x)
  }
  have pi_det_neq0: LinearMap.det π ≠ 0 := by
    intro hdet
    have := LinearMap.range_lt_top_of_det_eq_zero hdet
    rw [SetLike.lt_iff_le_and_exists] at this
    obtain ⟨hh1, hh2⟩ := this
    have: LinearMap.range π = ⊤ := by
      simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
      Set.union_empty, Set.union_singleton, top_le_iff] at hspa_sc_q
      ext v
      constructor
      · intro hv
        simp only [Submodule.mem_top]
      · rw[← hspa_sc_q, Submodule.mem_span_pair, ← h_pi_1, ← h_pi_2]
        intro ⟨a, b, hpii⟩
        use a • β • p2 + b • α • p1
        rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add ] at hpii
        exact hpii
    simp only [Submodule.mem_top, this, not_true_eq_false, and_false, exists_const] at hh2

-- Defining Φ as a Matrix in SL(2,F):
  let Φ : SL(2,F) := {
    val := LinearMap.toMatrix vBasis vBasis φ
    property :=  by
      rw[LinearMap.det_toMatrix]
      have: φ.det = n^2 * π.det := by
        have: 2 = Module.finrank F V := Eq.symm (Module.finrank_eq_of_rank_eq hV)
        rw[this, ← LinearMap.det_smul n π]
        rfl
      rw [← sq n] at hn
      rw[this, ← hn, one_div, inv_mul_cancel₀ ?_]
      intro hdet
      have := LinearMap.range_lt_top_of_det_eq_zero hdet
      rw [SetLike.lt_iff_le_and_exists] at this
      obtain ⟨hh1, hh2⟩ := this
      have: LinearMap.range π = ⊤ := by
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.range_cons, Matrix.range_empty,
         Set.union_empty, Set.union_singleton, top_le_iff] at hspa_sc_q
        ext v
        constructor
        · intro hv
          simp only [Submodule.mem_top]
        · rw[← hspa_sc_q, Submodule.mem_span_pair, ← h_pi_1, ← h_pi_2]
          intro ⟨a, b, hpii⟩
          use a • β • p2 + b • α • p1
          rw [← LinearMap.map_smul, ← LinearMap.map_smul, ← map_add ] at hpii
          exact hpii
      simp only [Submodule.mem_top, this, not_true_eq_false, and_false, exists_const] at hh2

    }
  use Φ

  /-
  It is left to show that ∀ i ∈ {1,2,3} : Φ • P_i = Q_i.
  To prove this, we have to show that the group action of SL(2,F) on V is independet of the choice of basis for V.
  -/
  have bas_choice (p' : V): (coord hV) ((Φ.val).mulVec ((finDimVectorspaceEquiv 2 hV) p')) = Fintype.linearCombination F vBasis (Φ.val.mulVec (vBasis.repr p')):= by
     -- b' is the Basis, which is imlicitly used by f1 and f2:
    have hli : LinearIndependent F ![f1 hV ![1,0], f1 hV ![0,1]] := by
      rw [LinearIndependent.pair_iff]
      intro s t
      rw [← LinearMap.map_smul_of_tower, ← LinearMap.map_smul_of_tower, ← map_add]
      simp
    have hspa : ⊤ ≤ Submodule.span F (Set.range ![f1 hV ![1,0], f1 hV ![0,1]]) := by
      rw [top_le_iff]
      exact LinearIndependent.span_eq_top_of_card_eq_finrank hli (Eq.symm (Module.finrank_eq_of_rank_eq hV))
    let b':= Module.Basis.mk hli hspa
    have f2_repr (v : V) : f2 hV v = b'.repr v := by sorry
    have f1_comb : f1 hV = Fintype.linearCombination F b' := by sorry
    sorry

  -- the following two "haves" are needed in two of the following analogeus three cases:
  have ny_val_inv (a'  b' : Fˣ) (α' γ' : F) (ha': α' ≠ 0 ) (hg': γ' ≠ 0 ): n • a' • (α')⁻¹ • γ' • (b')⁻¹ * b' • (γ')⁻¹ • α' • (a')⁻¹ • n⁻¹ = 1 := by
    rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc, smul_mul_assoc,
              show b' • (γ')⁻¹ • α' • a'⁻¹ • n⁻¹ = b' * (γ')⁻¹ • α' • (a')⁻¹  • n⁻¹ from rfl, Units.inv_mul_cancel_left, smul_inv_smul₀ hg' (α' • (a')⁻¹  • n⁻¹),
              inv_smul_smul₀ ha' ((a')⁻¹  • n⁻¹), smul_inv_smul, show n • n⁻¹ = n * n⁻¹ from rfl, mul_inv_cancel₀ ?_ ]
    rw[← zero_ne_mul_self, ← hn ]
    intro hpn
    rw [eq_div_iff pi_det_neq0, zero_mul (LinearMap.det π)] at hpn
    norm_num at hpn
  have ny_inv_val (a'  b' : Fˣ) (α' γ' : F) (ha': α' ≠ 0 ) (hg': γ' ≠ 0 ): b' • (γ')⁻¹ • α' • (a')⁻¹ • n⁻¹ * n • a' • (α')⁻¹ • γ' • (b')⁻¹ = 1 := by
    rw [← smul_assoc, smul_smul, smul_mul_assoc, smul_mul_assoc (a')⁻¹ n⁻¹ (n • a' • (α')⁻¹ • γ' • (b')⁻¹),
              mul_smul_comm, ← neg_mul_neg n⁻¹ (a' • (α')⁻¹ • γ' • (b')⁻¹), ← smul_mul_assoc, smul_neg , show n • n⁻¹ = n * n⁻¹ from rfl,
              mul_inv_cancel₀ ?_]
    · rw [neg_mul_neg, one_mul, smul_smul, inv_mul_cancel a', mul_smul, one_smul Fˣ,
              smul_inv_smul₀ ha', smul_smul, smul_mul_assoc, inv_mul_cancel₀ hg', smul_one_smul,
              Units.smul_def, smul_eq_mul, Units.val_inv_eq_inv_val,
              mul_inv_cancel₀ (Units.ne_zero b')]
    · rw [← zero_ne_mul_self, ← hn]
      intro hpn
      rw [eq_div_iff pi_det_neq0, zero_mul (LinearMap.det π)] at hpn
      norm_num at hpn

  split_ands
  · induction P1 with
    | h p1' hp' =>
      induction Q1 with
      | h q1' hq' =>
        have hpp1: ∃ a : Fˣ, a • p1 = p1' := by
          have h_mk: Projectivization.mk F p1' hp' = Projectivization.mk F p1 (rep_nonzero (mk F p1' hp')) := by rw [mk_rep]
          exact (mk_eq_mk_iff F p1' p1 hp' (rep_nonzero (mk F p1' hp'))).1 h_mk
        obtain ⟨a, haa⟩ := hpp1
        have hqq1: ∃ b : Fˣ, b • q1 = q1' := by
          have h_mk: Projectivization.mk F q1' hq' = Projectivization.mk F q1 (rep_nonzero (mk F q1' hq')) := by rw [mk_rep]
          exact (mk_eq_mk_iff F q1' q1 hq' (rep_nonzero (mk F q1' hq'))).1 h_mk
        obtain ⟨b, hbb⟩ := hqq1
        show mulPP hV Φ (mk F p1' hp') = mk F q1' hq'
        simp only [mulPP, mulVP, Projectivization.lift_mk]
        rw [ mk_eq_mk_iff F _ q1' _ hq']
        let ny : Fˣ := {
          val := n • a • α⁻¹ • γ • b⁻¹
          inv := b • γ⁻¹  • α • a⁻¹  • n⁻¹
          val_inv := ny_val_inv a b α γ ha hg
          inv_val := ny_inv_val a b α γ ha hg
        }
        use ny
        show ny • q1' = (coord hV) ((Φ.val).mulVec ((finDimVectorspaceEquiv 2 hV) p1'))
        rw[bas_choice p1']
        unfold Φ ny
        have: n • a • π p1 = n • a • α⁻¹ • π (α • p1) := by simp [inv_smul_smul₀ ha (π p1)]
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
        rw[LinearMap.toMatrix_mulVec_repr vBasis vBasis φ p1', show φ p1' = n • π p1' from rfl,
          ← haa, LinearMap.map_smul_of_tower π a p1, this, h_pi_1]
        have (d:V): (Fintype.linearCombination F ⇑vBasis) (vBasis.repr d) = d := by simp [Fintype.linearCombination_apply]
        rw[this]
        simp only [Units.val_inv_eq_inv_val, smul_eq_mul, Units.smul_mk_apply, ← hbb,]
        have: (n * a • (α⁻¹ * (γ * (↑b)⁻¹))) • b • q1 = ((n * a • (α⁻¹ * (γ * (↑b)⁻¹))) * b) • q1 := by
          rw [mul_smul (n * a • (α⁻¹ * (γ * (↑b)⁻¹))) (↑b) q1]
          rfl
        rw[this]
        have: (n * a • (α⁻¹ * (γ * (↑b)⁻¹))) * b = n * a • (α⁻¹ * γ):= by
          rw [← mul_assoc, ← mul_smul_comm , mul_assoc, mul_assoc, smul_mul_assoc, Units.inv_mul',
            mul_smul_one]
        rw [this, ← smul_eq_mul, ← smul_eq_mul , smul_assoc , smul_assoc , smul_assoc]
  · induction P2 with
    | h p2' hp' =>
      induction Q2 with
      | h q2' hq' =>
        have hpp2: ∃ a : Fˣ, a • p2 = p2' := by
          have h_mk: Projectivization.mk F p2' hp' = Projectivization.mk F p2 (rep_nonzero (mk F p2' hp')) := by rw [mk_rep]
          exact (mk_eq_mk_iff F p2' p2 hp' (rep_nonzero (mk F p2' hp'))).1 h_mk
        obtain ⟨a, haa⟩ := hpp2
        have hqq2: ∃ b : Fˣ, b • q2 = q2' := by
          have h_mk: Projectivization.mk F q2' hq' = Projectivization.mk F q2 (rep_nonzero (mk F q2' hq')) := by rw [mk_rep]
          exact (mk_eq_mk_iff F q2' q2 hq' (rep_nonzero (mk F q2' hq'))).1 h_mk
        obtain ⟨b, hbb⟩ := hqq2
        show mulPP hV Φ (mk F p2' hp') = mk F q2' hq'
        simp only [mulPP, mulVP, Projectivization.lift_mk]
        rw [ mk_eq_mk_iff F _ q2' _ hq']
        let ny : Fˣ := {
          val := n • a • β⁻¹ • δ • b⁻¹
          inv := b • δ⁻¹  • β • a⁻¹  • n⁻¹
          val_inv := ny_val_inv a b β δ hb hd
          inv_val := ny_inv_val a b β δ hb hd
        }
        use ny
        show ny • q2' = (coord hV) ((Φ.val).mulVec ((finDimVectorspaceEquiv 2 hV) p2'))
        rw[bas_choice p2']
        unfold Φ ny
        have: n • a • π p2 = n • a • β⁻¹ • π (β • p2) := by simp [inv_smul_smul₀ hb (π p2)]
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
        rw[LinearMap.toMatrix_mulVec_repr vBasis vBasis φ p2', show φ p2' = n • π p2' from rfl,
          ← haa, LinearMap.map_smul_of_tower π a p2, this, h_pi_2]
        have (d:V): (Fintype.linearCombination F ⇑vBasis) (vBasis.repr d) = d := by simp [Fintype.linearCombination_apply]
        rw[this]
        simp only [Units.val_inv_eq_inv_val, smul_eq_mul, Units.smul_mk_apply, ← hbb,]
        have: (n * a • (β⁻¹ * (δ * (↑b)⁻¹))) • b • q2 = ((n * a • (β⁻¹ * (δ * (↑b)⁻¹))) * b) • q2 := by
          rw [mul_smul (n * a • (β⁻¹ * (δ * (↑b)⁻¹))) b q2]
          rfl
        rw[this]
        have: (n * a • (β⁻¹ * (δ * (↑b)⁻¹))) * b = n * a • (β⁻¹ * δ):= by
          simp only [← mul_smul_comm, mul_assoc, smul_mul_assoc, ne_eq, Units.ne_zero,
            not_false_eq_true, inv_mul_cancel₀, mul_smul_one]
        rw [this, ← smul_eq_mul, ← smul_eq_mul , smul_assoc , smul_assoc , smul_assoc]
  · induction P3 with
    | h p3' hp' =>
      induction Q3 with
      | h q3' hq' =>
        have hpp3: ∃ a : Fˣ, a • p3 = p3' := by
          have h_mk: Projectivization.mk F p3' hp' = Projectivization.mk F p3 (rep_nonzero (mk F p3' hp')) := by rw [mk_rep]
          exact (mk_eq_mk_iff F p3' p3 hp' (rep_nonzero (mk F p3' hp'))).1 h_mk
        obtain ⟨a, haa⟩ := hpp3
        have hqq2: ∃ b : Fˣ, b • q3 = q3' := by
          have h_mk: Projectivization.mk F q3' hq' = Projectivization.mk F q3 (rep_nonzero (mk F q3' hq')) := by rw [mk_rep]
          exact (mk_eq_mk_iff F q3' q3 hq' (rep_nonzero (mk F q3' hq'))).1 h_mk
        obtain ⟨b, hbb⟩ := hqq2
        show mulPP hV Φ (mk F p3' hp') = mk F q3' hq'
        simp only [mulPP, mulVP, Projectivization.lift_mk]
        rw [ mk_eq_mk_iff F _ q3' _ hq']
        let ny : Fˣ := {
          val := n • a • b⁻¹
          inv := b • a⁻¹ • n⁻¹
          val_inv := by
            simp only [Units.val_inv_eq_inv_val, smul_eq_mul, mul_assoc, smul_mul_assoc, Units.smul_def b (a⁻¹ • n⁻¹), ne_eq, Units.ne_zero,
            not_false_eq_true, inv_mul_cancel_left₀, smul_inv_smul]
            rw [mul_inv_cancel₀ ?_ ]
            rw [← zero_ne_mul_self, ← hn]
            intro hpn
            rw [eq_div_iff pi_det_neq0, zero_mul (LinearMap.det π)] at hpn
            norm_num at hpn
          inv_val := by
            simp
            rw [smul_smul b a⁻¹ n⁻¹, smul_mul_assoc (b * a⁻¹) n⁻¹ (n * a • (↑b)⁻¹), inv_mul_cancel_left₀]
            · rw [smul_smul , inv_mul_cancel_right, Units.smul_def]
              simp
            · rw [← zero_ne_mul_self, ← hn]
              intro hpn
              rw [eq_div_iff pi_det_neq0, zero_mul (LinearMap.det π)] at hpn
              norm_num at hpn
        }
        use ny
        show ny • q3' = (coord hV) ((Φ.val).mulVec ((finDimVectorspaceEquiv 2 hV) p3'))
        rw[bas_choice p3']
        unfold Φ ny
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd]
        rw[LinearMap.toMatrix_mulVec_repr vBasis vBasis φ p3', show φ p3' = n • π p3' from rfl,
          ← haa, LinearMap.map_smul_of_tower π a p3, h_pi_3]
        have (d:V): (Fintype.linearCombination F ⇑vBasis) (vBasis.repr d) = d := by simp [Fintype.linearCombination_apply]
        simp only [this, Units.val_inv_eq_inv_val, smul_eq_mul, Units.smul_mk_apply, ← hbb,]
        rw [mul_smul, smul_assoc, Units.smul_def b q3, smul_smul, Units.inv_mul' b]
        simp
