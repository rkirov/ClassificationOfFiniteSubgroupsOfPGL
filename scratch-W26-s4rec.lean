import ClassificationOfSubgroups.Ch7_DicksonsClassificationTheorem
import ClassificationOfSubgroups.Ch7_S4Recognition

set_option linter.style.longLine true
set_option maxHeartbeats 1000000

open Matrix Subgroup LinearMap Ch7GroupRecognition MulAut

open scoped MatrixGroups Pointwise

open MaximalAbelianSubgroup

open CaseArithmetic

open Polynomial

open SpecialMatrices

variable {p : ℕ} [hp : Fact (Nat.Prime p)] {n m : ℕ+}

open FreeGroup Symbols PresentedGroup

/-- **Small-orbit contradiction (Butler Case VIb workhorse).** In a `|G| = 48` class-VI group
with an order-`6` maximal abelian class `Ab`, no noncentral `w ∈ G` can have all its
`G`-conjugates in `{w, w⁻¹}`: the centralizer class `C = C_{SL₂}(w) ⊓ G` would have index `≤ 2`
in `G`, hence contain the order-`3` element `b` of `Ab` (as `b = (b²)²` and squares land in an
index-`≤ 2` subgroup), forcing `C = Ab` (two maximal abelian classes sharing the noncentral `b`
coincide) of order `6` — but then `48 = |G| ≤ 2 · 6`. -/
private lemma caseVI_b_orbit_aux {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (he2 : Nat.card (center SL(2,F)) = 2) (hG48 : Nat.card G = 48)
    (Ab : Subgroup SL(2,F)) (hAb_mem : Ab ∈ MaximalAbelianSubgroupsOf G)
    (hAb6 : Nat.card Ab = 6)
    (w : ↥G) (hw_ncen : (w : SL(2,F)) ∉ center SL(2,F))
    (hconj : ∀ g : ↥G, g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w⁻¹) : False := by
  classical
  -- `C := C_{SL₂}(w) ⊓ G` is a maximal abelian subgroup of `G`
  have hC_mem : centralizer {(w : SL(2,F))} ⊓ G ∈ MaximalAbelianSubgroupsOf G :=
    centralizer_inf_mem_maximalAbelianSubgroupsOf_of_noncentral G _ ⟨w.2, hw_ncen⟩
  set C : Subgroup SL(2,F) := centralizer {(w : SL(2,F))} ⊓ G with hC_def
  set C' : Subgroup ↥G := C.subgroupOf G with hC'_def
  -- two conjugators of `w` to the same element differ by an element of `C'`
  have hmem_of_conj_eq : ∀ a b : ↥G, a * w * a⁻¹ = b * w * b⁻¹ → a⁻¹ * b ∈ C' := by
    intro a b h
    have hcomm : w * (a⁻¹ * b) = (a⁻¹ * b) * w := by
      calc w * (a⁻¹ * b) = a⁻¹ * (a * w * a⁻¹) * b := by group
        _ = a⁻¹ * (b * w * b⁻¹) * b := by rw [h]
        _ = (a⁻¹ * b) * w := by group
    rw [hC'_def, Subgroup.mem_subgroupOf, hC_def, Subgroup.mem_inf]
    refine ⟨?_, (a⁻¹ * b).2⟩
    rw [Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    exact_mod_cast congrArg Subtype.val hcomm
  -- the coset space `G ⧸ C'` injects into `{w, w⁻¹}` (conjugate-of-`w` fibers), so it has `≤ 2`
  -- elements
  have hqle : Nat.card (↥G ⧸ C') ≤ 2 := by
    have hinj : Function.Injective (fun q : ↥G ⧸ C' =>
        (⟨q.out * w * q.out⁻¹, by
          rcases hconj q.out with h | h <;> rw [h] <;> simp⟩ : ({w, w⁻¹} : Set ↥G))) := by
      intro q q' h
      have h' : q.out * w * q.out⁻¹ = q'.out * w * q'.out⁻¹ := congrArg Subtype.val h
      have heq : (QuotientGroup.mk q.out : ↥G ⧸ C') = QuotientGroup.mk q'.out :=
        QuotientGroup.eq.mpr (hmem_of_conj_eq _ _ h')
      rwa [QuotientGroup.out_eq', QuotientGroup.out_eq'] at heq
    have hcard_le := Nat.card_le_card_of_injective _ hinj
    have hpair : Nat.card ({w, w⁻¹} : Set ↥G) ≤ 2 := by
      rw [Nat.card_coe_set_eq]
      have h := Set.ncard_insert_le w ({w⁻¹} : Set ↥G)
      rw [Set.ncard_singleton] at h
      omega
    exact le_trans hcard_le hpair
  -- hence `C'` has index `≤ 2` in `G`
  have hidx : C'.index = 1 ∨ C'.index = 2 := by
    have h1 : C'.index ≤ 2 := by rw [Subgroup.index_eq_card]; exact hqle
    have h2 : C'.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  -- the order-`3` element `b` of `Ab`
  haveI hAb_fin : Finite Ab :=
    (Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hAb_mem.right).to_subtype
  obtain ⟨b₀, hb₀⟩ := exists_prime_orderOf_dvd_card' (G := Ab) 3 (by rw [hAb6]; norm_num)
  have hbG : (b₀ : SL(2,F)) ∈ G := hAb_mem.right b₀.2
  set bb : ↥G := ⟨(b₀ : SL(2,F)), hbG⟩ with hbb_def
  have hbb_ord : orderOf bb = 3 := by
    have h1 : orderOf (bb : SL(2,F)) = 3 := by
      show orderOf (b₀ : SL(2,F)) = 3
      rw [orderOf_coe]; exact hb₀
    rw [← orderOf_coe bb]; exact h1
  have hbb3 : bb ^ 3 = 1 := by rw [← hbb_ord]; exact pow_orderOf_eq_one bb
  -- `bb ∈ C'`: an index-`≤ 2` subgroup contains all squares, and `bb = (bb²)²`
  have hbbC : bb ∈ C' := by
    have hbb4 : (bb ^ 2) ^ 2 = bb := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hbb3, one_mul]
    rcases hidx with h1 | h2
    · have htop : C' = ⊤ := Subgroup.index_eq_one.mp h1
      rw [htop]; exact Subgroup.mem_top bb
    · haveI : C'.Normal := Subgroup.normal_of_index_eq_two h2
      have hsq : bb ^ 2 ∈ C' := by
        have h := Subgroup.pow_index_mem C' bb
        rwa [h2] at h
      rw [← hbb4]
      exact Subgroup.pow_mem C' hsq 2
  have hbC : (bb : SL(2,F)) ∈ C := Subgroup.mem_subgroupOf.mp hbbC
  -- `bb` is noncentral (order `3` does not divide `|Z(SL₂)| = 2`)
  have hb_ncen : (bb : SL(2,F)) ∉ center SL(2,F) := by
    intro hb
    have h := orderOf_dvd_natCard (⟨(bb : SL(2,F)), hb⟩ : center SL(2,F))
    rw [orderOf_mk, orderOf_coe, hbb_ord, he2] at h
    norm_num at h
  -- two maximal abelian classes sharing the noncentral `bb` coincide: `Ab = C`
  have hAbC : Ab = C := by
    by_contra hne
    have hmeet := center_eq_meet_of_ne_MaximalAbelianSubgroups Ab C G hAb_mem hC_mem hne
      center_le_G
    exact hb_ncen (hmeet ▸ (Subgroup.mem_inf.mpr ⟨b₀.2, hbC⟩))
  -- counting: `48 = |G| = |G ⧸ C'| · |C'| ≤ 2 · 6`
  have hC'card : Nat.card C' = 6 := by
    rw [hC'_def, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, ← hC_def,
      ← hAbC]
    exact hAb6
  have hcount := Subgroup.card_eq_card_quotient_mul_card_subgroup C'
  rw [hG48, hC'card] at hcount
  omega

/-- **Case VIb: the order-`24` quotient has no normal subgroup of order `3`** — a normal `B̄`
of order `3` in `G ⧸ ⟨z⟩` is generated by an order-`3` `v`, which lifts (after adjusting by `z`)
to an order-`3` element `w ∈ G` whose conjugates all lie in `{w, w⁻¹}` (they descend into
`B̄ \ {1} = {v, v⁻¹}`, and the `·z`-coset alternatives have nontrivial cubes), contradicting
`caseVI_b_orbit_aux`. -/
private lemma caseVI_b_no_normal_card_three {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (he2 : Nat.card (center SL(2,F)) = 2) (hG48 : Nat.card G = 48)
    (z : ↥G) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hz_cen : z ∈ Subgroup.center ↥G)
    [hzNormal : (Subgroup.zpowers z).Normal]
    (Ab : Subgroup SL(2,F)) (hAb_mem : Ab ∈ MaximalAbelianSubgroupsOf G)
    (hAb6 : Nat.card Ab = 6)
    (B : Subgroup (↥G ⧸ Subgroup.zpowers z)) (hBnorm : B.Normal) (hB3 : Nat.card B = 3) :
    False := by
  classical
  have hzcomm : ∀ x : ↥G, x * z = z * x := fun x => Subgroup.mem_center_iff.mp hz_cen x
  have hz3 : z ^ 3 = z := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hz2, one_mul]
  -- an order-`3` generator `v` of `B`
  obtain ⟨v₀, hv₀⟩ := exists_prime_orderOf_dvd_card' (G := B) 3 (by rw [hB3])
  have hv_ord : orderOf (v₀ : ↥G ⧸ Subgroup.zpowers z) = 3 := (orderOf_coe v₀).trans hv₀
  have hv3 : (v₀ : ↥G ⧸ Subgroup.zpowers z) ^ 3 = 1 := by
    rw [← hv_ord]; exact pow_orderOf_eq_one _
  have hv1 : (v₀ : ↥G ⧸ Subgroup.zpowers z) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hv_ord
    norm_num at hv_ord
  have hBz : Subgroup.zpowers (v₀ : ↥G ⧸ Subgroup.zpowers z) = B :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr v₀.2)
      (by rw [Nat.card_zpowers, hv_ord, hB3])
  -- lift `v` to an order-`3` element `w` of `G` (adjusting the lift by `z` if needed)
  obtain ⟨w₀, hw₀⟩ := QuotientGroup.mk_surjective (v₀ : ↥G ⧸ Subgroup.zpowers z)
  have hw₀3 : w₀ ^ 3 ∈ Subgroup.zpowers z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hw₀]
    exact hv3
  obtain ⟨w, hwmk, hw3⟩ : ∃ w : ↥G,
      QuotientGroup.mk w = (v₀ : ↥G ⧸ Subgroup.zpowers z) ∧ w ^ 3 = 1 := by
    rcases binaryOctahedral_mem_zpowers_involution hz2 _ hw₀3 with h | h
    · exact ⟨w₀, hw₀, h⟩
    · refine ⟨w₀ * z, ?_, ?_⟩
      · rw [QuotientGroup.mk_mul, hw₀,
          (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z), mul_one]
      · have hc : Commute w₀ z := hzcomm w₀
        rw [hc.mul_pow, h, hz3]
        rw [show z * z = z ^ 2 from (sq z).symm, hz2]
  have hwne : w ≠ 1 := by
    intro h
    exact hv1 (by rw [← hwmk, h, QuotientGroup.mk_one])
  have hw_ord : orderOf w = 3 := orderOf_eq_prime hw3 hwne
  -- all conjugates of `w` lie in `{w, w⁻¹}`
  have hconj : ∀ g : ↥G, g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w⁻¹ := by
    intro g
    have hconj3 : (g * w * g⁻¹) ^ 3 = 1 := by
      calc (g * w * g⁻¹) ^ 3 = g * w ^ 3 * g⁻¹ := _root_.conj_pow
        _ = 1 := by rw [hw3]; group
    -- the conjugate descends into `B = ⟨v⟩`
    have hmkconj : (QuotientGroup.mk (g * w * g⁻¹) : ↥G ⧸ Subgroup.zpowers z)
        ∈ Subgroup.zpowers (v₀ : ↥G ⧸ Subgroup.zpowers z) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hwmk, hBz]
      exact hBnorm.conj_mem _ v₀.2 (QuotientGroup.mk g)
    obtain ⟨k, hk⟩ := hmkconj
    have hk' : (v₀ : ↥G ⧸ Subgroup.zpowers z) ^ k = QuotientGroup.mk (g * w * g⁻¹) := hk
    have hv3' : (v₀ : ↥G ⧸ Subgroup.zpowers z) ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, _root_.zpow_natCast, hv3]
    have hdecomp : (v₀ : ↥G ⧸ Subgroup.zpowers z) ^ k
        = (v₀ : ↥G ⧸ Subgroup.zpowers z) ^ (k % 3) := by
      conv_lhs => rw [← Int.mul_ediv_add_emod k 3]
      rw [_root_.zpow_add, _root_.zpow_mul, hv3', _root_.one_zpow, one_mul]
    have hrange : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
    rcases hrange with h0 | h1 | h2
    · -- `mk (g w g⁻¹) = 1`: impossible (`w ≠ 1` and `z` has trivial cube-defect)
      exfalso
      have hmk : QuotientGroup.mk (g * w * g⁻¹) = (1 : ↥G ⧸ Subgroup.zpowers z) := by
        rw [← hk', hdecomp, h0, _root_.zpow_zero]
      have hmem := (QuotientGroup.eq_one_iff _).mp hmk
      rcases binaryOctahedral_mem_zpowers_involution hz2 _ hmem with hcase | hcase
      · apply hwne
        calc w = g⁻¹ * (g * w * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by rw [hcase]
          _ = 1 := by group
      · apply hz1
        rw [← hz3, ← hcase]
        exact hconj3
    · -- `mk (g w g⁻¹) = v`: the conjugate is `w` (the `w z` alternative has cube `z ≠ 1`)
      have hmk : QuotientGroup.mk (g * w * g⁻¹)
          = (QuotientGroup.mk w : ↥G ⧸ Subgroup.zpowers z) := by
        rw [← hk', hdecomp, h1, _root_.zpow_one, hwmk]
      rcases binaryOctahedral_mem_zpowers_involution hz2 _ (QuotientGroup.eq.mp hmk)
        with hcase | hcase
      · exact Or.inl (inv_mul_eq_one.mp hcase)
      · exfalso
        apply hz1
        have hh : (g * w * g⁻¹) * z = w := by rw [← hcase]; group
        have hcz : Commute (g * w * g⁻¹) z := hzcomm _
        calc z = z ^ 3 := hz3.symm
          _ = (g * w * g⁻¹) ^ 3 * z ^ 3 := by rw [hconj3, one_mul]
          _ = ((g * w * g⁻¹) * z) ^ 3 := (hcz.mul_pow 3).symm
          _ = w ^ 3 := by rw [hh]
          _ = 1 := hw3
    · -- `mk (g w g⁻¹) = v²`: the conjugate is `w² = w⁻¹` (again `· z` has cube `z ≠ 1`)
      have hmk : QuotientGroup.mk (g * w * g⁻¹)
          = (QuotientGroup.mk (w * w) : ↥G ⧸ Subgroup.zpowers z) := by
        rw [← hk', hdecomp, h2, _root_.zpow_two, ← hwmk, ← QuotientGroup.mk_mul]
      have hww : w * w = w⁻¹ := by
        have h : w ^ 2 * w = 1 := by rw [← pow_succ]; exact hw3
        rw [← sq]
        exact eq_inv_of_mul_eq_one_left h
      rcases binaryOctahedral_mem_zpowers_involution hz2 _ (QuotientGroup.eq.mp hmk)
        with hcase | hcase
      · refine Or.inr ?_
        rw [inv_mul_eq_one.mp hcase, hww]
      · exfalso
        apply hz1
        have hh : (g * w * g⁻¹) * z = w * w := by rw [← hcase]; group
        have h6 : (w * w) ^ 3 = 1 := by
          rw [← sq, ← pow_mul, show 2 * 3 = 3 * 2 from rfl, pow_mul, hw3, one_pow]
        have hcz : Commute (g * w * g⁻¹) z := hzcomm _
        calc z = z ^ 3 := hz3.symm
          _ = (g * w * g⁻¹) ^ 3 * z ^ 3 := by rw [hconj3, one_mul]
          _ = ((g * w * g⁻¹) * z) ^ 3 := (hcz.mul_pow 3).symm
          _ = (w * w) ^ 3 := by rw [hh]
          _ = 1 := h6
  -- `w` is noncentral in `SL(2,F)` (order `3` does not divide `2`), so the orbit lemma applies
  have hw_ncen : (w : SL(2,F)) ∉ center SL(2,F) := by
    intro hcen
    have h := orderOf_dvd_natCard (⟨(w : SL(2,F)), hcen⟩ : center SL(2,F))
    rw [orderOf_mk, orderOf_coe, hw_ord, he2] at h
    norm_num at h
  exact caseVI_b_orbit_aux G center_le_G he2 hG48 Ab hAb_mem hAb6 w hw_ncen hconj

/-- **Case VIb: the order-`24` quotient has no central involution** — a central involution `u`
of `G ⧸ ⟨z⟩` lifts to an order-`4` element `w ∈ G` (with `w² = z`, by uniqueness of the
involution), whose conjugates all lie in `{w, w z} = {w, w⁻¹}` by centrality of `u`,
contradicting `caseVI_b_orbit_aux`. -/
private lemma caseVI_b_no_central_involution {F : Type*} [Field F] [IsAlgClosed F]
    [DecidableEq F]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (he2 : Nat.card (center SL(2,F)) = 2) (hG48 : Nat.card G = 48)
    (z : ↥G) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (huniq : ∀ w : ↥G, w ^ 2 = 1 → w ≠ 1 → w = z)
    [hzNormal : (Subgroup.zpowers z).Normal]
    (Ab : Subgroup SL(2,F)) (hAb_mem : Ab ∈ MaximalAbelianSubgroupsOf G)
    (hAb6 : Nat.card Ab = 6) :
    ∀ u : ↥G ⧸ Subgroup.zpowers z, u ∈ Subgroup.center (↥G ⧸ Subgroup.zpowers z) →
      u ^ 2 = 1 → u = 1 := by
  intro u hu_cen hu2
  by_contra hu1
  obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective u
  -- the lift has `w² = z`, hence order `4`
  have hw1 : w ≠ 1 := by
    intro h
    exact hu1 (by rw [← hw, h, QuotientGroup.mk_one])
  have hsqmem : w ^ 2 ∈ Subgroup.zpowers z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hw]
    exact hu2
  have hw2z : w ^ 2 = z := by
    rcases binaryOctahedral_mem_zpowers_involution hz2 _ hsqmem with h | h
    · exfalso
      apply hu1
      rw [← hw, huniq w h hw1]
      exact (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
    · exact h
  have hw4 : w ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hw2z, hz2]
  have hw_ord : orderOf w = 4 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := orderOf_eq_prime_pow (x := w) (p := 2) (n := 1)
      (by rw [pow_one, hw2z]; exact hz1)
      (by rw [show (2 : ℕ) ^ 2 = 4 by norm_num]; exact hw4)
    rw [h]; norm_num
  -- centrality of `u` puts every conjugate of `w` in `{w, w z} = {w, w⁻¹}`
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hz2)
  have hconj : ∀ g : ↥G, g * w * g⁻¹ = w ∨ g * w * g⁻¹ = w⁻¹ := by
    intro g
    have hmk : (QuotientGroup.mk (g * w * g⁻¹) : ↥G ⧸ Subgroup.zpowers z)
        = QuotientGroup.mk w := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hw]
      have hcen := Subgroup.mem_center_iff.mp hu_cen (QuotientGroup.mk g)
      calc QuotientGroup.mk g * u * (QuotientGroup.mk g)⁻¹
          = u * QuotientGroup.mk g * (QuotientGroup.mk g)⁻¹ := by rw [hcen]
        _ = u := by group
    rcases binaryOctahedral_mem_zpowers_involution hz2 _ (QuotientGroup.eq.mp hmk)
      with hcase | hcase
    · exact Or.inl (inv_mul_eq_one.mp hcase)
    · refine Or.inr ?_
      have hh : (g * w * g⁻¹) * z = w := by rw [← hcase]; group
      have hw3inv : w ^ 3 = w⁻¹ := by
        have h : w ^ 3 * w = 1 := by rw [← pow_succ]; exact hw4
        exact eq_inv_of_mul_eq_one_left h
      calc g * w * g⁻¹ = ((g * w * g⁻¹) * z) * z⁻¹ := by group
        _ = w * z⁻¹ := by rw [hh]
        _ = w * z := by rw [hzinv]
        _ = w * w ^ 2 := by rw [hw2z]
        _ = w ^ 3 := by
          rw [show (3 : ℕ) = 2 + 1 from rfl]
          exact (pow_succ' w 2).symm
        _ = w⁻¹ := hw3inv
  -- `w` is noncentral in `SL(2,F)` (order `4` does not divide `2`), so the orbit lemma applies
  have hw_ncen : (w : SL(2,F)) ∉ center SL(2,F) := by
    intro hcen
    have h := orderOf_dvd_natCard (⟨(w : SL(2,F)), hcen⟩ : center SL(2,F))
    rw [orderOf_mk, orderOf_coe, hw_ord, he2] at h
    norm_num at h
  exact caseVI_b_orbit_aux G center_le_G he2 hG48 Ab hAb_mem hAb6 w hw_ncen hconj

/-- Scratch mirror of the final `caseVI_b_quotient_iso_S4`, calling the actual
`Ch7_S4Recognition` module (compiled to an olean by hand for this test). -/
lemma scratch_caseVI_b_quotient_iso_S4 {F : Type*} {p : ℕ} [Field F] [IsAlgClosed F]
    [DecidableEq F] [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (hp_ne_two : p ≠ 2) (hcard48 : Nat.card G = 48)
    (z : ↥G) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (huniq : ∀ w : ↥G, w ^ 2 = 1 → w ≠ 1 → w = z)
    [hzNormal : (Subgroup.zpowers z).Normal]
    (Aa : Subgroup SL(2,F)) (hAa_mem : Aa ∈ MaximalAbelianSubgroupsOf G) (hAa4 : Nat.card Aa = 4)
    (Ab : Subgroup SL(2,F)) (hAb_mem : Ab ∈ MaximalAbelianSubgroupsOf G) (hAb6 : Nat.card Ab = 6)
    (Ac : Subgroup SL(2,F)) (hAc_mem : Ac ∈ MaximalAbelianSubgroupsOf G) (hAc8 : Nat.card Ac = 8)
    (hAc_cyc : IsCyclic Ac)
    (hAa_relIndex : relIndex (Aa.subgroupOf G) (normalizer (Aa.subgroupOf G : Set ↥G)) = 2)
    (hAc_relIndex : relIndex (Ac.subgroupOf G) (normalizer (Ac.subgroupOf G : Set ↥G)) = 2) :
    ∃ f : (↥G ⧸ Subgroup.zpowers z) ≃* Equiv.Perm (Fin 4),
      ∀ w : ↥G, (f (QuotientGroup.mk w)).IsSwap → orderOf w = 4 := by
  classical
  -- `|Z(SL₂)| = 2` from `p ≠ 2`
  have h2ne : (2 : F) ≠ 0 := by
    intro h2
    have hCharP2 : CharP F 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
    exact hp_ne_two (CharP.eq F (‹CharP F p› : CharP F p) hCharP2)
  haveI : NeZero (2 : F) := ⟨h2ne⟩
  have he2 : Nat.card (center SL(2,F)) = 2 := by
    rw [SpecialSubgroups.center_SL2_eq_Z]; exact SpecialSubgroups.card_Z_eq_two_of_two_ne_zero
  -- `z` is central, `|⟨z⟩| = 2`, `|G ⧸ ⟨z⟩| = 24`
  have hz_cen : z ∈ Subgroup.center ↥G := isCentral_of_unique_involution hz2 hz1 huniq
  have hzord : orderOf z = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime hz2 hz1
  have hzcard : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hzord]
  have hQ24 : Nat.card (↥G ⧸ Subgroup.zpowers z) = 24 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers z)
    rw [hcard48, hzcard] at h
    omega
  -- the two nonexistence hypotheses of the `S₄`-recognition module, from the class data
  have h3 : ∀ B : Subgroup (↥G ⧸ Subgroup.zpowers z), B.Normal → Nat.card B = 3 → False :=
    fun B hBnorm hB3 => caseVI_b_no_normal_card_three G center_le_G he2 hcard48 z hz2 hz1
      hz_cen Ab hAb_mem hAb6 B hBnorm hB3
  have h2 : ∀ u : ↥G ⧸ Subgroup.zpowers z, u ∈ Subgroup.center (↥G ⧸ Subgroup.zpowers z) →
      u ^ 2 = 1 → u = 1 :=
    caseVI_b_no_central_involution G center_le_G he2 hcard48 z hz2 hz1 huniq Ab hAb_mem hAb6
  obtain ⟨f⟩ := Ch7S4Recognition.mulEquiv_permFinFour_of_card_24 hQ24 h3 h2
  exact ⟨f, fun w hw => Ch7S4Recognition.orderOf_eq_four_of_isSwap hz2 hz1 huniq f w hw⟩

#print axioms scratch_caseVI_b_quotient_iso_S4
