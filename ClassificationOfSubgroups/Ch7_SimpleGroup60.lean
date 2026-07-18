import Mathlib

/-!
# Every simple group of order `60` is isomorphic to `A₅`

This file proves the classical theorem (Dummit–Foote §6.2, or Rotman's *Introduction to the
Theory of Groups* §5.4/§5.5): a finite simple group `G` of order `60` is isomorphic to the
alternating group `alternatingGroup (Fin 5)`.

It is **pure finite group theory** (no reference to `SL(2,F)`, `PGL`, or fields): it identifies
the abstract isomorphism type `A₅` needed to *recognize* the image of `SL(2,5)/{±1}` in Dickson's
classification, feeding case Vd/VIc (the Butler exposition) via
`Ch7_DicksonsClassificationTheorem.lean` (wired in separately by the orchestrator).

## Proof outline (standard, e.g. Dummit–Foote Prop. 6.2.13 / Rotman Thm 5.20)

1. `card_sylow_five_eq_six`: `G` has exactly `6` Sylow `5`-subgroups (Sylow's theorems rule out
   `n₅ = 1`, since a unique, hence normal, Sylow subgroup would contradict simplicity of a
   nonabelian group).
2. `G` acts (by conjugation) on its `6` Sylow `5`-subgroups; since the action is transitive
   (Sylow's second theorem) and nontrivial, and `G` is simple, the associated homomorphism
   `G →* Equiv.Perm (Fin 6)` (transporting the action along a chosen bijection with `Fin 6`) is
   injective (`toPermHom_sylow_injective`).
3. `range_le_alternatingGroup_of_isSimpleGroup`: composing an injective homomorphism from a
   simple group of order `> 2` into `Equiv.Perm (Fin n)` with the sign character forces the range
   into `alternatingGroup (Fin n)` (the sign character's kernel is normal, hence trivial or full;
   trivial is impossible since `Nat.card G > 2 = Nat.card ℤˣ`; so the character is trivial, i.e.
   every image element is even). This is stated once and reused for both `G` (into `A₆`) and,
   internally, for `A₆` itself (into `A₆` again, via its coset action on the resulting index-`6`
   subgroup).
4. Combining (2)–(3), `G` embeds into `alternatingGroup (Fin 6)` (order `360`) as a subgroup `H` of
   order `60`, i.e. of index `6`.
5. `isoAlternatingGroupFive_of_index_six`: any index-`6` subgroup of `alternatingGroup (Fin 6)` is
   isomorphic (as an abstract group) to `alternatingGroup (Fin 5)`. This is the crux of the
   theorem and is proved by *repeating steps 2–3 one level up*: `alternatingGroup (Fin 6)` acts
   faithfully (by the same simplicity argument, now applied to `alternatingGroup (Fin 6)` itself,
   which is simple since `5 ≤ Nat.card (Fin 6)`) on the `6` cosets of `H`, yielding (after the same
   sign trick) a *second* embedding `alternatingGroup (Fin 6) ↪ Equiv.Perm (Fin 6)` whose image,
   by a cardinality count, is all of `alternatingGroup (Fin 6)` again — i.e. an automorphism of
   `alternatingGroup (Fin 6)` under which `H` corresponds exactly to the stabilizer of a point of
   `Fin 6` (since `H` is literally the stabilizer of the trivial coset, `Subgroup.stabilizer_quotient`).
   Finally, the stabilizer of a point of the natural action of `alternatingGroup (Fin 6)` on `Fin 6`
   is isomorphic to `alternatingGroup (Fin 5)` (via `alternatingGroup.ofSubtype` applied to the
   complementary `5`-element `Finset`, whose range is exactly that stabilizer,
   `alternatingGroup.mem_range_ofSubtype_iff`).
6. `isSimpleGroup_card_sixty_iso_alternating`: combine (4) and (5).

## Divergences

None yet recorded against the Butler exposition: this file is *new* supporting group theory (a
classical fact used, but not itself proved, by Butler/Dickson), not a formalization of a specific
numbered lemma in the exposition. See `DIVERGENCES.md` for the project-wide convention.
-/

set_option linter.style.longLine true
set_option maxHeartbeats 400000

open Equiv Subgroup MulAction

namespace Ch7SimpleGroup60

/-! ### Step 3 (stated first, it is shared): a simple group embeds evenly -/

/-- If `G` is simple, `Nat.card G > 2`, and `φ : G →* Equiv.Perm (Fin n)` is injective, then the
image of `φ` consists only of even permutations. This is the standard "sign trick": composing
with `Equiv.Perm.sign` gives a homomorphism `G →* ℤˣ` whose kernel is normal, hence (`G` simple)
trivial or everything; trivial is impossible since `|G| > 2 = |ℤˣ|` would force `φ` (hence the
composite) to be injective into a group of order `2`. -/
theorem range_le_alternatingGroup_of_isSimpleGroup {G : Type*} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hG2 : 2 < Nat.card G) {n : ℕ} (φ : G →* Equiv.Perm (Fin n)) :
    φ.range ≤ alternatingGroup (Fin n) := by
  haveI := hs
  set χ : G →* ℤˣ := Equiv.Perm.sign.comp φ with hχ_def
  rcases (inferInstance : χ.ker.Normal).eq_bot_or_eq_top with hbot | htop
  · exfalso
    have hχinj : Function.Injective χ := by
      rw [← MonoidHom.ker_eq_bot_iff]; exact hbot
    have hle : Nat.card G ≤ Nat.card (ℤˣ : Type) := Nat.card_le_card_of_injective χ hχinj
    have hZ2 : Nat.card (ℤˣ : Type) = 2 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_units_int]
    omega
  · intro g hg
    obtain ⟨x, rfl⟩ := hg
    have hx : χ x = 1 := by
      have : x ∈ χ.ker := htop ▸ Subgroup.mem_top x
      simpa [MonoidHom.mem_ker] using this
    simpa [hχ_def, alternatingGroup, Equiv.Perm.mem_alternatingGroup] using hx

/-! ### Step 1: `G` has exactly `6` Sylow `5`-subgroups -/

instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

variable {G : Type*} [Group G] [Finite G]

/-- `Finite (Sylow 5 G)` always holds for a finite group: a Sylow subgroup of a finite group
automatically has finite index. -/
instance instFiniteSylowFive : Finite (Sylow 5 G) :=
  haveI : (Classical.arbitrary (Sylow 5 G)).toSubgroup.FiniteIndex := inferInstance
  Sylow.finite_of_finiteIndex (P := Classical.arbitrary (Sylow 5 G))

/-- A Sylow `5`-subgroup of a group of order `60` has order `5`. -/
theorem sylow_five_card_eq_five (hcard : Nat.card G = 60) (P : Sylow 5 G) :
    Nat.card P = 5 := by
  have hf : (60 : ℕ).factorization 5 = 1 := by
    rw [show (60 : ℕ) = 5 * 12 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [P.card_eq_multiplicity, hcard, hf, pow_one]

/-- The index of a Sylow `5`-subgroup of a group of order `60` is `12`. -/
theorem sylow_five_index_eq_twelve (hcard : Nat.card G = 60) (P : Sylow 5 G) :
    P.index = 12 := by
  have h5 := sylow_five_card_eq_five hcard P
  have := P.toSubgroup.card_mul_index
  rw [h5, hcard] at this
  omega

/-- The number `n₅` of Sylow `5`-subgroups of a group of order `60` is `1` or `6` (Sylow's third
theorem: `n₅ ≡ 1 (mod 5)` and `n₅ ∣ 12`). -/
theorem card_sylow_five_eq_one_or_six (hcard : Nat.card G = 60) :
    Nat.card (Sylow 5 G) = 1 ∨ Nat.card (Sylow 5 G) = 6 := by
  obtain P := Classical.arbitrary (Sylow 5 G)
  have hdvd : Nat.card (Sylow 5 G) ∣ 12 := (sylow_five_index_eq_twelve hcard P) ▸ P.card_dvd_index
  have hmod : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] := card_sylow_modEq_one 5 G
  have hpos : 0 < Nat.card (Sylow 5 G) := Nat.card_pos
  have hle : Nat.card (Sylow 5 G) ≤ 12 := Nat.le_of_dvd (by norm_num) hdvd
  unfold Nat.ModEq at hmod
  interval_cases (Nat.card (Sylow 5 G)) <;> omega

/-- If `G` is simple (in particular nonabelian, since `Nat.card G = 60 > 1`), it cannot have a
unique (hence normal) Sylow `5`-subgroup, so `n₅ = 6`. -/
theorem card_sylow_five_eq_six (hs : IsSimpleGroup G) (hcard : Nat.card G = 60) :
    Nat.card (Sylow 5 G) = 6 := by
  haveI := hs
  rcases card_sylow_five_eq_one_or_six hcard with h1 | h6
  · exfalso
    obtain P := Classical.arbitrary (Sylow 5 G)
    haveI : Subsingleton (Sylow 5 G) := Nat.card_eq_one_iff_unique.mp h1 |>.1
    have hPnormal : P.toSubgroup.Normal := Sylow.normal_of_subsingleton P
    rcases hPnormal.eq_bot_or_eq_top with hbot | htop
    · have h5 : Nat.card P.toSubgroup = 5 := sylow_five_card_eq_five hcard P
      rw [hbot] at h5
      simp at h5
    · have h5 : Nat.card P.toSubgroup = 5 := sylow_five_card_eq_five hcard P
      rw [htop, Subgroup.card_top, hcard] at h5
      norm_num at h5
  · exact h6

/-! ### Step 5: an index-`6` subgroup of `A₆` is isomorphic to `A₅`

The crux of the theorem. Given `H ≤ alternatingGroup (Fin 6)` (order `360`) of index `6`, the
coset action `alternatingGroup (Fin 6) →* Equiv.Perm (Fin 6)` (transported along a chosen bijection
`(alternatingGroup (Fin 6) ⧸ H) ≃ Fin 6`) is injective (its kernel is `H.normalCore`, which is
`⊥` since `A₆` is simple and `H ≠ ⊤`), and lands in `alternatingGroup (Fin 6)` by the shared sign
trick (step 3). The image of `H` under this embedding is the point-stabilizer of `e ⟦1⟧`, i.e. the
range of `alternatingGroup.ofSubtype {e ⟦1⟧}ᶜ` (even permutations fixing that point). A cardinality
count (`60 = 60`) shows the containment is an equality, so `H` is isomorphic to the range, which is
isomorphic to `alternatingGroup ↥{e ⟦1⟧}ᶜ ≃* alternatingGroup (Fin 5)` (a `5`-element index set). -/
noncomputable def isoAlternatingGroupFive_of_index_six
    (H : Subgroup (alternatingGroup (Fin 6))) (hH : H.index = 6) :
    ↥H ≃* alternatingGroup (Fin 5) := by
  classical
  haveI hAsimple : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  -- Cardinalities.
  have hcardA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; decide
  have hcardH : Nat.card ↥H = 60 := by
    have := Subgroup.card_mul_index H
    rw [hcardA, hH] at this; omega
  have hcardQ : Nat.card (alternatingGroup (Fin 6) ⧸ H) = 6 := by
    rw [← Subgroup.index_eq_card]; exact hH
  -- Faithfulness of the coset action: its kernel is `H.normalCore = ⊥`.
  have hker : (MulAction.toPermHom (alternatingGroup (Fin 6))
      (alternatingGroup (Fin 6) ⧸ H)).ker = ⊥ := by
    rw [← Subgroup.normalCore_eq_ker H]
    rcases (Subgroup.normalCore_normal H).eq_bot_or_eq_top with h | h
    · exact h
    · exfalso
      have hHtop : H = ⊤ := top_le_iff.mp (h ▸ H.normalCore_le)
      rw [hHtop, Subgroup.index_top] at hH
      exact absurd hH (by norm_num)
  have hφinj : Function.Injective (MulAction.toPermHom (alternatingGroup (Fin 6))
      (alternatingGroup (Fin 6) ⧸ H)) := (MonoidHom.ker_eq_bot_iff _).mp hker
  -- Transport the action to `Fin 6` via a chosen bijection `e`.
  haveI : Fintype (alternatingGroup (Fin 6) ⧸ H) := Fintype.ofFinite _
  let e : (alternatingGroup (Fin 6) ⧸ H) ≃ Fin 6 :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hcardQ)
  let φ' : alternatingGroup (Fin 6) →* Equiv.Perm (Fin 6) :=
    (e.permCongrHom.toMonoidHom).comp
      (MulAction.toPermHom (alternatingGroup (Fin 6)) (alternatingGroup (Fin 6) ⧸ H))
  have hφ'inj : Function.Injective φ' :=
    (EquivLike.injective e.permCongrHom).comp hφinj
  -- The sign trick (step 3): the image is even.
  have hrange : φ'.range ≤ alternatingGroup (Fin 6) :=
    range_le_alternatingGroup_of_isSimpleGroup hAsimple (by rw [hcardA]; norm_num) φ'
  have hmem : ∀ a, φ' a ∈ alternatingGroup (Fin 6) :=
    fun a => hrange (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  let ψ : alternatingGroup (Fin 6) →* alternatingGroup (Fin 6) :=
    φ'.codRestrict (alternatingGroup (Fin 6)) hmem
  have hψinj : Function.Injective ψ :=
    (MonoidHom.injective_codRestrict φ' (alternatingGroup (Fin 6)) hmem).mpr hφ'inj
  -- The stabilised point and the complementary `5`-element index set.
  set q₀ : alternatingGroup (Fin 6) ⧸ H :=
    ((1 : alternatingGroup (Fin 6)) : alternatingGroup (Fin 6) ⧸ H) with hq₀
  set p₀ : Fin 6 := e q₀ with hp₀
  set s : Finset (Fin 6) := {p₀}ᶜ with hs
  have hs5 : s.card = 5 := by
    rw [hs, Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
  -- The image of `H` lands in the point-stabilizer `range (ofSubtype s)`.
  have hmaple : H.map ψ ≤ (alternatingGroup.ofSubtype s).range := by
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨h, hh, rfl⟩ := hx
    have hs2 : h • q₀ = q₀ := by
      apply MulAction.mem_stabilizer_iff.mp
      rw [hq₀, MulAction.stabilizer_quotient]; exact hh
    have fixproof : (↑(ψ h) : Equiv.Perm (Fin 6)) p₀ = p₀ := by
      show (e.permCongr (MulAction.toPermHom (alternatingGroup (Fin 6))
          (alternatingGroup (Fin 6) ⧸ H) h)) p₀ = p₀
      rw [hp₀, Equiv.permCongr_apply, Equiv.symm_apply_apply,
        MulAction.toPermHom_apply, MulAction.toPerm_apply, hs2]
    rw [alternatingGroup.mem_range_ofSubtype_iff, hs]
    intro y hy
    rw [Finset.mem_compl, Finset.mem_singleton]
    rintro rfl
    exact (Equiv.Perm.mem_support.mp hy) fixproof
  -- The stabilizer has order `60`, hence the containment is an equality.
  have hcardT : Nat.card ↥(alternatingGroup.ofSubtype s).range = 60 := by
    haveI : Nontrivial ↥s :=
      Fintype.one_lt_card_iff_nontrivial.mp (by rw [Fintype.card_coe, hs5]; norm_num)
    rw [← Nat.card_congr
        (MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := s))).toEquiv,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_coe, hs5]; decide
  have hmap : H.map ψ = (alternatingGroup.ofSubtype s).range := by
    refine Subgroup.eq_of_le_of_card_ge hmaple (le_of_eq ?_)
    rw [hcardT, ← Nat.card_congr (H.equivMapOfInjective ψ hψinj).toEquiv, hcardH]
  -- Assemble the isomorphism.
  exact (H.equivMapOfInjective ψ hψinj).trans <|
    (MulEquiv.subgroupCongr hmap).trans <|
      (MonoidHom.ofInjective (alternatingGroup.ofSubtype_injective (s := s))).symm.trans <|
        Equiv.altCongrHom (Finset.equivFinOfCardEq hs5)

/-! ### Step 2: the conjugation action on the Sylow `5`-subgroups is faithful -/

/-- For a simple group `G` of order `60`, the conjugation action on its (six) Sylow `5`-subgroups
is faithful: `G →* Equiv.Perm (Sylow 5 G)` is injective. Its kernel is normal, hence (`G` simple)
`⊥` or `⊤`; `⊤` is impossible because the action is transitive (Sylow's second theorem) on a set
with `6 ≠ 1` elements. -/
theorem toPermHom_sylow_injective (hs : IsSimpleGroup G) (hcard : Nat.card G = 60) :
    Function.Injective (MulAction.toPermHom G (Sylow 5 G)) := by
  haveI := hs
  rw [← MonoidHom.ker_eq_bot_iff]
  rcases (inferInstance : (MulAction.toPermHom G (Sylow 5 G)).ker.Normal).eq_bot_or_eq_top with
    hbot | htop
  · exact hbot
  · exfalso
    have h6 : Nat.card (Sylow 5 G) = 6 := card_sylow_five_eq_six hs hcard
    have hsub : Subsingleton (Sylow 5 G) := by
      refine ⟨fun P Q => ?_⟩
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
      have hgker : g ∈ (MulAction.toPermHom G (Sylow 5 G)).ker := by
        rw [htop]; exact Subgroup.mem_top g
      have hg1 : (MulAction.toPermHom G (Sylow 5 G)) g = 1 := MonoidHom.mem_ker.mp hgker
      have hgP : g • P = P := by
        have := Equiv.Perm.ext_iff.mp hg1 P
        simpa [MulAction.toPermHom_apply, MulAction.toPerm_apply] using this
      rwa [hgP] at hg
    have hle := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega

/-! ### Step 6: the capstone -/

/-- **Every simple group of order `60` is isomorphic to `A₅`.** The group acts faithfully by
conjugation on its `6` Sylow `5`-subgroups (steps 1–2), giving (after the sign trick, step 3) an
embedding into `alternatingGroup (Fin 6)` whose image is a subgroup of index `6`, which is
isomorphic to `alternatingGroup (Fin 5)` (step 5). -/
theorem isSimpleGroup_card_sixty_iso_alternating (hs : IsSimpleGroup G) (hcard : Nat.card G = 60) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  haveI := hs
  have h6 : Nat.card (Sylow 5 G) = 6 := card_sylow_five_eq_six hs hcard
  haveI : Fintype (Sylow 5 G) := Fintype.ofFinite _
  -- Transport the (transitive, faithful) conjugation action to `Fin 6`.
  let e : Sylow 5 G ≃ Fin 6 :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact h6)
  let φ : G →* Equiv.Perm (Fin 6) :=
    (e.permCongrHom.toMonoidHom).comp (MulAction.toPermHom G (Sylow 5 G))
  have hφinj : Function.Injective φ :=
    (EquivLike.injective e.permCongrHom).comp (toPermHom_sylow_injective hs hcard)
  have hrange : φ.range ≤ alternatingGroup (Fin 6) :=
    range_le_alternatingGroup_of_isSimpleGroup hs (by rw [hcard]; norm_num) φ
  let ψ : G →* alternatingGroup (Fin 6) :=
    φ.codRestrict (alternatingGroup (Fin 6)) (fun a => hrange (MonoidHom.mem_range.mpr ⟨a, rfl⟩))
  have hψinj : Function.Injective ψ :=
    (MonoidHom.injective_codRestrict φ (alternatingGroup (Fin 6)) _).mpr hφinj
  -- The image is a subgroup of `A₆` of index `6`.
  have hHindex : ψ.range.index = 6 := by
    have hcardH : Nat.card ↥ψ.range = 60 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv]; exact hcard
    have hcardA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]; decide
    have := Subgroup.card_mul_index ψ.range
    rw [hcardH, hcardA] at this; omega
  -- Combine `G ≃* ψ.range` with step 5.
  exact ⟨(MonoidHom.ofInjective hψinj).trans
    (isoAlternatingGroupFive_of_index_six ψ.range hHindex)⟩

/-! ## A finite group of order `60` with a non-normal Sylow-5 subgroup is simple

This is the *pure group-theory* companion to `isSimpleGroup_card_sixty_iso_alternating`: it supplies
the hypothesis `IsSimpleGroup H` needed to recognise `H ⧸ Z(H)` in Case Vd of Dickson's
classification. The route (validated in Wave 21/22) replaces Butler's census (tex 2088–2102) by a
Sylow-counting argument: a normal subgroup of every possible order `{2,…,30}` is ruled out using a
unique Sylow-5 of a normal subgroup (`n5_eq_one_of_normal`), the preimage of a unique Sylow-5 of a
quotient (`preimage_sylow5`), and element counts at orders `12`, `30`. -/

instance fact_prime_two : Fact (Nat.Prime 2) := ⟨by norm_num⟩
instance fact_prime_three : Fact (Nat.Prime 3) := ⟨by norm_num⟩

set_option maxHeartbeats 1000000

/-! ### Sylow-5 counting machinery -/

lemma sylow5_card (H : Type*) [Group H] [Finite H] (P : Sylow 5 H) (m : ℕ)
    (hcard : Nat.card H = 5 * m) (hm : ¬ (5 ∣ m)) : Nat.card P.toSubgroup = 5 := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 5)
  have hfact : (Nat.card H).factorization 5 = 1 := by
    rw [hcard, Nat.factorization_mul (by norm_num) hm0, Finsupp.add_apply,
        Nat.Prime.factorization_self (by norm_num),
        Nat.factorization_eq_zero_of_not_dvd hm]
  rw [P.card_eq_multiplicity, hfact, pow_one]

lemma n5_dvd_modEq (H : Type*) [Group H] [Finite H] (m : ℕ)
    (hcard : Nat.card H = 5 * m) (hm : ¬ (5 ∣ m)) :
    Nat.card (Sylow 5 H) ∣ m ∧ Nat.card (Sylow 5 H) % 5 = 1 := by
  obtain P := Classical.arbitrary (Sylow 5 H)
  have hcardP := sylow5_card H P m hcard hm
  have hindex : P.index = m := by
    have h := P.toSubgroup.card_mul_index
    rw [hcardP, hcard] at h; omega
  refine ⟨hindex ▸ P.card_dvd_index, ?_⟩
  have hmod := card_sylow_modEq_one 5 H
  unfold Nat.ModEq at hmod; omega

lemma n5_eq_one (H : Type*) [Group H] [Finite H] (m : ℕ)
    (hcard : Nat.card H = 5 * m) (hm : ¬ (5 ∣ m)) (hmle : m ≤ 4) :
    Nat.card (Sylow 5 H) = 1 := by
  obtain ⟨hdvd, hmod⟩ := n5_dvd_modEq H m hcard hm
  have hle : Nat.card (Sylow 5 H) ≤ m := Nat.le_of_dvd (by omega) hdvd
  have hpos : 0 < Nat.card (Sylow 5 H) := Nat.card_pos
  omega

lemma n5_order30 (H : Type*) [Group H] [Finite H] (hcard : Nat.card H = 30) :
    Nat.card (Sylow 5 H) = 1 ∨ Nat.card (Sylow 5 H) = 6 := by
  obtain ⟨hdvd, hmod⟩ := n5_dvd_modEq H 6 (by omega) (by norm_num)
  have hle : Nat.card (Sylow 5 H) ≤ 6 := Nat.le_of_dvd (by omega) hdvd
  have hpos : 0 < Nat.card (Sylow 5 H) := Nat.card_pos
  omega

lemma normalSylow5_of {H : Type*} [Group H] [Finite H]
    (M : Subgroup H) [hMnorm : M.Normal] (hM1 : Nat.card (Sylow 5 M) = 1)
    (P : Sylow 5 H) (hPM : (P : Subgroup H) ≤ M) : (P : Subgroup H).Normal := by
  haveI : Subsingleton (Sylow 5 M) := Nat.card_eq_one_iff_unique.mp hM1 |>.1
  apply Subgroup.normalizer_eq_top_iff.mp
  rw [eq_top_iff]
  intro g _
  rw [P.coe_coe, ← Sylow.smul_eq_iff_mem_normalizer]
  have hgM : ((g • P : Sylow 5 H) : Subgroup H) ≤ M := by
    intro x hx
    have hx2 : x ∈ (↑(g • P) : Set H) := hx
    rw [Sylow.coe_smul] at hx2
    obtain ⟨y, hyP, rfl⟩ := hx2
    have hyM : y ∈ M := hPM hyP
    simpa using hMnorm.conj_mem y hyM g
  have hsub := Subsingleton.elim (P.subtype hPM) ((g • P).subtype hgM)
  exact (Sylow.subtype_injective hsub).symm

lemma n5_eq_one_of_normal {H : Type*} [Group H] [Finite H] (m : ℕ)
    (hcard : Nat.card H = 5 * m) (hm : ¬ (5 ∣ m))
    (M : Subgroup H) [M.Normal] (hM5 : 5 ∣ Nat.card M)
    (hM1 : Nat.card (Sylow 5 M) = 1) : Nat.card (Sylow 5 H) = 1 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) 5 hM5
  have hoy : orderOf (x : H) = 5 := (orderOf_coe x).trans hx
  have hzcard : Nat.card (Subgroup.zpowers (x : H)) = 5 := by
    rw [Nat.card_zpowers, hoy]
  have hzp : IsPGroup 5 (Subgroup.zpowers (x : H)) :=
    IsPGroup.of_card (n := 1) (by simpa using hzcard)
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup H) = 5 := sylow5_card H P m hcard hm
  have heqP : Subgroup.zpowers (x : H) = (P : Subgroup H) :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [hPcard, hzcard])
  have hPM : (P : Subgroup H) ≤ M := by
    rw [← heqP, Subgroup.zpowers_le]; exact SetLike.coe_mem x
  have hPnorm : (P : Subgroup H).Normal := normalSylow5_of M hM1 P hPM
  haveI := Sylow.unique_of_normal P hPnorm
  exact Nat.card_unique

lemma preimage_sylow5 {N : Type*} [Group N] [Finite N] (N₀ : Subgroup N) [N₀.Normal]
    (m' : ℕ) (hq : Nat.card (N ⧸ N₀) = 5 * m') (hm' : ¬ 5 ∣ m')
    (hu : Nat.card (Sylow 5 (N ⧸ N₀)) = 1) :
    ∃ M : Subgroup N, M.Normal ∧ Nat.card ↥M = 5 * Nat.card ↥N₀ := by
  classical
  haveI : Subsingleton (Sylow 5 (N ⧸ N₀)) := (Nat.card_eq_one_iff_unique.mp hu).1
  let P5 : Sylow 5 (N ⧸ N₀) := Classical.arbitrary _
  have hP5c : Nat.card (P5 : Subgroup (N ⧸ N₀)) = 5 := sylow5_card (N ⧸ N₀) P5 m' hq hm'
  haveI hP5n : (P5 : Subgroup (N ⧸ N₀)).Normal := Sylow.normal_of_subsingleton P5
  refine ⟨(P5 : Subgroup (N ⧸ N₀)).comap (QuotientGroup.mk' N₀), hP5n.comap _, ?_⟩
  set M := (P5 : Subgroup (N ⧸ N₀)).comap (QuotientGroup.mk' N₀) with hM
  have hsurj : Function.Surjective (QuotientGroup.mk' N₀) := QuotientGroup.mk'_surjective N₀
  have hiM : M.index = (P5 : Subgroup (N ⧸ N₀)).index :=
    Subgroup.index_comap_of_surjective _ hsurj
  have e1 : Nat.card ↥M * M.index = Nat.card N := Subgroup.card_mul_index M
  have e2 : 5 * (P5 : Subgroup (N ⧸ N₀)).index = Nat.card (N ⧸ N₀) := by
    have h := Subgroup.card_mul_index (P5 : Subgroup (N ⧸ N₀))
    rwa [hP5c] at h
  have e3 : Nat.card ↥N₀ * Nat.card (N ⧸ N₀) = Nat.card N := by
    have := Subgroup.card_mul_index N₀
    rwa [Subgroup.index_eq_card] at this
  have hipos : 0 < M.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
  have h2 : (5 * Nat.card ↥N₀) * M.index = Nat.card N := by
    rw [hiM]
    calc (5 * Nat.card ↥N₀) * (P5 : Subgroup (N ⧸ N₀)).index
        = Nat.card ↥N₀ * (5 * (P5 : Subgroup (N ⧸ N₀)).index) := by ring
      _ = Nat.card ↥N₀ * Nat.card (N ⧸ N₀) := by rw [e2]
      _ = Nat.card N := e3
  exact Nat.eq_of_mul_eq_mul_right hipos (e1.trans h2.symm)

/-! ### Element-count helpers (`#{x : orderOf x = r} = n_r · (r-1)` when `r ‖ |Q|`) -/

lemma inf_eq_bot_of_card_prime {Q : Type*} [Group Q] [Finite Q] {r : ℕ} (hp : r.Prime)
    (A B : Subgroup Q) (hA : Nat.card A = r) (hB : Nat.card B = r) (hAB : A ≠ B) :
    A ⊓ B = ⊥ := by
  have hdvd : Nat.card (A ⊓ B : Subgroup Q) ∣ r := by
    rw [← hA]; exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
  · exact Subgroup.card_eq_one.mp h1
  · exfalso; apply hAB
    have hAI : (A ⊓ B : Subgroup Q) = A := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left; rw [hp', hA]
    have hBI : (A ⊓ B : Subgroup Q) = B := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_right; rw [hp', hB]
    rw [← hAI, hBI]

lemma orderOf_eq_of_mem_card_prime {Q : Type*} [Group Q] {r : ℕ} [Fact r.Prime]
    {P : Subgroup Q} (hP : Nat.card P = r) {x : Q} (hx : x ∈ P) (hx1 : x ≠ 1) :
    orderOf x = r := by
  have hdvd : orderOf (⟨x, hx⟩ : P) ∣ r := hP ▸ orderOf_dvd_natCard _
  have hne : orderOf (⟨x, hx⟩ : P) ≠ 1 :=
    fun h => hx1 (Subtype.ext_iff.mp (orderOf_eq_one_iff.mp h))
  have hop : orderOf (⟨x, hx⟩ : P) = r := ((Nat.dvd_prime (Fact.out)).mp hdvd).resolve_left hne
  show orderOf ((⟨x, hx⟩ : P) : Q) = r
  rw [orderOf_coe]; exact hop

lemma card_orderOf_eq_prime {Q : Type*} [Group Q] [Fintype Q] {r : ℕ} [Fact r.Prime]
    (hmult : (Nat.card Q).factorization r = 1) :
    (Finset.univ.filter (fun x : Q => orderOf x = r)).card = Nat.card (Sylow r Q) * (r - 1) := by
  classical
  letI : Fintype (Sylow r Q) := Fintype.ofFinite _
  have hpp : r.Prime := Fact.out
  have hcardSyl : ∀ P : Sylow r Q, Nat.card (P : Subgroup Q) = r := by
    intro P; rw [P.card_eq_multiplicity, hmult, pow_one]
  set T : Sylow r Q → Finset Q :=
    fun P => Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q) ∧ orderOf x = r) with hT
  have hbi : Finset.univ.filter (fun x : Q => orderOf x = r) = Finset.univ.biUnion T := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, hT]
    constructor
    · intro hx
      have hzc : Nat.card (Subgroup.zpowers x) = r ^ (Nat.card Q).factorization r := by
        rw [Nat.card_zpowers, hx, hmult, pow_one]
      refine ⟨Sylow.ofCard (Subgroup.zpowers x) hzc, ?_, hx⟩
      rw [Sylow.coe_ofCard]; exact Subgroup.mem_zpowers x
    · rintro ⟨P, -, hxo⟩; exact hxo
  have hdisj : (↑(Finset.univ : Finset (Sylow r Q)) : Set (Sylow r Q)).PairwiseDisjoint T := by
    intro P _ P' _ hPP'
    rw [Function.onFun, Finset.disjoint_left]
    intro x hxP hxP'
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and] at hxP hxP'
    have hinf : (P : Subgroup Q) ⊓ (P' : Subgroup Q) = ⊥ :=
      inf_eq_bot_of_card_prime hpp _ _ (hcardSyl P) (hcardSyl P')
        (fun h => hPP' (Sylow.ext h))
    have hxmem : x ∈ (P : Subgroup Q) ⊓ (P' : Subgroup Q) := ⟨hxP.1, hxP'.1⟩
    rw [hinf, Subgroup.mem_bot] at hxmem
    rw [hxmem] at hxP
    simp only [orderOf_one, Subgroup.one_mem, true_and] at hxP
    exact absurd hxP.symm hpp.ne_one
  rw [hbi, Finset.card_biUnion hdisj]
  have hterm : ∀ P : Sylow r Q, (T P).card = r - 1 := by
    intro P
    have hTP : T P = (Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q))).filter (· ≠ 1) := by
      rw [hT]; ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hxP, hxo⟩
        exact ⟨hxP, fun h => by rw [h, orderOf_one] at hxo; exact hpp.ne_one hxo.symm⟩
      · rintro ⟨hxP, hx1⟩; exact ⟨hxP, orderOf_eq_of_mem_card_prime (hcardSyl P) hxP hx1⟩
    rw [hTP]
    have hmemcard : (Finset.univ.filter (fun x : Q => x ∈ (P : Subgroup Q))).card = r := by
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

/-! ### Order-30/order-12 lemmas, normal-Sylow extraction, and the assembly -/

/-- Generalized `normalSylow5_of` for arbitrary prime `p`. -/
lemma normalSylow_of {H : Type*} [Group H] [Finite H] (p : ℕ) [Fact p.Prime]
    (M : Subgroup H) [hMnorm : M.Normal] (hM1 : Nat.card (Sylow p M) = 1)
    (P : Sylow p H) (hPM : (P : Subgroup H) ≤ M) : (P : Subgroup H).Normal := by
  haveI : Subsingleton (Sylow p M) := Nat.card_eq_one_iff_unique.mp hM1 |>.1
  apply Subgroup.normalizer_eq_top_iff.mp
  rw [eq_top_iff]
  intro g _
  rw [P.coe_coe, ← Sylow.smul_eq_iff_mem_normalizer]
  have hgM : ((g • P : Sylow p H) : Subgroup H) ≤ M := by
    intro x hx
    have hx2 : x ∈ (↑(g • P) : Set H) := hx
    rw [Sylow.coe_smul] at hx2
    obtain ⟨y, hyP, rfl⟩ := hx2
    have hyM : y ∈ M := hPM hyP
    simpa using hMnorm.conj_mem y hyM g
  have hsub := Subsingleton.elim (P.subtype hPM) ((g • P).subtype hgM)
  exact (Sylow.subtype_injective hsub).symm

/-- If `N ⊴ H` has a unique Sylow-`p` and its `p`-part matches that of `H`, then `H` has a
Sylow-`p` inside `N`, and it is normal in `H`. -/
lemma exists_normal_sylow_le {H : Type*} [Group H] [Finite H] (p : ℕ) [Fact p.Prime]
    (N : Subgroup H) [N.Normal] (hN1 : Nat.card (Sylow p N) = 1)
    (hpart : (Nat.card N).factorization p = (Nat.card H).factorization p) :
    ∃ P : Sylow p H, (P : Subgroup H) ≤ N ∧ (P : Subgroup H).Normal := by
  classical
  haveI : Subsingleton (Sylow p N) := (Nat.card_eq_one_iff_unique.mp hN1).1
  let Q : Sylow p N := Classical.arbitrary _
  have hQcard : Nat.card (Q : Subgroup N) = p ^ (Nat.card N).factorization p :=
    Q.card_eq_multiplicity
  set QM : Subgroup H := (Q : Subgroup N).map N.subtype with hQMdef
  have hQM_le : QM ≤ N := Subgroup.map_subtype_le _
  have hQMcard : Nat.card QM = p ^ (Nat.card H).factorization p := by
    have e := (Q : Subgroup N).equivMapOfInjective N.subtype N.subtype_injective
    rw [hQMdef, ← Nat.card_congr e.toEquiv, hQcard, hpart]
  have hpg : IsPGroup p QM := IsPGroup.of_card hQMcard
  obtain ⟨P, hP⟩ := hpg.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup H) = p ^ (Nat.card H).factorization p :=
    P.card_eq_multiplicity
  have hEq : QM = (P : Subgroup H) := Subgroup.eq_of_le_of_card_ge hP (by rw [hPcard, hQMcard])
  have hPle : (P : Subgroup H) ≤ N := hEq ▸ hQM_le
  exact ⟨P, hPle, normalSylow_of p N hN1 P hPle⟩

/-- Key Lemma A: `|M| = 5 m`, `5 ∤ m`, `m ≤ 6` ⟹ unique Sylow-5. -/
lemma n5_eq_one_le30 (M : Type*) [Group M] [Finite M] (m : ℕ)
    (hcard : Nat.card M = 5 * m) (hm : ¬ 5 ∣ m) (hm6 : m ≤ 6) :
    Nat.card (Sylow 5 M) = 1 := by
  interval_cases m
  · exact absurd (dvd_zero 5) hm
  · exact n5_eq_one M 1 hcard hm (by norm_num)
  · exact n5_eq_one M 2 hcard hm (by norm_num)
  · exact n5_eq_one M 3 hcard hm (by norm_num)
  · exact n5_eq_one M 4 hcard hm (by norm_num)
  · exact absurd (by norm_num : (5 : ℕ) ∣ 5) hm
  · exact (n5_order30 M (by rw [hcard])).resolve_right (by
      intro h6
      -- order-30: rule out n₅ = 6 by element counting
      classical
      haveI : Fintype M := Fintype.ofFinite M
      have hcard30 : Nat.card M = 30 := by rw [hcard]
      have hf5 : (Nat.card M).factorization 5 = 1 := by
        rw [hcard30, show (30 : ℕ) = 5 * 6 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
          Nat.Prime.factorization_self (by norm_num),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      have hf3 : (Nat.card M).factorization 3 = 1 := by
        rw [hcard30, show (30 : ℕ) = 3 * 10 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
          Nat.Prime.factorization_self (by norm_num),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      obtain P3 := Classical.arbitrary (Sylow 3 M)
      have hc3P : Nat.card (P3 : Subgroup M) = 3 := by rw [P3.card_eq_multiplicity, hf3, pow_one]
      have hn3cases : Nat.card (Sylow 3 M) = 1 ∨ Nat.card (Sylow 3 M) = 10 := by
        have hidx : (P3 : Subgroup M).index = 10 := by
          have := P3.card_mul_index; rw [hc3P, hcard30] at this; omega
        have hdvd : Nat.card (Sylow 3 M) ∣ 10 := hidx ▸ P3.card_dvd_index
        have hmod : Nat.card (Sylow 3 M) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 M
        have hle : Nat.card (Sylow 3 M) ≤ 10 := Nat.le_of_dvd (by norm_num) hdvd
        have hpos : 0 < Nat.card (Sylow 3 M) := Nat.card_pos
        unfold Nat.ModEq at hmod; interval_cases (Nat.card (Sylow 3 M)) <;> omega
      have hcnt5 := card_orderOf_eq_prime (Q := M) (r := 5) hf5
      have hcnt3 := card_orderOf_eq_prime (Q := M) (r := 3) hf3
      rw [h6] at hcnt5
      have hn3 : Nat.card (Sylow 3 M) = 1 := by
        rcases hn3cases with h | h
        · exact h
        · exfalso
          rw [h] at hcnt3
          have hdisj : Disjoint (Finset.univ.filter (fun x : M => orderOf x = 5))
              (Finset.univ.filter (fun x : M => orderOf x = 3)) := by
            rw [Finset.disjoint_left]; intro x h5 h3
            simp only [Finset.mem_filter] at h5 h3; omega
          have hle : (Finset.univ.filter (fun x : M => orderOf x = 5) ∪
              Finset.univ.filter (fun x : M => orderOf x = 3)).card ≤ Fintype.card M :=
            Finset.card_le_univ _
          rw [Finset.card_union_of_disjoint hdisj, hcnt5, hcnt3, ← Nat.card_eq_fintype_card,
            hcard30] at hle
          omega
      -- n₃ = 1 → normal Sylow-3 → order-15 normal subgroup → n₅ = 1, contradiction
      haveI : Subsingleton (Sylow 3 M) := Nat.card_eq_one_iff_unique.mp hn3 |>.1
      haveI hP3norm : (P3 : Subgroup M).Normal := Sylow.normal_of_subsingleton P3
      have hquot : Nat.card (M ⧸ (P3 : Subgroup M)) = 5 * 2 := by
        have h := Subgroup.card_mul_index (P3 : Subgroup M)
        rw [hc3P, hcard30] at h
        rw [← Subgroup.index_eq_card]; omega
      have hu10 : Nat.card (Sylow 5 (M ⧸ (P3 : Subgroup M))) = 1 :=
        n5_eq_one (M ⧸ (P3 : Subgroup M)) 2 hquot (by norm_num) (by norm_num)
      obtain ⟨M15, hM15norm, hM15card⟩ :=
        preimage_sylow5 (P3 : Subgroup M) 2 hquot (by norm_num) hu10
      haveI := hM15norm
      rw [hc3P] at hM15card
      have hM155 : 5 ∣ Nat.card M15 := ⟨3, hM15card⟩
      have hM15n5 : Nat.card (Sylow 5 M15) = 1 :=
        n5_eq_one M15 3 hM15card (by norm_num) (by norm_num)
      have : Nat.card (Sylow 5 M) = 1 :=
        n5_eq_one_of_normal 6 hcard30 (by norm_num) M15 hM155 hM15n5
      omega)

/-- Order-12 lemma (b): `|N| = 12` ⟹ `N` has a unique Sylow-3 or a unique Sylow-2. -/
lemma n3_or_n2_order12 (N : Type*) [Group N] [Finite N] (hcard : Nat.card N = 12) :
    Nat.card (Sylow 3 N) = 1 ∨ Nat.card (Sylow 2 N) = 1 := by
  classical
  haveI : Fintype N := Fintype.ofFinite N
  have hf3 : (Nat.card N).factorization 3 = 1 := by
    rw [hcard, show (12 : ℕ) = 3 * 4 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
      Finsupp.add_apply, Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain P3 := Classical.arbitrary (Sylow 3 N)
  have hc3P : Nat.card (P3 : Subgroup N) = 3 := by rw [P3.card_eq_multiplicity, hf3, pow_one]
  have hn3cases : Nat.card (Sylow 3 N) = 1 ∨ Nat.card (Sylow 3 N) = 4 := by
    have hidx : (P3 : Subgroup N).index = 4 := by
      have := P3.card_mul_index; rw [hc3P, hcard] at this; omega
    have hdvd : Nat.card (Sylow 3 N) ∣ 4 := hidx ▸ P3.card_dvd_index
    have hmod : Nat.card (Sylow 3 N) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 N
    have hle : Nat.card (Sylow 3 N) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card (Sylow 3 N) := Nat.card_pos
    unfold Nat.ModEq at hmod; interval_cases (Nat.card (Sylow 3 N)) <;> omega
  rcases hn3cases with h1 | h4
  · exact Or.inl h1
  right
  have hcnt3 := card_orderOf_eq_prime (Q := N) (r := 3) hf3
  rw [h4] at hcnt3
  have hcompl : (Finset.univ.filter (fun x : N => orderOf x ≠ 3)).card ≤ 4 := by
    have hdisj : Disjoint (Finset.univ.filter (fun x : N => orderOf x ≠ 3))
        (Finset.univ.filter (fun x : N => orderOf x = 3)) := by
      rw [Finset.disjoint_left]; intro x ha hb
      simp only [Finset.mem_filter] at ha hb; exact ha.2 hb.2
    have hle : (Finset.univ.filter (fun x : N => orderOf x ≠ 3)
        ∪ Finset.univ.filter (fun x : N => orderOf x = 3)).card ≤ Fintype.card N :=
      Finset.card_le_univ _
    rw [Finset.card_union_of_disjoint hdisj, hcnt3, ← Nat.card_eq_fintype_card, hcard] at hle
    omega
  have hf2 : (Nat.card N).factorization 2 = 2 := by
    rw [hcard, show (12 : ℕ) = 2 ^ 2 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num), smul_eq_mul]
  have hc2P : ∀ P : Sylow 2 N, Nat.card (P : Subgroup N) = 4 := by
    intro P; rw [P.card_eq_multiplicity, hf2]; norm_num
  have hset : ∀ P : Sylow 2 N,
      Finset.univ.filter (fun x : N => x ∈ (P : Subgroup N))
        = Finset.univ.filter (fun x : N => orderOf x ≠ 3) := by
    intro P
    have hsub : Finset.univ.filter (fun x : N => x ∈ (P : Subgroup N))
        ⊆ Finset.univ.filter (fun x : N => orderOf x ≠ 3) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      have hdvd : orderOf x ∣ 4 := by
        have hd : orderOf (⟨x, hx⟩ : (P : Subgroup N)) ∣ 4 := by
          have := orderOf_dvd_natCard (⟨x, hx⟩ : (P : Subgroup N)); rwa [hc2P P] at this
        show orderOf ((⟨x, hx⟩ : (P : Subgroup N)) : N) ∣ 4
        rw [orderOf_coe]; exact hd
      intro h3; rw [h3] at hdvd; omega
    have hcardP : (Finset.univ.filter (fun x : N => x ∈ (P : Subgroup N))).card = 4 := by
      have h1 : (Finset.univ.filter (fun x : N => x ∈ (P : Subgroup N))).card
          = Nat.card (P : Subgroup N) := by
        rw [show (Finset.univ.filter (fun x : N => x ∈ (P : Subgroup N))).card
            = Fintype.card {x // x ∈ (P : Subgroup N)} from (Fintype.card_subtype _).symm,
          ← Nat.card_eq_fintype_card]
      rw [h1, hc2P P]
    exact Finset.eq_of_subset_of_card_le hsub (by rw [hcardP]; exact hcompl)
  haveI : Subsingleton (Sylow 2 N) := by
    refine ⟨fun P P' => Sylow.ext (SetLike.ext (fun x => ?_))⟩
    have hP := hset P; have hP' := hset P'
    constructor <;> intro hx
    · have : x ∈ Finset.univ.filter (fun y : N => y ∈ (P' : Subgroup N)) := by
        rw [hP', ← hP]; simp [hx]
      simpa using this
    · have : x ∈ Finset.univ.filter (fun y : N => y ∈ (P : Subgroup N)) := by
        rw [hP, ← hP']; simp [hx]
      simpa using this
  exact Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩

/-- Finisher for the `5 ∤ |N|` case: a normal `N` with `|N| = d0 ≤ 6` (`5 ∤ d0`, `d0 > 0`) and
`|H/N| = 5 m'` (`5 ∤ m'`, unique Sylow-5) forces `H` to have a unique Sylow-5 (via preimage). -/
lemma n5H_finish {H : Type*} [Group H] [Finite H] (hcard : Nat.card H = 60)
    (N : Subgroup H) [N.Normal] (m' d0 : ℕ)
    (hq : Nat.card (H ⧸ N) = 5 * m') (hm' : ¬ 5 ∣ m')
    (hu : Nat.card (Sylow 5 (H ⧸ N)) = 1)
    (hN : Nat.card N = d0) (hd0 : ¬ 5 ∣ d0) (hd0le : d0 ≤ 6) :
    Nat.card (Sylow 5 H) = 1 := by
  obtain ⟨M, hMnorm, hMcard⟩ := preimage_sylow5 N m' hq hm' hu
  haveI := hMnorm
  rw [hN] at hMcard
  have hM5 : 5 ∣ Nat.card M := ⟨d0, hMcard⟩
  have hMn5 : Nat.card (Sylow 5 M) = 1 := n5_eq_one_le30 M d0 hMcard hd0 hd0le
  exact n5_eq_one_of_normal 12 (by omega) (by norm_num) M hM5 hMn5

/-- Engine E2: normal `N` with `5 ∤ |N|`, `1 < |N| ≤ 6` ⟹ `H` has a unique Sylow-5. -/
lemma n5H_of_coprime_normal {H : Type*} [Group H] [Finite H] (hcard : Nat.card H = 60)
    (N : Subgroup H) [N.Normal] (hNcop : ¬ 5 ∣ Nat.card N)
    (hpos : 1 < Nat.card N) (hle : Nat.card N ≤ 6) :
    Nat.card (Sylow 5 H) = 1 := by
  have hidxmul : Nat.card N * N.index = 60 := by rw [← hcard]; exact Subgroup.card_mul_index N
  have hqi : Nat.card (H ⧸ N) = N.index := (Subgroup.index_eq_card N).symm
  have hcases : Nat.card N = 2 ∨ Nat.card N = 3 ∨ Nat.card N = 4 ∨ Nat.card N = 6 := by omega
  rcases hcases with h | h | h | h
  · have hidx : N.index = 30 := by rw [h] at hidxmul; omega
    have hq : Nat.card (H ⧸ N) = 5 * 6 := by rw [hqi, hidx]
    exact n5H_finish hcard N 6 2 hq (by norm_num)
      (n5_eq_one_le30 _ 6 hq (by norm_num) (by norm_num)) h (by omega) (by omega)
  · have hidx : N.index = 20 := by rw [h] at hidxmul; omega
    have hq : Nat.card (H ⧸ N) = 5 * 4 := by rw [hqi, hidx]
    exact n5H_finish hcard N 4 3 hq (by norm_num)
      (n5_eq_one_le30 _ 4 hq (by norm_num) (by norm_num)) h (by omega) (by omega)
  · have hidx : N.index = 15 := by rw [h] at hidxmul; omega
    have hq : Nat.card (H ⧸ N) = 5 * 3 := by rw [hqi, hidx]
    exact n5H_finish hcard N 3 4 hq (by norm_num)
      (n5_eq_one_le30 _ 3 hq (by norm_num) (by norm_num)) h (by omega) (by omega)
  · have hidx : N.index = 10 := by rw [h] at hidxmul; omega
    have hq : Nat.card (H ⧸ N) = 5 * 2 := by rw [hqi, hidx]
    exact n5H_finish hcard N 2 6 hq (by norm_num)
      (n5_eq_one_le30 _ 2 hq (by norm_num) (by norm_num)) h (by omega) (by omega)

/-- **Pure theorem**: a finite group of order `60` whose Sylow-5 subgroup is not normal
(`n₅ ≠ 1`) is simple. -/
theorem isSimpleGroup_of_card_60_of_sylow5_ne_one {H : Type*} [Group H] [Finite H]
    (hcard : Nat.card H = 60) (hn5 : Nat.card (Sylow 5 H) ≠ 1) : IsSimpleGroup H := by
  haveI : Nontrivial H := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]; norm_num
  refine ⟨fun N hNnorm => ?_⟩
  haveI := hNnorm
  by_contra hcon
  push_neg at hcon
  obtain ⟨hNbot, hNtop⟩ := hcon
  have hd_dvd : Nat.card N ∣ 60 := hcard ▸ Subgroup.card_subgroup_dvd_card N
  have hd_gt1 : 1 < Nat.card N := by
    rw [Finite.one_lt_card_iff_nontrivial]; exact (Subgroup.nontrivial_iff_ne_bot N).mpr hNbot
  have hd_lt : Nat.card N < 60 := by
    have hle60 : Nat.card N ≤ 60 := Nat.le_of_dvd (by norm_num) hd_dvd
    have hne : Nat.card N ≠ 60 := by
      intro he
      apply hNtop
      have hidxmul : Nat.card N * N.index = 60 := by rw [← hcard]; exact Subgroup.card_mul_index N
      rw [he] at hidxmul
      exact Subgroup.index_eq_one.mp (by omega)
    omega
  have henum : Nat.card N = 2 ∨ Nat.card N = 3 ∨ Nat.card N = 4 ∨ Nat.card N = 5 ∨ Nat.card N = 6
      ∨ Nat.card N = 10 ∨ Nat.card N = 12 ∨ Nat.card N = 15 ∨ Nat.card N = 20
      ∨ Nat.card N = 30 := by
    interval_cases (Nat.card N) <;> omega
  rcases henum with h | h | h | h | h | h | h | h | h | h
  -- |N| = 2, 3, 4, 6 : E2
  · exact hn5 (n5H_of_coprime_normal hcard N (by rw [h]; norm_num) (by omega) (by omega))
  · exact hn5 (n5H_of_coprime_normal hcard N (by rw [h]; norm_num) (by omega) (by omega))
  · exact hn5 (n5H_of_coprime_normal hcard N (by rw [h]; norm_num) (by omega) (by omega))
  -- |N| = 5 : E1
  · exact hn5 (n5_eq_one_of_normal 12 (by omega) (by norm_num) N (by rw [h])
      (n5_eq_one_le30 N 1 (by omega) (by norm_num) (by norm_num)))
  -- |N| = 6 : E2
  · exact hn5 (n5H_of_coprime_normal hcard N (by rw [h]; norm_num) (by omega) (by omega))
  -- |N| = 10 : E1
  · exact hn5 (n5_eq_one_of_normal 12 (by omega) (by norm_num) N (by rw [h]; norm_num)
      (n5_eq_one_le30 N 2 (by omega) (by norm_num) (by norm_num)))
  -- |N| = 12 : extract normal Sylow-3 or Sylow-2 of H, reduce to E2
  · rcases n3_or_n2_order12 N h with h3 | h2
    · have hpart : (Nat.card N).factorization 3 = (Nat.card H).factorization 3 := by
        rw [h, hcard]
        rw [show (12 : ℕ) = 3 * 4 by norm_num, show (60 : ℕ) = 3 * 20 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Finsupp.add_apply,
          Nat.Prime.factorization_self (by norm_num),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      obtain ⟨P, _, hPnorm⟩ := exists_normal_sylow_le 3 N h3 hpart
      haveI := hPnorm
      have hPcard : Nat.card (P : Subgroup H) = 3 := by
        rw [P.card_eq_multiplicity, ← hpart, h,
          show (12 : ℕ) = 3 * 4 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply, Nat.Prime.factorization_self (by norm_num),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num), pow_one]
      exact hn5 (n5H_of_coprime_normal hcard (P : Subgroup H) (by rw [hPcard]; norm_num)
        (by rw [hPcard]; norm_num) (by rw [hPcard]; norm_num))
    · have hpart : (Nat.card N).factorization 2 = (Nat.card H).factorization 2 := by
        rw [h, hcard]
        rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, show (60 : ℕ) = 2 ^ 2 * 15 by norm_num,
          Nat.factorization_mul (by norm_num) (by norm_num),
          Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply, Finsupp.add_apply,
          Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self (by norm_num),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      obtain ⟨P, _, hPnorm⟩ := exists_normal_sylow_le 2 N h2 hpart
      haveI := hPnorm
      have hPcard : Nat.card (P : Subgroup H) = 4 := by
        rw [P.card_eq_multiplicity, ← hpart, h,
          show (12 : ℕ) = 2 ^ 2 * 3 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
          Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply,
          Nat.Prime.factorization_self (by norm_num),
          Nat.factorization_eq_zero_of_not_dvd (by norm_num), smul_eq_mul]
        norm_num
      exact hn5 (n5H_of_coprime_normal hcard (P : Subgroup H) (by rw [hPcard]; norm_num)
        (by rw [hPcard]; norm_num) (by rw [hPcard]; norm_num))
  -- |N| = 15 : E1
  · exact hn5 (n5_eq_one_of_normal 12 (by omega) (by norm_num) N (by rw [h]; norm_num)
      (n5_eq_one_le30 N 3 (by omega) (by norm_num) (by norm_num)))
  -- |N| = 20 : E1
  · exact hn5 (n5_eq_one_of_normal 12 (by omega) (by norm_num) N (by rw [h]; norm_num)
      (n5_eq_one_le30 N 4 (by omega) (by norm_num) (by norm_num)))
  -- |N| = 30 : E1
  · exact hn5 (n5_eq_one_of_normal 12 (by omega) (by norm_num) N (by rw [h]; norm_num)
      (n5_eq_one_le30 N 6 (by omega) (by norm_num) (by norm_num)))


end Ch7SimpleGroup60
