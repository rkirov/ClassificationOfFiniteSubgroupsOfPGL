import Mathlib

/-!
# Every simple group of order `60` is isomorphic to `A₅`

This file proves the classical theorem (Dummit–Foote §6.2, or Rotman's *Introduction to the
Theory of Groups* §5.4/§5.5): a finite simple group `G` of order `60` is isomorphic to the
alternating group `alternatingGroup (Fin 5)`.

It is **pure finite group theory** (no reference to `SL(2,F)`, `PGL`, or fields): it identifies
the abstract isomorphism type `A₅` needed to *recognize* the image of `SL(2,5)/{±1}` in Dickson's
classification, feeding case Vd/VIc (`ChristopherButler.tex`) via
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

None yet recorded against `ChristopherButler.tex`: this file is *new* supporting group theory (a
classical fact used, but not itself proved, by Butler/Dickson), not a formalization of a specific
numbered lemma in the tex. See `DIVERGENCES.md` for the project-wide convention.
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

end Ch7SimpleGroup60
