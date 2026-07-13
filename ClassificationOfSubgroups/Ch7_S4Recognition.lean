import Mathlib

/-!
# Recognition of `S₄` among groups of order `24`

This file proves the pure group-theoretic recognition theorem needed by Case VIb of Dickson's
classification (`ChristopherButler.tex` ~2173-2201, via
`Ch7_DicksonsClassificationTheorem.lean`): a finite group `Q` of order `24` with

* no normal subgroup of order `3`, and
* no central involution

is isomorphic to `Equiv.Perm (Fin 4)`.

## Proof outline (standard Sylow counting)

1. `card_sylow_three_eq_one_or_four`: `n₃ ∈ {1, 4}` (Sylow: `n₃ ∣ 8`, `n₃ ≡ 1 [MOD 3]`).
   `n₃ = 1` would make the (order-`3`) Sylow-`3` normal, contradicting the first hypothesis,
   so `n₃ = 4`.
2. `Q` acts by conjugation on its `4` Sylow-`3`-subgroups; the kernel `K` of
   `Q →* Equiv.Perm (Sylow 3 Q)` normalizes every Sylow-`3`, so `|K| ∣ |N(P)| = 24 / 4 = 6`.
   If `3 ∣ |K|` then (`|K| ∈ {3, 6}` has a unique Sylow-`3`, `n3_eq_one_of_card_three_or_six`,
   and `K ⊴ Q`) `n₃(Q) = 1` (`n3_eq_one_of_normal`), contradiction; if `|K| = 2` then `K = ⟨u⟩`
   for a central involution `u`, contradiction. So `K = ⊥` and the action is faithful.
3. `|Q| = 24 = |S₄|` upgrades the injection to an isomorphism
   (`Nat.bijective_iff_injective_and_card`), transported to `Equiv.Perm (Fin 4)` along a chosen
   bijection `Sylow 3 Q ≃ Fin 4`.

The file also contains the generic central-extension half of Butler's `Ŝ₄` argument
(`orderOf_eq_four_of_isSwap`): if `Γ` has a *unique* involution `z` and
`f : Γ ⧸ ⟨z⟩ ≃* Equiv.Perm (Fin 4)`, then any `w` whose image under `f` is a transposition has
`orderOf w = 4` (its square lies in `⟨z⟩ \ {1}`), which is what distinguishes the binary
octahedral group `2O` from `GL(2,3)` among the two representation groups of `S₄`.

This file is deliberately `Mathlib`-only (mirroring `Ch7_SimpleGroup60.lean`): it identifies an
abstract isomorphism type, with no reference to `SL(2,F)`; the wiring into the Dickson file
supplies the two nonexistence hypotheses from Butler's maximal-abelian class data.

## Divergences

None recorded against `ChristopherButler.tex`: like `Ch7_SimpleGroup60.lean`, this is new
supporting group theory (Butler cites the recognition of `G/Z` as `S₄` and Suzuki's
classification of its representation groups without proof), not a formalization of a specific
numbered lemma. Butler's own route (the coset action on `N_G(A₂)/Z` of index `4`) is replaced
by the conjugation action on the four Sylow-`3`-subgroups, which needs strictly less of the
class data; see `DIVERGENCES.md` for the project-wide convention.
-/

set_option linter.style.longLine true
set_option maxHeartbeats 400000

open Equiv Subgroup MulAction

namespace Ch7S4Recognition

/-! ### Generic helpers: involutions and central extensions by `⟨z⟩` -/

/-- Every element of `⟨z⟩` for an involution `z` (`z² = 1`) is `1` or `z`: split the exponent
`k = 2 * (k / 2) + k % 2` and kill the even part with `z² = 1`. -/
lemma mem_zpowers_involution {Γ : Type*} [Group Γ] {z : Γ} (hz2 : z ^ 2 = 1) :
    ∀ w : Γ, w ∈ Subgroup.zpowers z → w = 1 ∨ w = z := by
  intro w hw
  obtain ⟨k, hk⟩ := hw
  have hk' : z ^ k = w := hk
  have hz2' : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hz2]
  have hdecomp : z ^ k = z ^ (k % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 2]
    rw [zpow_add, zpow_mul, hz2', one_zpow, one_mul]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [← hk', hdecomp, h, zpow_zero]
  · right; rw [← hk', hdecomp, h, zpow_one]

/-- An element squaring to an involution `z ≠ 1` has order exactly `4`. -/
lemma orderOf_eq_four_of_sq_eq_involution {Γ : Type*} [Group Γ] {z : Γ} (hz2 : z ^ 2 = 1)
    (hz1 : z ≠ 1) {w : Γ} (hw2 : w ^ 2 = z) : orderOf w = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ w ^ (2 : ℕ) ^ 1 = 1 := by rw [pow_one, hw2]; exact hz1
  have hfin : w ^ (2 : ℕ) ^ 2 = 1 := by
    rw [show ((2 : ℕ) ^ 2) = 2 * 2 by norm_num, pow_mul, hw2, hz2]
  have h := orderOf_eq_prime_pow hnot hfin
  rw [h]; norm_num

/-- **Unique-involution lift**: if `z` is the unique involution of `Γ` and `w` maps to a
nontrivial element of order dividing `2` in `Γ ⧸ ⟨z⟩`, then `orderOf w = 4` (its square must be
`z` itself). This is the generic core of Butler's `Ŝ₄`-vs-`GL(2,3)` distinction. -/
theorem orderOf_eq_four_of_mk_sq {Γ : Type*} [Group Γ] {z : Γ} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (huniq : ∀ g : Γ, g ^ 2 = 1 → g ≠ 1 → g = z) [hN : (Subgroup.zpowers z).Normal] {w : Γ}
    (h1 : (QuotientGroup.mk w : Γ ⧸ Subgroup.zpowers z) ≠ 1)
    (hsq : (QuotientGroup.mk w : Γ ⧸ Subgroup.zpowers z) ^ 2 = 1) :
    orderOf w = 4 := by
  have hmem : w ^ 2 ∈ Subgroup.zpowers z := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hsq
  rcases mem_zpowers_involution hz2 _ hmem with h | h
  · exfalso
    rcases eq_or_ne w 1 with rfl | hw1
    · exact h1 rfl
    · have hwz : w = z := huniq w h hw1
      exact h1 ((QuotientGroup.eq_one_iff w).mpr (hwz ▸ Subgroup.mem_zpowers w))
  · exact orderOf_eq_four_of_sq_eq_involution hz2 hz1 h

/-- The transposition-lift half of Case VIb: with `z` the unique involution of `Γ` and
`f : Γ ⧸ ⟨z⟩ ≃* S₄`, every `w` mapping to a transposition has order `4`. -/
theorem orderOf_eq_four_of_isSwap {Γ : Type*} [Group Γ] {z : Γ} (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1)
    (huniq : ∀ g : Γ, g ^ 2 = 1 → g ≠ 1 → g = z) [hN : (Subgroup.zpowers z).Normal]
    (f : (Γ ⧸ Subgroup.zpowers z) ≃* Equiv.Perm (Fin 4)) (w : Γ)
    (hsw : (f (QuotientGroup.mk w)).IsSwap) : orderOf w = 4 := by
  obtain ⟨x, y, hxy, hfw⟩ := hsw
  have hne : f (QuotientGroup.mk w) ≠ 1 := by
    rw [hfw]
    intro h
    have hx : Equiv.swap x y x = (1 : Equiv.Perm (Fin 4)) x := by rw [h]
    rw [Equiv.swap_apply_left, Equiv.Perm.one_apply] at hx
    exact hxy hx.symm
  have hsq : f (QuotientGroup.mk w) ^ 2 = 1 := by rw [hfw, sq, Equiv.swap_mul_self]
  have h1 : (QuotientGroup.mk w : Γ ⧸ Subgroup.zpowers z) ≠ 1 := by
    intro h
    exact hne (by rw [h, map_one])
  have h2 : (QuotientGroup.mk w : Γ ⧸ Subgroup.zpowers z) ^ 2 = 1 := by
    apply f.injective
    rw [map_pow, map_one, hsq]
  exact orderOf_eq_four_of_mk_sq hz2 hz1 huniq h1 h2

/-! ### Sylow-`3` counting in a group of order `24` -/

variable {Q : Type*} [Group Q] [Finite Q]

/-- `Finite (Sylow 3 Q)` always holds for a finite group (cf. `Ch7SimpleGroup60`'s
`instFiniteSylowFive`). -/
instance instFiniteSylowThree : Finite (Sylow 3 Q) :=
  haveI : (Classical.arbitrary (Sylow 3 Q)).toSubgroup.FiniteIndex := inferInstance
  Sylow.finite_of_finiteIndex (P := Classical.arbitrary (Sylow 3 Q))

/-- A Sylow `3`-subgroup of a group of order `24` has order `3`. -/
theorem sylow_three_card (hcard : Nat.card Q = 24) (P : Sylow 3 Q) :
    Nat.card P = 3 := by
  have hf : (24 : ℕ).factorization 3 = 1 := by
    rw [show (24 : ℕ) = 3 * 8 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_self (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [P.card_eq_multiplicity, hcard, hf, pow_one]

/-- The index of a Sylow `3`-subgroup of a group of order `24` is `8`. -/
theorem sylow_three_index (hcard : Nat.card Q = 24) (P : Sylow 3 Q) :
    (P : Subgroup Q).index = 8 := by
  have h3 := sylow_three_card hcard P
  have h := (P : Subgroup Q).card_mul_index
  rw [h3, hcard] at h
  omega

/-- Sylow's third theorem at `|Q| = 24`: `n₃ ∣ 8` and `n₃ ≡ 1 [MOD 3]`, so `n₃ ∈ {1, 4}`. -/
theorem card_sylow_three_eq_one_or_four (hcard : Nat.card Q = 24) :
    Nat.card (Sylow 3 Q) = 1 ∨ Nat.card (Sylow 3 Q) = 4 := by
  obtain P := Classical.arbitrary (Sylow 3 Q)
  have hdvd : Nat.card (Sylow 3 Q) ∣ 8 := (sylow_three_index hcard P) ▸ P.card_dvd_index
  have hmod : Nat.card (Sylow 3 Q) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 Q
  have hpos : 0 < Nat.card (Sylow 3 Q) := Nat.card_pos
  have hle : Nat.card (Sylow 3 Q) ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  unfold Nat.ModEq at hmod
  interval_cases (Nat.card (Sylow 3 Q)) <;> omega

/-- A Sylow `p`-subgroup of a finite group contained in a normal subgroup with a *unique*
Sylow `p`-subgroup is itself normal (cf. `Ch7SimpleGroup60.normalSylow_of`). -/
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

/-- A group whose order is `3` or `6` has a unique Sylow `3`-subgroup (`n₃ ∣ 2` and
`n₃ ≡ 1 [MOD 3]`). -/
lemma n3_eq_one_of_card_three_or_six {M : Type*} [Group M] [Finite M]
    (h : Nat.card M = 3 ∨ Nat.card M = 6) : Nat.card (Sylow 3 M) = 1 := by
  have hf : (Nat.card M).factorization 3 = 1 := by
    rcases h with h | h <;> rw [h]
    · exact Nat.Prime.factorization_self (by norm_num)
    · rw [show (6 : ℕ) = 3 * 2 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_self (by norm_num),
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  obtain P := Classical.arbitrary (Sylow 3 M)
  have hcardP : Nat.card (P : Subgroup M) = 3 := by
    rw [P.card_eq_multiplicity, hf, pow_one]
  have hidx : (P : Subgroup M).index ≤ 2 := by
    have hmul := (P : Subgroup M).card_mul_index
    rcases h with h | h <;> rw [hcardP, h] at hmul <;> omega
  have hdvd : Nat.card (Sylow 3 M) ∣ (P : Subgroup M).index := P.card_dvd_index
  have hipos : 0 < (P : Subgroup M).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle : Nat.card (Sylow 3 M) ≤ 2 := le_trans (Nat.le_of_dvd hipos hdvd) hidx
  have hmod : Nat.card (Sylow 3 M) ≡ 1 [MOD 3] := card_sylow_modEq_one 3 M
  have hpos : 0 < Nat.card (Sylow 3 M) := Nat.card_pos
  unfold Nat.ModEq at hmod
  omega

/-- If a normal subgroup `M ⊴ Q` (with `|Q| = 24`) has `3 ∣ |M|` and a unique Sylow-`3`, then
`Q` itself has a unique Sylow-`3` (cf. `Ch7SimpleGroup60.n5_eq_one_of_normal`). -/
lemma n3_eq_one_of_normal (hcard : Nat.card Q = 24) (M : Subgroup Q) [M.Normal]
    (hM3 : 3 ∣ Nat.card M) (hM1 : Nat.card (Sylow 3 M) = 1) :
    Nat.card (Sylow 3 Q) = 1 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := M) 3 hM3
  have hoy : orderOf (x : Q) = 3 := (orderOf_coe x).trans hx
  have hzcard : Nat.card (Subgroup.zpowers (x : Q)) = 3 := by rw [Nat.card_zpowers, hoy]
  have hzp : IsPGroup 3 (Subgroup.zpowers (x : Q)) :=
    IsPGroup.of_card (n := 1) (by simpa using hzcard)
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  have hPcard : Nat.card (P : Subgroup Q) = 3 := sylow_three_card hcard P
  have heqP : Subgroup.zpowers (x : Q) = (P : Subgroup Q) :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [hPcard, hzcard])
  have hPM : (P : Subgroup Q) ≤ M := by
    rw [← heqP, Subgroup.zpowers_le]; exact SetLike.coe_mem x
  have hPnorm : (P : Subgroup Q).Normal := normalSylow_of 3 M hM1 P hPM
  haveI := Sylow.unique_of_normal P hPnorm
  exact Nat.card_unique

/-! ### The recognition theorem -/

/-- **Recognition of `S₄`**: a finite group of order `24` with no normal subgroup of order `3`
and no central involution is isomorphic to `Equiv.Perm (Fin 4)`, via the conjugation action on
its four Sylow-`3`-subgroups. -/
theorem mulEquiv_permFinFour_of_card_24 (hcard : Nat.card Q = 24)
    (h3 : ∀ B : Subgroup Q, B.Normal → Nat.card B = 3 → False)
    (h2 : ∀ u : Q, u ∈ Subgroup.center Q → u ^ 2 = 1 → u = 1) :
    Nonempty (Q ≃* Equiv.Perm (Fin 4)) := by
  classical
  -- Step 1: `n₃ = 4`.
  have hn4 : Nat.card (Sylow 3 Q) = 4 := by
    rcases card_sylow_three_eq_one_or_four hcard with h1 | h4
    · exfalso
      obtain P := Classical.arbitrary (Sylow 3 Q)
      haveI : Subsingleton (Sylow 3 Q) := Nat.card_eq_one_iff_unique.mp h1 |>.1
      exact h3 (P : Subgroup Q) (Sylow.normal_of_subsingleton P) (sylow_three_card hcard P)
    · exact h4
  -- Step 2: the kernel `K` of the conjugation action normalizes every Sylow-`3`.
  obtain P₀ := Classical.arbitrary (Sylow 3 Q)
  have hKle : (MulAction.toPermHom Q (Sylow 3 Q)).ker ≤ normalizer (P₀ : Set Q) := by
    intro k hk
    have hk1 : MulAction.toPermHom Q (Sylow 3 Q) k = 1 := MonoidHom.mem_ker.mp hk
    have hkP : k • P₀ = P₀ := by
      have h := Equiv.Perm.ext_iff.mp hk1 P₀
      simpa [MulAction.toPermHom_apply, MulAction.toPerm_apply] using h
    exact Sylow.smul_eq_iff_mem_normalizer.mp hkP
  -- `|N(P₀)| = 6`.
  have hNidx : (normalizer (P₀ : Set Q)).index = 4 := by
    rw [← Sylow.card_eq_index_normalizer]; exact hn4
  have hNcard : Nat.card (normalizer (P₀ : Set Q)) = 6 := by
    have h := (normalizer (P₀ : Set Q)).card_mul_index
    rw [hNidx, hcard] at h
    omega
  have hKdvd : Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker ∣ 6 := by
    have h := Subgroup.card_dvd_of_le hKle
    rwa [hNcard] at h
  -- `3 ∤ |K|` (else `Q` would have a unique Sylow-`3`).
  have hK3 : ¬ (3 ∣ Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker) := by
    intro hdvd
    have h36 : Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker = 3 ∨
        Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker = 6 := by
      have hpos : 0 < Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker := Nat.card_pos
      have hle : Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker ≤ 6 :=
        Nat.le_of_dvd (by norm_num) hKdvd
      interval_cases (Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker) <;> omega
    have hn1 : Nat.card (Sylow 3 Q) = 1 :=
      n3_eq_one_of_normal hcard _ hdvd (n3_eq_one_of_card_three_or_six h36)
    omega
  -- `|K| ≠ 2` (else `K = ⟨u⟩` for a central involution `u`).
  have hK2 : Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker ≠ 2 := by
    intro h2K
    have hex : ∃ u : Q, u ∈ (MulAction.toPermHom Q (Sylow 3 Q)).ker ∧ u ≠ 1 := by
      haveI : Nontrivial (MulAction.toPermHom Q (Sylow 3 Q)).ker :=
        Finite.one_lt_card_iff_nontrivial.mp (by omega)
      obtain ⟨u₀, hu₀⟩ := exists_ne (1 : (MulAction.toPermHom Q (Sylow 3 Q)).ker)
      exact ⟨(u₀ : Q), u₀.2, fun h => hu₀ (OneMemClass.coe_eq_one.mp h)⟩
    obtain ⟨u, huK, hune⟩ := hex
    have huord : orderOf u = 2 := by
      have hdvd : orderOf u ∣ 2 := by
        rw [← h2K]
        have h := orderOf_dvd_natCard (⟨u, huK⟩ : (MulAction.toPermHom Q (Sylow 3 Q)).ker)
        rwa [orderOf_mk] at h
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hune
      · exact h
    have husq : u ^ 2 = 1 := by rw [← huord]; exact pow_orderOf_eq_one _
    have hzpow : Subgroup.zpowers u = (MulAction.toPermHom Q (Sylow 3 Q)).ker := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr huK)
      rw [Nat.card_zpowers, huord, h2K]
    have hucen : u ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hconj : g * u * g⁻¹ ∈ Subgroup.zpowers u := by
        rw [hzpow]
        exact (MulAction.toPermHom Q (Sylow 3 Q)).normal_ker.conj_mem _ huK g
      rcases mem_zpowers_involution husq _ hconj with hc | hc
      · exfalso
        apply hune
        have h1 : g * u = g := by
          calc g * u = g * u * g⁻¹ * g := by group
            _ = 1 * g := by rw [hc]
            _ = g := one_mul g
        calc u = g⁻¹ * (g * u) := by group
          _ = g⁻¹ * g := by rw [h1]
          _ = 1 := by group
      · calc g * u = g * u * g⁻¹ * g := by group
          _ = u * g := by rw [hc]
    exact hune (h2 _ hucen husq)
  -- Step 3: `K = ⊥`, so the action is faithful, and cardinality upgrades it to an isomorphism.
  have hK1 : Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker = 1 := by
    have hpos : 0 < Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker := Nat.card_pos
    have hle : Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker ≤ 6 :=
      Nat.le_of_dvd (by norm_num) hKdvd
    interval_cases (Nat.card (MulAction.toPermHom Q (Sylow 3 Q)).ker) <;> omega
  have hinj : Function.Injective (MulAction.toPermHom Q (Sylow 3 Q)) :=
    (MonoidHom.ker_eq_bot_iff _).mp (Subgroup.card_eq_one.mp hK1)
  have hcardPerm : Nat.card (Equiv.Perm (Sylow 3 Q)) = 24 := by
    rw [Nat.card_perm, hn4]
    norm_num [Nat.factorial]
  have hbij : Function.Bijective (MulAction.toPermHom Q (Sylow 3 Q)) := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨hinj, by rw [hcard, hcardPerm]⟩
  haveI : Fintype (Sylow 3 Q) := Fintype.ofFinite _
  let e : Sylow 3 Q ≃ Fin 4 :=
    Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact hn4)
  exact ⟨(MulEquiv.ofBijective _ hbij).trans e.permCongrHom⟩

end Ch7S4Recognition
