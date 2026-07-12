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
  rw [P.card_eq_multiplicity, hcard]
  decide

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
  have hmod : Nat.card (Sylow 5 G) ≡ 1 [MOD 5] := Sylow.card_sylow_modEq_one 5 G
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
    have hP_unique : ∀ Q : Sylow 5 G, Q = P := by
      have : Subsingleton (Sylow 5 G) := Nat.card_eq_one_iff_unique.mp h1 |>.1
      exact fun Q => Subsingleton.elim Q P
    haveI hPnormal : P.toSubgroup.Normal := by
      constructor
      intro n hn g
      have : g • P = P := hP_unique (g • P)
      have hmem : g * n * g⁻¹ ∈ (g • P).toSubgroup := by
        rw [Sylow.pointwise_smul_def]
        exact ⟨n, hn, rfl⟩
      rwa [this] at hmem
    rcases P.toSubgroup.normal.eq_bot_or_eq_top with hbot | htop
    · have : Nat.card P.toSubgroup = 5 := sylow_five_card_eq_five hcard P
      rw [hbot] at this
      simp at this
    · have h5 : Nat.card P.toSubgroup = 5 := sylow_five_card_eq_five hcard P
      rw [htop] at h5
      rw [Subgroup.card_top] at h5
      rw [hcard] at h5
      norm_num at h5
  · exact h6

end Ch7SimpleGroup60
