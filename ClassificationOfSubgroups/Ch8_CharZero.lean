import ClassificationOfSubgroups.Ch7_DicksonsClassificationTheorem
import ClassificationOfSubgroups.Ch8_CharZeroEmbedding
-- WIRING (pending sibling): once `Ch8_CharZeroEmbedding.lean` (providing `klein_embed`) lands,
-- add `import ClassificationOfSubgroups.Ch8_CharZeroEmbedding` here and delete the local
-- `klein_embed` shim below (see the `KLEIN_EMBED SHIM` block).

/-!
# Klein's classification of finite subgroups of `SL₂` / `PGL₂` in characteristic zero

This module records **Klein's classical theorems** classifying the finite subgroups of
`SL(2, K)` and `PGL(2, K)` for an **algebraically closed field `K` of characteristic zero**
(e.g. `K = ℂ`). These are the characteristic-`0` analogues of Dickson's characteristic-`p`
theorems proven in `Ch7_DicksonsClassificationTheorem.lean`, and Klein's original list is the
source of the celebrated ADE / Platonic-solid correspondence:

* Every finite subgroup of `SL(2, ℂ)` is **cyclic**, a **binary dihedral (dicyclic /
  quaternion) group** `2D_n`, the **binary tetrahedral group** `SL(2,3) ≅ 2T`, the **binary
  octahedral group** `2O`, or the **binary icosahedral group** `SL(2,5) ≅ 2I`
  (`klein_classification_SL2_char_zero`).
* Every finite subgroup of `PGL(2, ℂ)` is **cyclic**, **dihedral** `D_n`, `A₄` (tetrahedral),
  `S₄` (octahedral), or `A₅` (icosahedral) (`klein_classification_PGL2_char_zero`).

## Method

Klein's theorems are *reduced* to Dickson's characteristic-`p` results. A finite subgroup `G` of
`SL(2, K)` embeds into `SL(2, F̄_ℓ)` for a suitable odd prime `ℓ` coprime to `|G|` — this is the
Minkowski/Brauer reduction supplied by the sibling embedding theorem `klein_embed`
(`Ch8_CharZeroEmbedding.lean`). Since `ℓ ∤ |G|` the image falls into **Dickson's Class I**, whose
*general* (center-free) form `dicksons_classification_theorem_class_I'` gives exactly the five
`SL₂`-types above; transporting back along the embedding proves the `SL₂` statement.

For `PGL₂` we mirror the descent architecture of
`FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod`: pull `G ≤ PGL(2, K)` back along
`SL(2, K) ↠ PGL(2, K)` to a finite subgroup `Ĝ` containing the center `{±1}` (the char-`0` copy
`klein_descent_setup` of `pgl_descent_setup`), apply the `SL₂` theorem above to `Ĝ`, then push each
of the five `SL₂`-types down through the order-`2` central quotient using the **field-generic**
descent lemmas already proven in the Dickson file (`pgl_descent_quaternion_quotient`,
`pgl_descent_SL2_ZMod3_quotient`, `pgl_descent_SL2_ZMod5_quotient`,
`pgl_descent_binaryOctahedral_quotient`, and the `pgl_descent_{ker_map_normal,ker_map_card,
quotient_transfer}` transfer chain): cyclic → cyclic, `2D_n` → `D_n`, `2T` → `A₄`, `2O` → `S₄`,
`2I` → `A₅`. Because `char K = 0`, no `ℓ`-divisible ("Class II") branch occurs, so the `PGL₂`
descent is strictly simpler than the finite-field case.
-/

open Matrix Subgroup Ch7GroupRecognition
open scoped MatrixGroups

/-! ### `SL₂` -/

/-- **Klein's theorem for `SL(2, K)`, `K` algebraically closed of characteristic `0`.** Every
finite subgroup `G ≤ SL(2, K)` is cyclic, a dicyclic (binary dihedral) group `QuaternionGroup n`,
the binary tetrahedral group `SL(2, ZMod 3) ≅ 2T`, the binary icosahedral group
`SL(2, ZMod 5) ≅ 2I`, or the binary octahedral group `2O` (`BinaryOctahedralGroup`).

Proof: the embedding `klein_embed` places `G` inside `SL(2, F̄_ℓ)` for an odd prime `ℓ ∤ |G|`;
`ℓ`-coprimality lands the image in Dickson's Class I, and the center-free form
`dicksons_classification_theorem_class_I'` yields the five types, transported back along the
embedding `G ≃* f.range`. -/
theorem klein_classification_SL2_char_zero {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (G : Subgroup SL(2, K)) [Finite G] :
    IsCyclic G ∨ (∃ n, Isomorphic G (QuaternionGroup n)) ∨
      Isomorphic G SL(2, ZMod 3) ∨ Isomorphic G SL(2, ZMod 5) ∨
      Isomorphic G Ch7GroupRecognition.BinaryOctahedralGroup := by
  obtain ⟨ℓ, _hfact, hℓ2, hcop, f, hf⟩ := CharZeroEmbedding.klein_embed G
  have hℓp : Nat.Prime ℓ := _hfact.out
  letI : DecidableEq (AlgebraicClosure (ZMod ℓ)) := Classical.decEq _
  -- The embedding as an isomorphism `G ≃* f.range`.
  let e : G ≃* f.range := MonoidHom.ofInjective hf
  haveI : Finite ↥(f.range) := Finite.of_equiv _ e.toEquiv
  -- `|f.range| = |G|` is coprime to `ℓ`, so we are in Class I.
  have hp' : ℓ = 0 ∨ Nat.Coprime (Nat.card ↥(f.range)) ℓ := by
    right; rw [← Nat.card_congr e.toEquiv]; exact hcop
  rcases dicksons_classification_theorem_class_I' hℓp.prime f.range hp' hℓ2 with
    hcyc | ⟨n, hquat⟩ | h23 | h25 | h2O
  · exact Or.inl ((MulEquiv.isCyclic e).mpr hcyc)
  · obtain ⟨e'⟩ := hquat; exact Or.inr (Or.inl ⟨n, ⟨e.trans e'⟩⟩)
  · obtain ⟨e'⟩ := h23; exact Or.inr (Or.inr (Or.inl ⟨e.trans e'⟩))
  · obtain ⟨e'⟩ := h25; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e.trans e'⟩)))
  · obtain ⟨e'⟩ := h2O; exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans e'⟩)))

/-! ### `PGL₂` -/

/-- Characteristic-`0` copy of `pgl_descent_setup`. The pullback of a finite `G ≤ PGL(2, K)`
along the surjection `SL(2, K) ↠ PGL(2, K)` is a finite subgroup `Ĝ ≤ SL(2, K)` containing the
center `{±1}`, together with a surjection `ψ : Ĝ ↠ G` whose kernel is the order-`2` center. The
proof is verbatim `pgl_descent_setup` with `AlgebraicClosure (ZMod p)` replaced by `K`; the only
input needed is `NeZero (2 : K)` (here from `CharZero K`) and `IsAlgClosed K` (for surjectivity
and the kernel computation of `SL_monoidHom_PGL`). -/
lemma klein_descent_setup {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (G : Subgroup (PGL (Fin 2) K)) [Finite G] :
    ∃ (Ghat : Subgroup SL(2, K)) (ψ : Ghat →* G),
      Finite Ghat ∧ center SL(2, K) ≤ Ghat ∧
        Function.Surjective ψ ∧ Nat.card ψ.ker = 2 := by
  haveI : NeZero (2 : K) := ⟨by norm_num⟩
  set φ : SL(2, K) →* PGL (Fin 2) K := SL_monoidHom_PGL (Fin 2) K with hφdef
  have hφ_surj : Function.Surjective φ := by
    intro x
    obtain ⟨y, hy⟩ := Surjective_PSL_monoidHom_PGL (Fin 2) K x
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact ⟨s, hy⟩
  have hφ_ker : φ.ker = center SL(2, K) := ker_SL_monoidHom_PGL_eq_center K (Fin 2) K
  have hker_le : φ.ker ≤ G.comap φ := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact G.one_mem
  have hZ_le : center SL(2, K) ≤ G.comap φ := hφ_ker ▸ hker_le
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

/-- **Klein's theorem for `PGL(2, K)`, `K` algebraically closed of characteristic `0`.** Every
finite subgroup `G ≤ PGL(2, K)` is cyclic, dihedral `DihedralGroup n`, `A₄`, `S₄`
(`Equiv.Perm (Fin 4)`), or `A₅`.

Proof: pull `G` back to a finite `Ĝ ≤ SL(2, K)` containing `{±1}` with `ψ : Ĝ ↠ G`, `|ker ψ| = 2`
(`klein_descent_setup`); classify `Ĝ` by `klein_classification_SL2_char_zero`; then push each
`SL₂`-type down the order-`2` central quotient (field-generic Dickson descent lemmas): cyclic →
cyclic, `2D_n` → `D_n`, `2T → A₄`, `2I → A₅`, `2O → S₄`. This is the Class I branch of
`FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod` — and in char `0` it is the only
branch. -/
theorem klein_classification_PGL2_char_zero {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (G : Subgroup (PGL (Fin 2) K)) [Finite G] :
    IsCyclic G ∨ (∃ n, Isomorphic G (DihedralGroup n)) ∨
      Isomorphic G (alternatingGroup (Fin 4)) ∨ Isomorphic G (Equiv.Perm (Fin 4)) ∨
      Isomorphic G (alternatingGroup (Fin 5)) := by
  obtain ⟨Ghat, ψ, hGhatFin, hZle, hψ_surj, hψ_ker_card⟩ := klein_descent_setup G
  haveI := hGhatFin
  rcases klein_classification_SL2_char_zero Ghat with
    hcyc | ⟨n, hquat⟩ | h23 | h25 | h2O
  · -- cyclic → cyclic
    exact Or.inl (isCyclic_of_surjective ψ hψ_surj)
  · -- dicyclic `2D_n` → dihedral `D_n`
    obtain ⟨e2⟩ := hquat
    haveI : NeZero n := ⟨by
      rintro rfl
      haveI : Finite (QuaternionGroup 0) := Finite.of_equiv _ e2.toEquiv
      haveI : Finite (DihedralGroup 0) := Finite.of_equiv _
        QuaternionGroup.quaternionGroupZeroEquivDihedralGroupZero.toEquiv
      exact not_finite (DihedralGroup 0)⟩
    haveI := pgl_descent_ker_map_normal ψ e2
    obtain ⟨e3⟩ := pgl_descent_quotient_transfer ψ hψ_surj e2
    obtain ⟨e4⟩ := pgl_descent_quaternion_quotient n _
      ((pgl_descent_ker_map_card ψ e2).trans hψ_ker_card)
    exact Or.inr (Or.inl ⟨n, ⟨e3.trans e4⟩⟩)
  · -- `2T = SL(2,3)` → `A₄`
    obtain ⟨e2⟩ := h23
    haveI := pgl_descent_ker_map_normal ψ e2
    obtain ⟨e3⟩ := pgl_descent_quotient_transfer ψ hψ_surj e2
    obtain ⟨e4⟩ := pgl_descent_SL2_ZMod3_quotient _
      ((pgl_descent_ker_map_card ψ e2).trans hψ_ker_card)
    exact Or.inr (Or.inr (Or.inl ⟨e3.trans e4⟩))
  · -- `2I = SL(2,5)` → `A₅`
    obtain ⟨e2⟩ := h25
    haveI := pgl_descent_ker_map_normal ψ e2
    obtain ⟨e3⟩ := pgl_descent_quotient_transfer ψ hψ_surj e2
    obtain ⟨e4⟩ := pgl_descent_SL2_ZMod5_quotient _
      ((pgl_descent_ker_map_card ψ e2).trans hψ_ker_card)
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e3.trans e4⟩)))
  · -- `2O` → `S₄`
    obtain ⟨e2⟩ := h2O
    haveI := pgl_descent_ker_map_normal ψ e2
    obtain ⟨e3⟩ := pgl_descent_quotient_transfer ψ hψ_surj e2
    obtain ⟨e4⟩ := pgl_descent_binaryOctahedral_quotient _
      ((pgl_descent_ker_map_card ψ e2).trans hψ_ker_card)
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e3.trans e4⟩)))
