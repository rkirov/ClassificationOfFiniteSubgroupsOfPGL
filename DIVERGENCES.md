# Divergences from Butler's exposition

This formalization targets the **classical Dickson classification** (finite subgroups of
SL(2,F̄_p) / PGL(2,F̄_p)). Where the Lean development diverges from Christopher Butler's
exposition (`ChristopherButler.tex`, cited by tex line numbers), the divergence is recorded
here and in the corresponding docstrings.

## Statement-level divergences

1. **Thm 6.8(iv) trivial case / `p = 2`** (tex 838; `S2_A: eq_center_of_card_le_two`).
   The intermediate claim "a maximal abelian subgroup of order ≤ 2 is central", factored
   out *without* Butler's standing coprimality hypothesis, is **false in char 2**
   (unipotent involutions are non-central; counterexample recorded by the original
   authors in S2_A ~line 338). **RESOLVED — Butler's theorem is vindicated**: under
   his own coprimality hypothesis the counterexample is excluded (its order is 2,
   not coprime to p = 2), and the char-2 case is now formally proven:
   `S2_B: of_index_normalizer_eq_two_char_two` (+ the two char-2 helper analogues),
   sorry-free. The `p ≠ 2` variants remain for the odd-characteristic route; the
   original gap-note applies only to the over-general Lean helper, not to the paper.
   **`Ch7: case_IV` now unblocked**: Case IVa (`p = 2`, dihedral) previously stopped
   short of the final group-recognition step because it needed exactly this char-2
   inverting-element fact; it is now wired in (`of_index_normalizer_eq_two_char_two`),
   and Case IVa is PROVED in full (Case IVb, `p = 3`, remains sorried separately —
   it needs the unrelated "analogous to Case IIb" `SL(2,3)`-construction, itself
   sorried in `case_II`'s `g1 = 3` branch).

2. **Case (0,3) arithmetic** (tex 2115-2160; `S4_CaseArithmetic.case_0_3`).
   Butler's displayed equation for Case VI does **not** determine `k` (the `(q-1)`
   factor vanishes identically at `q = 1`). The formalized lemma concludes only
   `q = 1`, which is all Butler's downstream argument uses. His conclusions are
   unaffected; only the implicit "and k = 1" reading is dropped.

3. **Ŝ₄ rendering** (tex 2121-2125, 2200, 2221; `Ch7` final theorems). Butler:
   Ŝ₄ = the representation group of S₄ in which transpositions lift to order-4
   elements (= the **binary octahedral group 2O**), citing Suzuki for the fact that
   S₄ has exactly two such covers. A formalization draft incorrectly rendered this
   as `GL (Fin 2) (ZMod 3)` — which is the *other* cover (transpositions lift to
   involutions; it has non-central involutions, so it cannot embed in SL(2,F) for
   p ≠ 2). **FIXED**: `Ch7_DicksonsClassificationTheorem.lean` now defines
   `BinaryOctahedralGroup` as the presented group `⟨x, y | x⁴ = y³ = (xy)²⟩`
   (the `⟨4,3,2⟩` binary polyhedral/von Dyck presentation of `2O`, order 48) and
   uses it in place of `GL (Fin 2) (ZMod 3)` in `case_VI`'s Case VIb disjunct and
   in `dicksons_classification_theorem_class_I`'s final disjunct. The *proofs* of
   those disjuncts (identifying an actual `G` with `BinaryOctahedralGroup`) remain
   sorried — this fix is statement-level only (matching item 3's original scope:
   picking the *correct type* for the disjunct), not a new recognition lemma.
   This is a formalization erratum, not Butler's.

## Proof-route divergences (statements faithful, proofs different)

4. **Thm 6.8(v-a) complement construction** (tex 899-948; `S2_B`).
   Butler constructs K = ⟨kᵖ⟩ from a generator of the cyclic quotient. The
   formalization instead obtains K by **Schur–Zassenhaus**
   (`Subgroup.exists_left_complement'_of_coprime`) and proves cyclicity via a new
   self-contained route: a central order-p element of Q is conjugate to a shear,
   Sylow maximality gives Q = (conj c • S F) ⊓ G, and the diagonal-projection
   homomorphism `L_toUnits_hom : L F →* Fˣ` (kernel S F) embeds N_G(Q)/Q into Fˣ.

5. **Thm 6.8(v-b)** (tex 950-975; `S2_B: K_mem_MaximalAbelianSubgroups_of_center_lt_card_K`).
   Butler's proof is projective-geometric (fixed points on P¹, Prop 6.7). The
   formalization proves it **algebraically**: the centralizer of a regular
   lower-triangular element is contained in L F (2×2 computation), plus
   L ≤ N(S) and cardinality comparison. Prop 6.7 itself is not formalized.
   An added hypothesis `Nat.Coprime (Nat.card K) p` matches the K produced by (v-a).

6. **Lemma 3.2 / caseVlemma** (tex 1306-1349; `Ch7: Sylow.not_normal_subgroup_of_G`).
   Butler's hypotheses [N_G(K):K] = 2 and Q ∩ K = 1 were missing from the original
   Lean stub; they are now explicit hypotheses (the stub was unprovable without them).

7. **Class-equation architecture** (tex 1107-1270; `S3`, `S4_CaseArithmetic`,
   `S5_NumericClassEquation`). Butler's counting narrative is reorganized into:
   a set-theoretic partition identity (S3), a pure-ℚ arithmetic layer
   (S4: `ClassEquation`, `case_enumeration`, per-case openers), and a bridge
   (`S5: main_bridge` / witness-carrying `exists_bridgeData`) that constructs the
   (g,q,k,s,t,gs,gt) data from a concrete finite subgroup. `main_bridge` carries
   `p ≠ 2` (inherited from divergence 1).

8. **Recognition lemmas** (`Ch7_GroupRecognition.lean`). Butler identifies groups
   from presentations by inspection/citation. The formalization proves explicit
   recognition lemmas (`mulEquiv_dihedralGroup_of`, `mulEquiv_quaternionGroup_of`)
   from generator/relation/cardinality data, matching mathlib's conventions.
   Butler's dihedral-order-2n groups with n odd in char-2 (Case IVa) and dicyclic
   ⟨x,y | xⁿ=y², yxy⁻¹=x⁻¹⟩ (Cases IIa/VIa) map to mathlib's `DihedralGroup n`
   and `QuaternionGroup n` respectively — note earlier drafts wrongly used
   `DihedralGroup` for the dicyclic cases (impossible in SL(2,F), p ≠ 2, which
   has a unique involution); fixed.

9. **`dicksons_classification_theorem_class_I`'s dispatch** (tex 2213-2226/2237-2254).
   Its body now genuinely obtains `BridgeData` (`center_le_G`/`hp2 : p ≠ 2` added as
   narrowing hypotheses, see the theorem's own docstring) and dispatches on
   `CaseArithmetic.case_enumeration`'s six `(s,t)` branches into `case_I` ... `case_VI`.
   A structural observation not in Butler's own exposition (he only ever states Class I
   in terms of `p ∤ |G|` directly, not via the class-equation case split) considerably
   simplifies the dispatch: `p ∤ |G|` forces every Sylow `p`-subgroup of `G` trivial,
   hence `q = k = 1` throughout `BridgeData` (via `hSylow`), which in turn makes
   Butler's own per-case arithmetic (`case_0_1`, `case_0_2`) *contradict* `q = 1` in
   the `(0,1)`/`(0,2)` branches (`case_IV`/`case_V`, i.e. his Class II) — so those
   branches are dispatched by deriving `False`, not by calling `case_IV`/`case_V` at
   all (a new auxiliary lemma, `two_card_le_of_relIndex_normalizer_eq_two`, supplies
   the `2*g1 ≤ g`-style numeral fact `case_0_1`/`case_0_2` need, which is not itself a
   `BridgeData` field). The `(0,0)` branch (`case_III`, his Class III) is similarly
   shown impossible (would force `G = center SL(2,F)`, excluded by construction). The
   `(1,0)` (`case_I`) and `(1,1)` (`case_II`) branches call the corresponding lemma
   for real, post-processing `case_I`'s structural conclusion (`Q` trivial ⟹ its
   cyclic complement is all of `G`) into `IsCyclic G`. The `(0,3)` branch (`case_VI`)
   is consistent with `q = 1` (it is Butler's own Class I (vi)) and is dispatched for
   real, inheriting `case_VI`'s own residual `sorry` (the `g₁ = 2` `WLOG` split).
   Sorry-debt of `dicksons_classification_theorem_class_I` is therefore exactly:
   `case_II`'s `g1 = 3` branch and `case_VI`'s own gap (both pre-existing, unchanged).
   Left out of scope (per the task instructions, separate pending items): the
   `Z ⊄ G ⟹ |G|` odd `⟹` Class I/III reduction (this theorem's own `hp'` disjunct does
   not imply `center_le_G`) and the char-2 finale (`hp2 : p ≠ 2` excludes `p = 2`
   entirely, tracking `case_IV`'s Case IVb-independent residual gap, item 1 above).

## Repaired Lean statement drafts (not Butler errors)

- `IsPGroup.not_le_normalizer` → `IsPGroup.lt_normalizer_subgroupOf` (original
  contradicted `Subgroup.le_normalizer`; Butler Lemma 3.1 tex 1277 is about N_K(H)).
- `normalizer_D_eq_DW` needed `[IsAlgClosed F]` (false over 𝔽₂/𝔽₃).
- `card_SL_field` needed `n ≠ 0` (ℕ-division artifact).
- `case_III`'s `IsComplement'` conjunct was in the wrong ambient group (contradicted
  the subgroup-equality conjunct); now stated internally to G.
- Final-theorem disjunct lists: self-contained existentials; `Equiv.Perm (Fin 5)`
  → `(Fin 4)` in the PGL₂ statement (S₄, per the classical list).
