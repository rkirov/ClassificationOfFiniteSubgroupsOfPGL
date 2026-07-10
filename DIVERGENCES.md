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

   **Extension — `SL(2,3)` recognition (Case IIb, tex ~1512-1653, `g₁ = 3`; Case IVb,
   tex ~1785, "analogous to Case IIb")**: `mulEquiv_SL2_ZMod3_of` proves, from Butler's
   presentation `⟨x,y,r | x²=y², yxy⁻¹=x⁻¹, r³=1, rxr⁻¹=y, ryr⁻¹=xy⟩` plus
   `Nat.card G = 24`, that `G ≃* SL(2, ZMod 3)`. Butler pins down the isomorphism by
   direct inspection: he exhibits explicit matrices `a,b,c ∈ SL(2,3)` satisfying the
   same relations and asserts the map `x ↦ a, y ↦ b, r ↦ c` is an isomorphism "since `G`
   and `SL(2,3)` have the same order and their generators satisfy the corresponding
   relations" (tex ~1642-1653) — a coset-enumeration-style argument not directly
   formalizable without substantial extra work (bounding the order of the abstractly
   presented group `⟨x,y,r | …⟩` from above by `24`). The formalization instead uses a
   **semidirect-product gluing** route: (a) `⟨x,y⟩` is recognized as (embeds as, without
   yet knowing its cardinality) a copy of `Q₈` via a variant of `mulEquiv_quaternionGroup_of`
   that stops at injectivity onto the *range* (`quaternionGroup_hom_injective`); (b) this
   range `N` is shown normal of order `8`, complemented by the order-`3` subgroup `⟨r⟩`
   (`Nat.card G = 24 = 8·3`, coprimality), giving `G ≃* N ⋊ ⟨r⟩` via mathlib's
   `SemidirectProduct.mulEquivSubgroup`; (c) applying (a)-(b) *identically* to
   `SL(2, ZMod 3)` itself (with Butler's own matrices `a,b,c⁻¹` as witnesses — note `c⁻¹`,
   not `c`: with the `r x r⁻¹ = y` convention it is `c⁻¹` that conjugates `a ↦ b`, a
   presentation-level swap, not a mathematical divergence) gives a matching semidirect
   decomposition of `SL(2,3)`; (d) the two decompositions are glued via
   `SemidirectProduct.congr`, matching `⟨x,y⟩ ≃* Q₈ ≃* ⟨a,b⟩` and `⟨r⟩ ≃* ⟨c⁻¹⟩`
   generator-to-generator, with the one nontrivial compatibility check (conjugation
   actions agree after transport) reduced to a finite `3`-way case split on `⟨r⟩`'s
   `3` elements (closed by direct computation, using a derived `r²`-conjugation formula,
   `rsq_conj_formula`, for the third case). All `SL(2,3)`-side algebraic facts (matrix
   orders, relations, `|SL(2,3)| = 24`) are verified by `decide`. This lemma is proved but
   **not yet wired into `Ch7_DicksonsClassificationTheorem.lean`**'s `case_II`/`case_IV`
   sorries (out of scope for this file; `Ch7_GroupRecognition.lean` was the exclusive
   target), so those two residual sorries are unchanged by this addition.

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

10. **Case IIb / Case IVb residual gap** (tex ~1512-1653 and ~1785; `Ch7:
    exists_Q8_generators_of_relIndex_two`, `case_II`'s `g1 = 3` branch, `case_IV`'s Case IVb
    branch). Both branches are now **partially proved**: Butler's numerals (`g2 = 2`/`g1 = 2`,
    `g = 12`, `e = 2`, `Nat.card G = 24`) and his `Q₈`-shaped presentation of `N_G(A₂)` (resp.
    `N_G(A)`) -- `x0, y0 : ↥G` with `orderOf x0 = 4`, `x0² = y0²`, `y0 x0 y0⁻¹ = x0⁻¹`,
    `y0 ∉ zpowers x0` -- are proved directly, via a new shared lemma
    `exists_Q8_generators_of_relIndex_two` factoring out the derivation already inlined in
    `case_II`'s (proved) Case IIa block. This is exactly the input `mulEquiv_SL2_ZMod3_of`
    (item 8 above, already proved in `Ch7_GroupRecognition.lean`) needs, *except* for the
    order-`3` element `r` and its exact conjugation relations `r x0 r⁻¹ = y0`,
    `r y0 r⁻¹ = x0 y0`.

    Producing `r` is left `sorry`, and investigation shows the gap is **deeper than "relation
    labeling"**: Butler's own route (tex ~1582 "`N` is thus a unique Sylow `2`-subgroup ... by
    Corollary 4thSylow, `N ⊴ G`") first shows `N := N_G(A₂)` is the *unique* Sylow `2`-subgroup
    of `G` (hence normal) by a **global element-order count**: every element of `2`-power order
    in `G` lies in a conjugate of `A₁` or of `A₂` (there being, since `s = 1, t = 1, q = 1`, no
    other maximal abelian classes at all), and `A₁`'s conjugates (odd-times-`2` order, cyclic)
    contribute none beyond `Z`, so exactly `|N| = 8` such elements exist in all of `G` -- forcing
    every (conjugate, hence isomorphic) Sylow `2`-subgroup to coincide with `N`. Only *then* does
    Butler let the order-`3` subgroup `H ≤ A₁` act (by conjugation) on `N`'s `3` maximal cyclic
    subgroups, landing the desired relations after a `2`-way relabeling.

    The "no maximal abelian class besides `A₁, A₂`" fact used in the first step is a genuine
    *global* statement about all of `G` (not a per-subgroup local one like the rest of Theorem
    6.8), and is not currently exposed as a reusable lemma: `S3_NoncenterClassEquation`'s
    `Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G)` Fintype construction and
    `S5_NumericClassEquation`'s `exists_bridgeData` implicitly *prove* it while assembling
    `s, t`, but do not *export* it, and `case_II`/`case_IV`'s own hypotheses (the per-class
    witness data `A1, A2`/`A` plus the numeric `ClassEquation`) do not carry it either. A
    self-contained alternative route was explored (using `H ∩ N = 1` -- provable directly from
    Lagrange plus `SL(2,F)`'s unique involution, no exhaustiveness needed -- to get
    `|G| = |H| · |N|` and hence, by orbit-stabilizer, a genuinely *transitive* action of `H` on
    the `3` `G`-conjugates of `A₂`) but still bottoms out on the same fact: showing the specific
    conjugate `r A₂ r⁻¹` lands *inside* `N` itself (as opposed to some other Sylow `2`-subgroup
    conjugate to, but not equal to, `N`) is equivalent to `N ⊴ G`. This matches the same category
    of gap already left open in `case_VI_core`'s `gb = gc = 3` branch (tex ~2149-2157, "Sylow-
    conjugacy elimination... genuinely group-theoretic, not pure arithmetic, and is not attempted
    here") -- both are instances of the same missing global-exhaustiveness infrastructure.

## Repaired Lean statement drafts (not Butler errors)

- `IsPGroup.not_le_normalizer` → `IsPGroup.lt_normalizer_subgroupOf` (original
  contradicted `Subgroup.le_normalizer`; Butler Lemma 3.1 tex 1277 is about N_K(H)).
- `normalizer_D_eq_DW` needed `[IsAlgClosed F]` (false over 𝔽₂/𝔽₃).
- `card_SL_field` needed `n ≠ 0` (ℕ-division artifact).
- `case_III`'s `IsComplement'` conjunct was in the wrong ambient group (contradicted
  the subgroup-equality conjunct); now stated internally to G.
- Final-theorem disjunct lists: self-contained existentials; `Equiv.Perm (Fin 5)`
  → `(Fin 4)` in the PGL₂ statement (S₄, per the classical list).
