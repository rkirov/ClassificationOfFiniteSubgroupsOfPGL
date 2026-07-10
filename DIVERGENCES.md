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
   p ≠ 2). **Fix pending**: replace with a presented binary octahedral group
   ⟨a, b | a⁴ = b³ = (ab)²⟩ (or the equivalent unique-involution double-cover
   characterization). This is a formalization erratum, not Butler's.

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

## Repaired Lean statement drafts (not Butler errors)

- `IsPGroup.not_le_normalizer` → `IsPGroup.lt_normalizer_subgroupOf` (original
  contradicted `Subgroup.le_normalizer`; Butler Lemma 3.1 tex 1277 is about N_K(H)).
- `normalizer_D_eq_DW` needed `[IsAlgClosed F]` (false over 𝔽₂/𝔽₃).
- `card_SL_field` needed `n ≠ 0` (ℕ-division artifact).
- `case_III`'s `IsComplement'` conjunct was in the wrong ambient group (contradicted
  the subgroup-equality conjunct); now stated internally to G.
- Final-theorem disjunct lists: self-contained existentials; `Equiv.Perm (Fin 5)`
  → `(Fin 4)` in the PGL₂ statement (S₄, per the classical list).
