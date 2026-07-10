/-
This file bridges the set-theoretic Maximal Abelian Subgroup Class Equation
(`S3_NoncenterClassEquation.card_noncenter_fin_subgroup_eq_sum_card_noncenter_mul_index_normalizer`)
towards the purely numeric `CaseArithmetic.ClassEquation` of `S4_CaseArithmetic`
(Butler tex lines ~1107-1270).

The plan (Butler ~1107-1150):
* Every `A ∈ MaximalAbelianSubgroupsOf G` is either of *coprime type* (cyclic, order coprime
  to `p`) or of *Sylow type* (`A = Q ⊔ Z` for `Q` a nontrivial elementary abelian Sylow
  `p`-subgroup) -- Theorem 6.8(iii), already proved in `S2_A` as
  `isCyclic_and_card_coprime_charP_or_eq_Q_sup_Z`. We record this dichotomy, show the two
  types are mutually exclusive, and show both the cardinality of `A` and its "type" are
  invariant under conjugation by elements of `G` -- so the dichotomy descends to the
  conjugacy classes making up `Quotient (lift_MaximalAbelianSubgroupsOf G)`.
* All Sylow-type classes coincide: any two nontrivial Sylow `p`-subgroups of `G` are
  `G`-conjugate (Sylow's second theorem), hence so are the corresponding `Q ⊔ Z` maximal
  abelian subgroups; so there is *at most one* Sylow-type conjugacy class.
* For a coprime-type class, the size of `C(A)^*` (the union of conjugates of `A^*`) is
  pinned down by Lagrange + `S3`'s bijections (`card_ConjClassOf_eq_index_normalizer`,
  `card_noncenter_ConjClassOfSet_eq_card_ConjClassOfSet`,
  `card_noncenter_C_eq_noncenter_MaximalAbelianSubgroup_mul_noncenter_ConjClassOfSet`) in terms
  of `Nat.card G`, `Nat.card A` and `[N_G(A) : A] ∈ {1, 2}` (Theorem 6.8(iv),
  `relIndex_normalizer_le_two`, proved in `S2_A` for `p ≠ 2`).
* For the (unique, if it exists) Sylow-type class, the analogous statement
  (`card_union_conjClasses_sylow_class`) is now also fully proved: the key extra step -- not
  anticipated by the original module plan -- is
  `normalizer_join_eq_normalizer_of_isPGroup_of_central_of_coprime`, which shows
  `N_G(Q ⊔ Z) = N_G(Q)` via a Sylow-uniqueness/characteristic-subgroup argument
  (`Sylow.characteristic_of_normal`) rather than by directly transporting the *set-union* fact
  `normalizer_Sylow_join_center_eq_normalizer_Sylow` (which is about `Q ∪ Z` as a plain set,
  not the subgroup join `Q ⊔ Z`, and so does not transport directly).
  `card_union_conjClasses_sylow_class` is stated with three extra hypotheses (`Q ≠ ⊥`, `K ≤ G`,
  `Disjoint (Q.subgroupOf G) (K.subgroupOf G)`) beyond the original module plan's sketch; see its
  docstring for why each is needed and why each holds in the intended application.

Full closure into a single instance of `CaseArithmetic.ClassEquation` (`main_bridge`, at the end
of this file) is now also proved, restated with an extra `hp2 : p ≠ 2` hypothesis (needed for
`relIndex_normalizer_le_two`'s `{1,2}`-dichotomy; Butler handles `p = 2` separately in Ch7). The
bookkeeping this required beyond the lemmas above: classifying every noncentral maximal abelian
conjugacy class (a term of the Fintype `Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G)`) as
coprime-type or Sylow-type via a chosen representative, using `isSylowType_conj_of_isSylowType` to
show there is at most one Sylow-type class, splitting the coprime-type classes by normalizer index
and reindexing via `Finset.equivFin` into `Fin s`/`Fin t` families, bridging
`exists_IsCyclic_K_normalizer_eq_Q_join_K` (`S2_B`) into `SL(2,F)`-subgroup data with the
disjointness of `Q`/`K` surfaced (`sylow_class_data`), and showing `Nat.card (center SL(2,F)) ∣
Nat.card K` (via a coprimality/cardinality argument, *not* via Butler's specific
`K = C_G(x) ⊓ G`, which is not what the Lean development constructs). See `main_bridge`'s
docstring for the full construction.
-/
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S3_NoncenterClassEquation
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S4_CaseArithmetic
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S2_B_MaximalAbelianSubgroup

set_option linter.style.longLine true
set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0

open Matrix MatrixGroups Subgroup MulAut MaximalAbelianSubgroup Pointwise SpecialSubgroups

namespace NumericClassEquation

/-! ### 1. The coprime/Sylow taxonomy of `MaximalAbelianSubgroupsOf G` (Butler ~1107-1130) -/

section Taxonomy

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
variable {p : ℕ} [hp' : Fact (Nat.Prime p)] [hC : CharP F p]

/-- **Sylow type**: `A` is the join of a nontrivial elementary abelian Sylow `p`-subgroup `Q`
of `G` with the center. (This is exactly the second disjunct of
`isCyclic_and_card_coprime_charP_or_eq_Q_sup_Z`.) -/
def IsSylowType (p : ℕ) (G A : Subgroup SL(2,F)) : Prop :=
  ∃ Q : Subgroup SL(2,F), Nontrivial Q ∧ Finite Q ∧ Q ≤ G ∧ A = Q ⊔ Z F ∧
    IsElementaryAbelian p Q ∧ ∃ S : Sylow p G, Q.subgroupOf G = S

/-- **Coprime type**: `A` is cyclic of order coprime to `p`. -/
def IsCoprimeType (p : ℕ) (A : Subgroup SL(2,F)) : Prop :=
  IsCyclic A ∧ Nat.Coprime (Nat.card A) p

/--
Theorem 6.8(iii): every maximal abelian subgroup of a finite `G ≤ SL(2,F)` is of coprime type
or of Sylow type. This is a restatement of
`isCyclic_and_card_coprime_charP_or_eq_Q_sup_Z` under the names used in this file.
-/
theorem isCoprimeType_or_isSylowType (G : Subgroup SL(2,F)) [Finite G]
    (center_le_G : center SL(2,F) ≤ G) (A : MaximalAbelianSubgroupsOf G) :
    IsCoprimeType p A.val ∨ IsSylowType p G A.val :=
  isCyclic_and_card_coprime_charP_or_eq_Q_sup_Z G A.val A.prop center_le_G

omit [IsAlgClosed F] [DecidableEq F] hp' hC in
/-- Sylow-type subgroups have order divisible by `p` (`Q` is a nontrivial `p`-group and
`Q ≤ A`), so in particular they cannot also be of coprime type. -/
theorem dvd_card_of_isSylowType {G A : Subgroup SL(2,F)} [Finite A]
    (h : IsSylowType p G A) : p ∣ Nat.card A := by
  obtain ⟨Q, hQnontriv, hQfin, -, hAeq, hQelem, -⟩ := h
  haveI := hQfin
  have hQ_le_A : Q ≤ A := hAeq ▸ le_sup_left
  have hQ_dvd_A : Nat.card Q ∣ Nat.card A := Subgroup.card_dvd_of_le hQ_le_A
  have hQ_bot_lt : (⊥ : Subgroup SL(2,F)) < Q :=
    bot_lt_iff_ne_bot.mpr ((Subgroup.nontrivial_iff_ne_bot Q).mp hQnontriv)
  exact (hQelem.dvd_card hQ_bot_lt).trans hQ_dvd_A

omit [IsAlgClosed F] [DecidableEq F] hC in
/-- The two types are mutually exclusive. -/
theorem not_isCoprimeType_and_isSylowType {G A : Subgroup SL(2,F)} [Finite A] :
    ¬ (IsCoprimeType p A ∧ IsSylowType p G A) := by
  rintro ⟨⟨-, hcop⟩, hsyl⟩
  exact (hp'.out.coprime_iff_not_dvd.mp hcop.symm) (dvd_card_of_isSylowType hsyl)

end Taxonomy

/-! ### 2. Well-definedness of cardinality, normalizer index and taxonomy on conjugacy classes
(Butler ~1130-1150) -/

section ConjInvariance

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]

omit [IsAlgClosed F] [DecidableEq F] in
/-- Conjugating (by an element of `G`) a maximal abelian subgroup of `G` stays a maximal
abelian subgroup of `G`, since `conj c • G = G` for `c ∈ G`. -/
theorem conj_smul_mem_MaximalAbelianSubgroupsOf_of_mem {G A : Subgroup SL(2,F)}
    (hA : A ∈ MaximalAbelianSubgroupsOf G) {c : SL(2,F)} (hc : c ∈ G) :
    conj c • A ∈ MaximalAbelianSubgroupsOf G := by
  have h := (mem_iff_conj_smul_mem_MaximalAbelianSubgroupsOf_conj_smul A G c).mp hA
  rwa [Subgroup.conj_smul_eq_self_of_mem hc] at h

omit [IsAlgClosed F] [DecidableEq F] in
/-- Conjugate maximal abelian subgroups have equal cardinality (no hypothesis on `c` is needed:
conjugation by any element of `SL(2,F)` is an automorphism). -/
theorem card_conj_smul_eq_card {A : Subgroup SL(2,F)} (c : SL(2,F)) :
    Nat.card (conj c • A : Subgroup SL(2,F)) = Nat.card A :=
  (card_conj_eq_card (A := conj c • A) (A' := A) rfl).symm

omit [IsAlgClosed F] [DecidableEq F] in
/-- Conjugate maximal abelian subgroups (by an element of `G`) have the same normalizer index
`[N_G(A) : A]`. -/
theorem relIndex_normalizer_conj_smul_eq {G A : Subgroup SL(2,F)} {c : SL(2,F)} (hc : c ∈ G) :
    relIndex (((conj c • A : Subgroup SL(2,F))).subgroupOf G)
        (normalizer (((conj c • A : Subgroup SL(2,F))).subgroupOf G : Set ↥G))
      = relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) := by
  have hG : G = conj c • G := (Subgroup.conj_smul_eq_self_of_mem hc).symm
  exact (relIndex_MaximalAbelianSubgroupOf_normalizer_eq_relIndex_conj_MaxAbelianSubgroupOf
    (A := conj c • A) (A' := A) (G := G) (G' := G) rfl hG).symm

omit [IsAlgClosed F] [DecidableEq F] in
/-- Conjugate maximal abelian subgroups have the same taxonomy type: coprime type transports to
coprime type (no hypothesis on `c` is needed). -/
theorem isCoprimeType_conj_smul_of_isCoprimeType {p : ℕ} {A : Subgroup SL(2,F)} (c : SL(2,F))
    (h : IsCoprimeType p A) :
    IsCoprimeType p (conj c • A : Subgroup SL(2,F)) := by
  obtain ⟨hcyc, hcop⟩ := h
  refine ⟨(MulEquiv.isCyclic (Subgroup.equivSMul (conj c) A)).mp hcyc, ?_⟩
  rwa [card_conj_smul_eq_card c]

/-- Conjugate maximal abelian subgroups (by an element of `G`) have the same taxonomy type:
Sylow type transports to Sylow type. Proof: `p ∣ Nat.card A` (since `A` is Sylow type) and
`Nat.card (conj c • A) = Nat.card A`, so `conj c • A` cannot be coprime type; by the (proven)
dichotomy it must then be Sylow type. -/
theorem isSylowType_conj_smul_of_isSylowType {p : ℕ} [hp' : Fact (Nat.Prime p)] [CharP F p]
    {G A : Subgroup SL(2,F)}
    [Finite G] (center_le_G : center SL(2,F) ≤ G) (hAmem : A ∈ MaximalAbelianSubgroupsOf G)
    [Finite A] {c : SL(2,F)} (hc : c ∈ G) (h : IsSylowType p G A) :
    IsSylowType p G (conj c • A : Subgroup SL(2,F)) := by
  have hAmem' := conj_smul_mem_MaximalAbelianSubgroupsOf_of_mem hAmem hc
  have hpdvd : p ∣ Nat.card (conj c • A : Subgroup SL(2,F)) := by
    rw [card_conj_smul_eq_card c]; exact dvd_card_of_isSylowType h
  rcases isCoprimeType_or_isSylowType G center_le_G ⟨_, hAmem'⟩ with hcop | hsyl
  · exact absurd hpdvd (hp'.out.coprime_iff_not_dvd.mp hcop.2.symm)
  · exact hsyl

end ConjInvariance

/-! ### 3. All Sylow-type maximal abelian subgroups are `G`-conjugate (Butler ~1150-1180) -/

section SylowUnique

/-- Every finite group has only finitely many Sylow `p`-subgroups: `Sylow p L` embeds
(via `Sylow.toSubgroup` and the coercion to `Set L`) into the finite type `Set L`.
(This should probably be a mathlib instance analogous to `Set.instFinite`.) -/
instance finite_Sylow {L : Type*} [Group L] [Finite L] (p : ℕ) : Finite (Sylow p L) :=
  Finite.of_injective (fun S : Sylow p L => (S.toSubgroup : Set L))
    (fun _S _T hST => Sylow.ext (SetLike.coe_injective hST))

/-- Naturality of pointwise conjugation-action under a group homomorphism: pushing a subgroup
`K` forward along `f` and then conjugating by `f g` agrees with conjugating by `g` first and
then pushing forward. (This should probably be a mathlib lemma alongside `Subgroup.map_map`.) -/
theorem map_conj_smul {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) (K : Subgroup G) :
    Subgroup.map f (MulAut.conj g • K) = MulAut.conj (f g) • Subgroup.map f K := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists, MulAut.smul_def,
    MulAut.conj_apply]
  constructor
  · rintro ⟨x, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨f k, ⟨k, hk, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨z, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨g * k * g⁻¹, ⟨k, hk, rfl⟩, by rw [map_mul, map_mul, map_inv]⟩

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
variable {p : ℕ} [hp' : Fact (Nat.Prime p)] [hC : CharP F p]

omit [IsAlgClosed F] [DecidableEq F] hC in
/-- Any two Sylow-type maximal abelian subgroups of a finite `G ≤ SL(2,F)` are `G`-conjugate:
their witnessing Sylow `p`-subgroups `Q_A.subgroupOf G`/`Q_B.subgroupOf G` are conjugate in `↥G`
by Sylow's second theorem, and conjugating `Q_A ⊔ Z` by (the image of) that same element gives
`Q_B ⊔ Z` since `conj • Z = Z` (`Z` is central) and pointwise conjugation distributes over `⊔`. -/
theorem isSylowType_conj_of_isSylowType {G A B : Subgroup SL(2,F)} [Finite G]
    (hA : IsSylowType p G A) (hB : IsSylowType p G B) :
    ∃ c ∈ G, conj c • A = B := by
  obtain ⟨QA, -, -, hQA_le, hAeq, -, SA, hSA⟩ := hA
  obtain ⟨QB, -, -, hQB_le, hBeq, -, SB, hSB⟩ := hB
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (α := Sylow p G) G SA SB
  refine ⟨(g : SL(2,F)), g.2, ?_⟩
  have hg' : MulAut.conj g • SA.toSubgroup = SB.toSubgroup := congrArg Sylow.toSubgroup hg
  have hSA' : QA.subgroupOf G = SA.toSubgroup := hSA
  have hSB' : QB.subgroupOf G = SB.toSubgroup := hSB
  have hQA_map : Subgroup.map G.subtype (QA.subgroupOf G) = QA :=
    map_subgroupOf_eq_of_le hQA_le
  have hQB_map : Subgroup.map G.subtype (QB.subgroupOf G) = QB :=
    map_subgroupOf_eq_of_le hQB_le
  have hstep : Subgroup.map G.subtype (MulAut.conj g • (QA.subgroupOf G))
      = Subgroup.map G.subtype (QB.subgroupOf G) := by
    congr 1
    rw [hSA', hg', hSB']
  have key : conj (g : SL(2,F)) • QA = QB := by
    rw [← hQA_map, ← hQB_map, ← hstep, map_conj_smul]
    rfl
  have hZ_inv : conj (g : SL(2,F)) • Z F = Z F := by
    rw [← center_SL2_eq_Z F]
    exact Normal.conj_smul_eq_self (g : SL(2,F)) (center SL(2,F))
  rw [hAeq, hBeq, Subgroup.smul_sup, key, hZ_inv]

end SylowUnique

/-! ### 4. Cardinality of a coprime-type conjugacy class (Butler ~1180-1206) -/

section CoprimeClassCard

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]

omit [IsAlgClosed F] [DecidableEq F] in
/-- `|A^*| + |Z| = |A|` for `A ∈ MaximalAbelianSubgroupsOf G` (`Z ≤ A` by `center_le`, so the
noncentral part `A^*` together with `Z` partitions `A`). Stated additively (rather than with
`Nat.card A - Nat.card Z`) to avoid truncated subtraction. -/
theorem card_noncenter_add_card_center_eq_card {G A : Subgroup SL(2,F)} [Finite A]
    (hA : A ∈ MaximalAbelianSubgroupsOf G) (center_le_G : center SL(2,F) ≤ G) :
    Nat.card (noncenter A : Set SL(2,F)) + Nat.card (center SL(2,F)) = Nat.card A := by
  haveI : Finite (center SL(2,F)) := by rw [center_SL2_eq_Z]; infer_instance
  have hZ_le_A : center SL(2,F) ≤ A := center_le G A hA center_le_G
  have hZ_sub : (center SL(2,F) : Set SL(2,F)) ⊆ A.carrier := hZ_le_A
  have hAfin : A.carrier.Finite := Set.toFinite _
  have hkey := Set.ncard_sdiff_add_ncard_of_subset hZ_sub hAfin
  have hA_ncard : A.carrier.ncard = Nat.card A := by rw [← Nat.card_coe_set_eq]; rfl
  have hZ_ncard : (center SL(2,F) : Set SL(2,F)).ncard = Nat.card (center SL(2,F)) := by
    rw [← Nat.card_coe_set_eq]; rfl
  have hnoncenter_ncard : (A.carrier \ (center SL(2,F) : Set SL(2,F))).ncard
      = Nat.card (noncenter A : Set SL(2,F)) := by
    rw [← Nat.card_coe_set_eq]; rfl
  rw [hnoncenter_ncard, hZ_ncard, hA_ncard] at hkey
  exact hkey

omit [IsAlgClosed F] [DecidableEq F] in
/-- Same as `card_noncenter_add_card_center_eq_card`, but for `G` itself (which need not be
abelian, so is not covered by that lemma): `|G \ Z| + |Z| = |G|`. Needed in `main_bridge` to
turn `S3`'s partition-of-`G \ Z` identity into a statement about `Nat.card G`. -/
theorem card_noncenter_add_card_center_eq_card' {G : Subgroup SL(2,F)} [Finite G]
    (center_le_G : center SL(2,F) ≤ G) :
    Nat.card (noncenter G : Set SL(2,F)) + Nat.card (center SL(2,F)) = Nat.card G := by
  haveI : Finite (center SL(2,F)) := by rw [center_SL2_eq_Z]; infer_instance
  have hZ_sub : (center SL(2,F) : Set SL(2,F)) ⊆ G.carrier := center_le_G
  have hGfin : G.carrier.Finite := Set.toFinite _
  have hkey := Set.ncard_sdiff_add_ncard_of_subset hZ_sub hGfin
  have hG_ncard : G.carrier.ncard = Nat.card G := by rw [← Nat.card_coe_set_eq]; rfl
  have hZ_ncard : (center SL(2,F) : Set SL(2,F)).ncard = Nat.card (center SL(2,F)) := by
    rw [← Nat.card_coe_set_eq]; rfl
  have hnoncenter_ncard : (G.carrier \ (center SL(2,F) : Set SL(2,F))).ncard
      = Nat.card (noncenter G : Set SL(2,F)) := by
    rw [← Nat.card_coe_set_eq]; rfl
  rw [hnoncenter_ncard, hZ_ncard, hG_ncard] at hkey
  exact hkey

omit [IsAlgClosed F] [DecidableEq F] in
/-- Lagrange's theorem applied twice to `A.subgroupOf G ≤ normalizer (A.subgroupOf G) ≤ ↥G`:
`|A| \cdot \big([N_G(A):A] \cdot [G:N_G(A)]\big) = |G|`. -/
theorem card_mul_relIndex_mul_index_normalizer_eq_card {G A : Subgroup SL(2,F)} [Finite G]
    (hA : A ∈ MaximalAbelianSubgroupsOf G) :
    Nat.card A * (relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G))
        * index (normalizer (A.subgroupOf G : Set ↥G)))
      = Nat.card G := by
  set H : Subgroup ↥G := A.subgroupOf G with hH_def
  have hcard_H : Nat.card H = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.right).toEquiv
  have hLagrange1 : Nat.card H * H.index = Nat.card G := Subgroup.card_mul_index H
  have hLagrange2 : H.relIndex (normalizer (H : Set ↥G)) * (normalizer (H : Set ↥G)).index
      = H.index := Subgroup.relIndex_mul_index le_normalizer
  rw [← hcard_H, hLagrange2]
  exact hLagrange1

omit [IsAlgClosed F] [DecidableEq F] in
/-- Both `Nat.card A` and the normalizer index `[N_G(A):A]` are (nonzero, hence) positive. -/
theorem card_pos_and_relIndex_pos {G A : Subgroup SL(2,F)} [Finite G]
    (hA : A ∈ MaximalAbelianSubgroupsOf G) :
    0 < Nat.card A ∧
      0 < relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) := by
  have hL := card_mul_relIndex_mul_index_normalizer_eq_card hA
  have hGpos : 0 < Nat.card G := Nat.card_pos
  rw [← hL] at hGpos
  rcases Nat.eq_zero_or_pos (Nat.card A) with hA0 | hApos
  · simp [hA0] at hGpos
  refine ⟨hApos, ?_⟩
  rcases Nat.eq_zero_or_pos
      (relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G))) with hδ0 | hδpos
  · simp [hδ0] at hGpos
  · exact hδpos

/--
The size of the conjugacy class `C(A^*)` of a coprime-type maximal abelian subgroup `A`, in the
exact multiplicative (division-free) shape of Lagrange's theorem applied twice
(`|G| = |N_G(A)| \cdot [G : N_G(A)]` and `|N_G(A)| = [N_G(A) : A] \cdot |A|`):
`|C(A^*)| \cdot \big([N_G(A):A] \cdot |A|\big) = |A^*| \cdot |G|`.
Combined with `relIndex_normalizer_le_two` (`[N_G(A):A] ∈ {1,2}` when `p ≠ 2`) and
`card_noncenter_add_card_center_eq_card`, this pins down `|C(A^*)|` exactly in terms of
`|G|, |A|, |Z|` and the normalizer index; `card_union_conjClasses_coprime_class_rat` below
recasts this as a single rational-division identity.
-/
theorem card_union_conjClasses_coprime_class {G A : Subgroup SL(2,F)} [Finite G]
    (center_le_G : center SL(2,F) ≤ G) (hA : A ∈ MaximalAbelianSubgroupsOf G) :
    Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G
        (⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G ⟨A, hA⟩⟩))
      * (relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) * Nat.card A)
      = Nat.card (noncenter A : Set SL(2,F)) * Nat.card G := by
  haveI hAfin : Finite A := Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hA.right
  set Astar : noncenter_MaximalAbelianSubgroupsOf G :=
    ⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G ⟨A, hA⟩⟩ with hAstar_def
  set H : Subgroup ↥G := A.subgroupOf G with hH_def
  set δ : ℕ := relIndex H (normalizer (H : Set ↥G)) with hδ_def
  -- Step 1: the size of `C(A^*)` in terms of the index of the normalizer.
  have h1 : Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G Astar)
      = Nat.card (noncenter A : Set SL(2,F)) * card_noncenter_ConjClassOf G Astar :=
    card_noncenter_C_eq_noncenter_MaximalAbelianSubgroup_mul_noncenter_ConjClassOfSet
      G center_le_G Astar
  have h2 : card_noncenter_ConjClassOf G Astar = Nat.card (ConjClassOf G ⟨A, hA⟩) :=
    (card_noncenter_ConjClassOfSet_eq_card_ConjClassOfSet G ⟨A, hA⟩).symm
  have h3 : Nat.card (ConjClassOf G ⟨A, hA⟩) = index (normalizer (H : Set ↥G)) :=
    card_ConjClassOf_eq_index_normalizer G ⟨A, hA⟩
  -- Step 2: Lagrange, applied twice: `|A| ⬝ (δ ⬝ [G : N_G(A)]) = |G|`.
  have hLagrange := card_mul_relIndex_mul_index_normalizer_eq_card (A := A) hA
  rw [← hH_def, ← hδ_def] at hLagrange
  -- Step 3: assemble.
  calc Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G Astar)
        * (δ * Nat.card A)
      = (Nat.card (noncenter A : Set SL(2,F)) * index (normalizer (H : Set ↥G)))
          * (δ * Nat.card A) := by rw [h1, h2, h3]
    _ = Nat.card (noncenter A : Set SL(2,F))
          * (Nat.card A * (δ * index (normalizer (H : Set ↥G)))) := by
        ring
    _ = Nat.card (noncenter A : Set SL(2,F)) * Nat.card G := by rw [hLagrange]

/-- The Nat identity `card_union_conjClasses_coprime_class` recast as a single rational-division
equation: `|C(A^*)| / |G| = |A^*| / ([N_G(A):A] \cdot |A|)`. -/
theorem card_union_conjClasses_coprime_class_rat {G A : Subgroup SL(2,F)} [Finite G]
    (center_le_G : center SL(2,F) ≤ G) (hA : A ∈ MaximalAbelianSubgroupsOf G) :
    (Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G
        (⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G ⟨A, hA⟩⟩)) : ℚ)
        / Nat.card G
      = (Nat.card (noncenter A : Set SL(2,F)) : ℚ)
          / (relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) * Nat.card A) := by
  have hnat := card_union_conjClasses_coprime_class center_le_G hA
  have hpos := card_pos_and_relIndex_pos hA
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hcast : (Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G
        (⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G ⟨A, hA⟩⟩)) : ℚ)
        * (relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) * Nat.card A)
      = (Nat.card (noncenter A : Set SL(2,F)) : ℚ) * Nat.card G := by exact_mod_cast hnat
  have hδA_ne : ((relIndex (A.subgroupOf G) (normalizer (A.subgroupOf G : Set ↥G)) : ℚ)
      * Nat.card A) ≠ 0 := by
    have := Nat.mul_pos hpos.2 hpos.1
    exact_mod_cast this.ne'
  rw [div_eq_div_iff (by exact_mod_cast hGpos.ne') hδA_ne]
  exact hcast

end CoprimeClassCard

/-! ### 5. Cardinality of the Sylow-type conjugacy class (Butler ~1150-1180, second half) -/

section SylowClassCard

/-! #### 5a. Generic subgroup-theoretic helper lemmas (not specific to `SL(2,F)`) -/

/-- If `K.Normal` and `H, K` are disjoint, `|H ⊔ K| = |H| ⋅ |K|`: the underlying set of `H ⊔ K`
is `H * K` (`Subgroup.mul_normal`), and the multiplication map `H × K → H * K` is a bijection
(injective since `H ⊓ K = ⊥`, by construction surjective onto `H * K`). -/
theorem card_sup_eq_of_disjoint_of_normal {L : Type*} [Group L] [Finite L]
    {H K : Subgroup L} [K.Normal] (hd : Disjoint H K) :
    Nat.card (H ⊔ K : Subgroup L) = Nat.card H * Nat.card K := by
  have hset : ((H ⊔ K : Subgroup L) : Set L) = (H : Set L) * (K : Set L) := Subgroup.mul_normal H K
  have hinj : Function.Injective (fun g : H × K => (g.1 : L) * g.2) :=
    Subgroup.mul_injective_of_disjoint hd
  have hrange : Set.range (fun g : H × K => (g.1 : L) * g.2) = ((H ⊔ K : Subgroup L) : Set L) := by
    rw [hset]
    ext x
    constructor
    · rintro ⟨⟨h, k⟩, rfl⟩
      exact Set.mul_mem_mul h.2 k.2
    · intro hx
      rw [Set.mem_mul] at hx
      obtain ⟨h, hh, k, hk, rfl⟩ := hx
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
  calc Nat.card (H ⊔ K : Subgroup L)
      = Nat.card (((H ⊔ K : Subgroup L) : Set L)) := (Nat.card_coe_set_eq _).symm
    _ = Nat.card (Set.range (fun g : H × K => (g.1 : L) * g.2)) := by rw [hrange]
    _ = Nat.card (H × K) := Nat.card_congr (Equiv.ofInjective _ hinj).symm
    _ = Nat.card H * Nat.card K := Nat.card_prod H K

/-- Same conclusion as `card_sup_eq_of_disjoint_of_normal`, but with the (weaker, and here more
convenient) hypothesis `H ≤ normalizer K` in place of `K.Normal`: the underlying set of `H ⊔ K` is
still `H * K` (`Subgroup.coe_mul_of_left_le_normalizer_right`), and the rest of the argument is
identical. -/
theorem card_sup_eq_of_disjoint_of_le_normalizer {L : Type*} [Group L] [Finite L]
    {H K : Subgroup L} (hle : H ≤ normalizer (K : Set L)) (hd : Disjoint H K) :
    Nat.card (H ⊔ K : Subgroup L) = Nat.card H * Nat.card K := by
  have hset : ((H ⊔ K : Subgroup L) : Set L) = (H : Set L) * (K : Set L) :=
    coe_mul_of_left_le_normalizer_right H K hle
  have hinj : Function.Injective (fun g : H × K => (g.1 : L) * g.2) :=
    Subgroup.mul_injective_of_disjoint hd
  have hrange : Set.range (fun g : H × K => (g.1 : L) * g.2) = ((H ⊔ K : Subgroup L) : Set L) := by
    rw [hset]
    ext x
    constructor
    · rintro ⟨⟨h, k⟩, rfl⟩
      exact Set.mul_mem_mul h.2 k.2
    · intro hx
      rw [Set.mem_mul] at hx
      obtain ⟨h, hh, k, hk, rfl⟩ := hx
      exact ⟨(⟨h, hh⟩, ⟨k, hk⟩), rfl⟩
  calc Nat.card (H ⊔ K : Subgroup L)
      = Nat.card (((H ⊔ K : Subgroup L) : Set L)) := (Nat.card_coe_set_eq _).symm
    _ = Nat.card (Set.range (fun g : H × K => (g.1 : L) * g.2)) := by rw [hrange]
    _ = Nat.card (H × K) := Nat.card_congr (Equiv.ofInjective _ hinj).symm
    _ = Nat.card H * Nat.card K := Nat.card_prod H K

/-- If `N_L(Q) = Q ⊔ K` and `Q, K` are disjoint, then `|N_L(Q)| = |Q| ⋅ |K|`
(`K ≤ Q ⊔ K = N_L(Q)` gives the hypothesis of `card_sup_eq_of_disjoint_of_le_normalizer`). -/
theorem card_normalizer_join_eq_of_disjoint_of_le {L : Type*} [Group L] [Finite L]
    {Qg Kg : Subgroup L} (hNG : normalizer (Qg : Set L) = Qg ⊔ Kg)
    (hQK : Disjoint Qg Kg) :
    Nat.card (normalizer (Qg : Set L)) = Nat.card Qg * Nat.card Kg := by
  have hle : Kg ≤ normalizer (Qg : Set L) := hNG ▸ le_sup_right
  have hcard := card_sup_eq_of_disjoint_of_le_normalizer hle hQK.symm
  rw [sup_comm] at hcard
  rw [hNG, hcard, mul_comm]

/--
The normalizer of a "Sylow-type" join `Q ⊔ Zc` (`Q` a nontrivial finite `p`-group, `Zc` central
and of order coprime to `p`) equals the normalizer of `Q` alone. Proof: `Zc` is central hence
normal, and (since it centralizes everything) `Q ⊔ Zc ≤ normalizer Q`, giving one inclusion
(`normalizer_le_normalizer_sup_normal` gives the other, easy, inclusion for free). For the hard
inclusion, `Q` is normal in `Ag := Q ⊔ Zc` (again since `Zc` is central) and, since `[Ag : Q] =
|Zc|` is coprime to `p` (`IsPGroup.toSylow`), `Q` -- viewed inside `Ag` -- is *the* Sylow
`p`-subgroup of `Ag`; being normal, it is then *characteristic* in `Ag`
(`Sylow.characteristic_of_normal`), i.e. fixed (setwise) by every automorphism of `Ag`, in
particular by the restriction of `conj y` to `Ag` for any `y` normalizing `Ag`. This forces
`y` to normalize `Q` too. -/
theorem normalizer_join_eq_normalizer_of_isPGroup_of_central_of_coprime
    {L : Type*} [Group L] [Finite L] {p : ℕ} [hp : Fact (Nat.Prime p)]
    {Q Zc : Subgroup L} (hQp : IsPGroup p Q) (hQnontriv : Q ≠ ⊥)
    (hZcentral : Zc ≤ center L)
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card Zc)) :
    normalizer ((Q ⊔ Zc : Subgroup L) : Set L) = normalizer (Q : Set L) := by
  haveI hZnormal : Zc.Normal := instNormalLeCenter Zc hZcentral
  apply le_antisymm _ normalizer_le_normalizer_sup_normal
  -- hard direction
  set Ag : Subgroup L := Q ⊔ Zc with hAg_def
  have hQ_le_Ag : Q ≤ Ag := le_sup_left
  have hAg_le_normQ : Ag ≤ normalizer (Q : Set L) := by
    apply sup_le le_normalizer
    intro z hz
    rw [mem_normalizer_iff]
    intro q
    have hcomm : q * z = z * q := (mem_center_iff.mp (hZcentral hz)) q
    have heq : z * q * z⁻¹ = q := by rw [← hcomm, mul_inv_cancel_right]
    rw [heq]
  haveI hQnormal : (Q.subgroupOf Ag).Normal :=
    (normal_subgroupOf_iff_le_normalizer hQ_le_Ag).mpr hAg_le_normQ
  have hdisj : Disjoint Q Zc := Subgroup.disjoint_of_coprime_natCard hcop
  have hcardAg : Nat.card Ag = Nat.card Q * Nat.card Zc :=
    card_sup_eq_of_disjoint_of_normal hdisj
  set Qr : Subgroup Ag := Q.subgroupOf Ag with hQr_def
  have hcard_Qr : Nat.card Qr = Nat.card Q :=
    Nat.card_congr (subgroupOfEquivOfLe hQ_le_Ag).toEquiv
  have hQr_pgroup : IsPGroup p Qr := hQp.comap_subtype
  have hQr_index : Qr.index = Nat.card Zc := by
    have hL := Subgroup.card_mul_index Qr
    rw [hcard_Qr] at hL
    have hL' : Nat.card Q * Qr.index = Nat.card Q * Nat.card Zc := by rw [hL, hcardAg]
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hL'
  have hpQ : p ∣ Nat.card Q := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQp
    rcases Nat.eq_zero_or_pos n with hn0 | hn0
    · exfalso; apply hQnontriv
      rw [← Subgroup.card_eq_one]
      rw [hn, hn0, pow_zero]
    · rw [hn]; exact dvd_pow_self p hn0.ne'
  have hQr_not_dvd_index : ¬ p ∣ Qr.index := by
    rw [hQr_index]
    intro hpdvd
    have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd (hcard_Qr ▸ hpQ) hpdvd
    have h1p := hp.out.one_lt
    have := Nat.le_of_dvd Nat.one_pos hp1
    omega
  set SQ : Sylow p Ag := hQr_pgroup.toSylow hQr_not_dvd_index with hSQ_def
  have hSQ_coe : (SQ : Subgroup Ag) = Qr := IsPGroup.toSylow_coe hQr_pgroup hQr_not_dvd_index
  haveI hSQ_normal : SQ.Normal := by
    show (SQ : Subgroup Ag).Normal
    rw [hSQ_coe]; exact hQnormal
  haveI hfinSylow : Finite (Sylow p Ag) :=
    Finite.of_injective (fun S : Sylow p Ag => (S.toSubgroup : Set Ag))
      (fun _S _T hST => Sylow.ext (SetLike.coe_injective hST))
  haveI := Sylow.characteristic_of_normal SQ hSQ_normal
  -- now conclude
  intro y hy
  rw [mem_normalizer_iff_map_conj_eq] at hy
  rw [mem_normalizer_iff_map_conj_eq]
  have hy' : Ag.map (MulAut.conj y) = Ag := hy
  set f : L →* L := (MulAut.conj y).toMonoidHom with hf_def
  have hfinj : Function.Injective f := (MulAut.conj y).injective
  have hQmap_le_Ag : Q.map f ≤ Ag := hy' ▸ Subgroup.map_mono hQ_le_Ag
  have hcard_Qmap : Nat.card (Q.map f) = Nat.card Q :=
    (Nat.card_congr (Q.equivMapOfInjective f hfinj).toEquiv).symm
  -- generic fact: any p-subgroup `R ≤ Ag` with the same cardinality as `Q` has index coprime `p`.
  have not_dvd_index_of_card_eq : ∀ R : Subgroup L, R ≤ Ag → Nat.card R = Nat.card Q →
      ¬ p ∣ (R.subgroupOf Ag).index := by
    intro R hR_le hR_card hpdvd
    have hcard_Rr : Nat.card (R.subgroupOf Ag) = Nat.card Q := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hR_le).toEquiv]; exact hR_card
    have hL := Subgroup.card_mul_index (R.subgroupOf Ag)
    rw [hcard_Rr] at hL
    have hL' : Nat.card Q * (R.subgroupOf Ag).index = Nat.card Q * Nat.card Zc := by
      rw [hL, hcardAg]
    have hindex_eq : (R.subgroupOf Ag).index = Nat.card Zc :=
      Nat.eq_of_mul_eq_mul_left Nat.card_pos hL'
    rw [hindex_eq] at hpdvd
    have hp1 : p ∣ 1 := hcop ▸ Nat.dvd_gcd (hcard_Qr ▸ hpQ) hpdvd
    have h1p := hp.out.one_lt
    have := Nat.le_of_dvd Nat.one_pos hp1
    omega
  have hQmap_pgroup : IsPGroup p (Q.map f) := hQp.map f
  set Q'r : Subgroup Ag := (Q.map f).subgroupOf Ag with hQ'r_def
  have hQ'r_pgroup : IsPGroup p Q'r := hQmap_pgroup.comap_subtype
  have hQ'r_not_dvd_index : ¬ p ∣ Q'r.index :=
    not_dvd_index_of_card_eq (Q.map f) hQmap_le_Ag hcard_Qmap
  set SQ' : Sylow p Ag := hQ'r_pgroup.toSylow hQ'r_not_dvd_index with hSQ'_def
  have hSQ'_coe : (SQ' : Subgroup Ag) = Q'r := IsPGroup.toSylow_coe hQ'r_pgroup hQ'r_not_dvd_index
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (α := Sylow p Ag) Ag SQ SQ'
  rw [Sylow.smul_eq_of_normal] at hg
  have hQrQ'r : Qr = Q'r := by rw [← hSQ_coe, ← hSQ'_coe, hg]
  have hkey : Q = Q.map f := by
    have := congrArg (Subgroup.map Ag.subtype) hQrQ'r
    rwa [hQr_def, hQ'r_def, map_subgroupOf_eq_of_le hQ_le_Ag,
      map_subgroupOf_eq_of_le hQmap_le_Ag] at this
  exact hkey.symm

/-! #### 5b. The `SL(2,F)`-specific cardinality identity -/

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
variable {p : ℕ} [hp' : Fact (Nat.Prime p)] [CharP F p]

omit [IsAlgClosed F] [DecidableEq F] in
/-- `Nat.card (Z F)` is coprime to `p` (it is `1` if `p = 2` -- since then `-1 = 1` -- and `2`
otherwise, and `2 ≠ p` for an odd prime `p`). -/
theorem coprime_card_Z_prime : Nat.Coprime (Nat.card (Z F)) p := by
  have hp : Nat.Prime p := Fact.out
  by_cases hp2 : p = 2
  · have h2 : (2 : F) = 0 := by
      have hcast : ((p : ℕ) : F) = 0 := CharP.cast_eq_zero F p
      rw [hp2] at hcast; exact_mod_cast hcast
    rw [card_Z_eq_one_of_two_eq_zero h2]
    simp
  · haveI hNeZero : NeZero (2 : F) := by
      constructor
      intro h2
      apply hp2
      have hcast2 : ((2 : ℕ) : F) = (0 : F) := by exact_mod_cast h2
      have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).mp hcast2
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd
    rw [card_Z_eq_two_of_two_ne_zero]
    exact (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)

/--
The analogue of `card_union_conjClasses_coprime_class` for a Sylow-type maximal abelian subgroup
`A = Q ⊔ Z`. This is `card_union_conjClasses_sylow_class` from the original module docstring,
**restated** with three extra hypotheses that turn out to be genuinely needed (not just routine
bookkeeping) for the numeric identity to hold, and which all hold in the intended application
(Theorem 6.8(v-a)/(v-b), `exists_IsCyclic_K_normalizer_eq_Q_join_K`):
* `hQnontriv : Q ≠ ⊥` -- already part of `IsSylowType`'s witness data;
* `hK_le_G : K ≤ G` -- `K ≤ N_G(Q) ≤ G` always;
* `hQK : Disjoint (Q.subgroupOf G) (K.subgroupOf G)` -- `K` is the *complement* to `Q` produced by
  the Schur–Zassenhaus argument underlying `exists_IsCyclic_K_normalizer_eq_Q_join_K`
  (`Subgroup.exists_left_complement'_of_coprime`), which is disjoint from `Q` by construction (an
  `IsComplement'` witness), even though this disjointness is not currently surfaced in that
  lemma's stated conclusion.

Without `hQK`, `|Q ⊔ K|` need not be `|Q| ⋅ |K|` (e.g. if `Q ⊓ K ≠ ⊥`), so the stated identity can
fail; without `hK_le_G`, `Nat.card (K.subgroupOf G)` need not equal `Nat.card K`; without
`hQnontriv`, `p` need not divide `Nat.card Q`, breaking the Sylow-uniqueness argument in
`normalizer_join_eq_normalizer_of_isPGroup_of_central_of_coprime` below.

Proof: `N_G(A) = N_G(Q)` (`normalizer_join_eq_normalizer_of_isPGroup_of_central_of_coprime`,
transporting `A = Q ⊔ Z F` through `Subgroup.subgroupOf G` via `Subgroup.subgroupOf_sup`, with `Z
F`'s image central by direct computation and of order coprime to `p` by `coprime_card_Z_prime`);
combined with `hNG : N_G(Q) = Q ⊔ K` and the disjointness/inclusion hypotheses
(`card_normalizer_join_eq_of_disjoint_of_le`), `|N_G(A)| = |Q| ⋅ |K|`; feeding this into the same
three `S3` bijections used in `card_union_conjClasses_coprime_class`
(`card_ConjClassOf_eq_index_normalizer`, `card_noncenter_ConjClassOfSet_eq_card_ConjClassOfSet`,
`card_noncenter_C_eq_noncenter_MaximalAbelianSubgroup_mul_noncenter_ConjClassOfSet`) together with
Lagrange (`Subgroup.card_mul_index`) gives the stated identity. -/
theorem card_union_conjClasses_sylow_class {G A Q K : Subgroup SL(2,F)} [Finite G]
    (center_le_G : center SL(2,F) ≤ G) (hA : A ∈ MaximalAbelianSubgroupsOf G)
    (S : Sylow p G) (hS : Q.subgroupOf G = S) (hAeq : A = Q ⊔ Z F)
    (hQnontriv : Q ≠ ⊥) (_hK : IsCyclic K) (hK_le_G : K ≤ G)
    (hNG : normalizer (Q.subgroupOf G : Set ↥G) = Q.subgroupOf G ⊔ K.subgroupOf G)
    (hQK : Disjoint (Q.subgroupOf G) (K.subgroupOf G)) :
    Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G
        (⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G ⟨A, hA⟩⟩))
      * (Nat.card Q * Nat.card K)
      = Nat.card (noncenter A : Set SL(2,F)) * Nat.card G := by
  haveI hAfin : Finite A := Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hA.right
  have hZF_le_G : Z F ≤ G := center_SL2_eq_Z F ▸ center_le_G
  have hQ_le_G : Q ≤ G := le_sup_left.trans (hAeq ▸ hA.right)
  set Qg : Subgroup ↥G := Q.subgroupOf G with hQg_def
  set Zg : Subgroup ↥G := (Z F).subgroupOf G with hZg_def
  set Kg : Subgroup ↥G := K.subgroupOf G with hKg_def
  set Ag : Subgroup ↥G := A.subgroupOf G with hAg_def
  have hAg_eq : Ag = Qg ⊔ Zg := by
    rw [hAg_def, hAeq, Subgroup.subgroupOf_sup hQ_le_G hZF_le_G]
  have hQg_pgroup : IsPGroup p Qg := hS ▸ S.isPGroup'
  have hQg_nontriv : Qg ≠ ⊥ := by
    intro hbot
    apply hQnontriv
    have hcard_Qg : Nat.card Qg = Nat.card Q :=
      Nat.card_congr (subgroupOfEquivOfLe hQ_le_G).toEquiv
    rw [hbot] at hcard_Qg
    simp only [Subgroup.card_bot] at hcard_Qg
    exact (Subgroup.card_eq_one).mp hcard_Qg.symm
  have hZg_central : Zg ≤ center (↥G) := by
    intro z hz
    rw [hZg_def, mem_subgroupOf] at hz
    rw [mem_center_iff]
    intro g
    have hz' : (z : SL(2,F)) ∈ center SL(2,F) := by
      rw [center_SL2_eq_Z]; exact hz
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact mem_center_iff.mp hz' (g : SL(2,F))
  have hcard_Zg : Nat.card Zg = Nat.card (Z F) :=
    Nat.card_congr (subgroupOfEquivOfLe hZF_le_G).toEquiv
  have hcop_ZP : Nat.Coprime (Nat.card Zg) p := hcard_Zg ▸ coprime_card_Z_prime
  have hcop : Nat.Coprime (Nat.card Qg) (Nat.card Zg) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQg_pgroup
    rw [hn]
    exact (Nat.Coprime.pow_right n hcop_ZP).symm
  have hnormalizer_eq : normalizer (Ag : Set ↥G) = normalizer (Qg : Set ↥G) := by
    rw [hAg_eq]
    exact normalizer_join_eq_normalizer_of_isPGroup_of_central_of_coprime
      hQg_pgroup hQg_nontriv hZg_central hcop
  have hcard_normalizer : Nat.card (normalizer (Ag : Set ↥G)) = Nat.card Qg * Nat.card Kg := by
    rw [hnormalizer_eq]
    exact card_normalizer_join_eq_of_disjoint_of_le hNG hQK
  have hcard_Qg_eq : Nat.card Qg = Nat.card Q :=
    Nat.card_congr (subgroupOfEquivOfLe hQ_le_G).toEquiv
  have hcard_Kg_eq : Nat.card Kg = Nat.card K :=
    Nat.card_congr (subgroupOfEquivOfLe hK_le_G).toEquiv
  have hcard_normalizer' : Nat.card (normalizer (Ag : Set ↥G)) = Nat.card Q * Nat.card K := by
    rw [hcard_normalizer, hcard_Qg_eq, hcard_Kg_eq]
  have hLagrange : Nat.card (normalizer (Ag : Set ↥G)) * index (normalizer (Ag : Set ↥G))
      = Nat.card G := Subgroup.card_mul_index _
  rw [hcard_normalizer'] at hLagrange
  set Astar : noncenter_MaximalAbelianSubgroupsOf G :=
    ⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G ⟨A, hA⟩⟩ with hAstar_def
  have h1 : Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G Astar)
      = Nat.card (noncenter A : Set SL(2,F)) * card_noncenter_ConjClassOf G Astar :=
    card_noncenter_C_eq_noncenter_MaximalAbelianSubgroup_mul_noncenter_ConjClassOfSet
      G center_le_G Astar
  have h2 : card_noncenter_ConjClassOf G Astar = Nat.card (ConjClassOf G ⟨A, hA⟩) :=
    (card_noncenter_ConjClassOfSet_eq_card_ConjClassOfSet G ⟨A, hA⟩).symm
  have h3 : Nat.card (ConjClassOf G ⟨A, hA⟩) = index (normalizer (Ag : Set ↥G)) :=
    card_ConjClassOf_eq_index_normalizer G ⟨A, hA⟩
  calc Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G Astar)
        * (Nat.card Q * Nat.card K)
      = (Nat.card (noncenter A : Set SL(2,F)) * index (normalizer (Ag : Set ↥G)))
          * (Nat.card Q * Nat.card K) := by rw [h1, h2, h3]
    _ = Nat.card (noncenter A : Set SL(2,F))
          * (Nat.card Q * Nat.card K * index (normalizer (Ag : Set ↥G))) := by ring
    _ = Nat.card (noncenter A : Set SL(2,F)) * Nat.card G := by rw [hLagrange]

/-- The Nat identity `card_union_conjClasses_sylow_class` recast as a single rational-division
equation, in the style of `card_union_conjClasses_coprime_class_rat`:
`|C(A^*)| / |G| = |A^*| / (|Q| \cdot |K|)`. -/
theorem card_union_conjClasses_sylow_class_rat {G A Q K : Subgroup SL(2,F)} [Finite G]
    (center_le_G : center SL(2,F) ≤ G) (hA : A ∈ MaximalAbelianSubgroupsOf G)
    (S : Sylow p G) (hS : Q.subgroupOf G = S.toSubgroup) (hAeq : A = Q ⊔ Z F)
    (hQnontriv : Q ≠ ⊥) (hK : IsCyclic K) (hK_le_G : K ≤ G)
    (hNG : normalizer (Q.subgroupOf G : Set ↥G) = Q.subgroupOf G ⊔ K.subgroupOf G)
    (hQK : Disjoint (Q.subgroupOf G) (K.subgroupOf G)) :
    (Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G
        (⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G ⟨A, hA⟩⟩)) : ℚ)
        / Nat.card G
      = (Nat.card (noncenter A : Set SL(2,F)) : ℚ) / ((Nat.card Q : ℚ) * Nat.card K) := by
  have hnat :=
    card_union_conjClasses_sylow_class center_le_G hA S hS hAeq hQnontriv hK hK_le_G hNG hQK
  have hQ_le_G : Q ≤ G := le_sup_left.trans (hAeq ▸ hA.right)
  haveI : Finite Q := Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hQ_le_G
  have hQpos : 0 < Nat.card Q := Nat.card_pos
  haveI : Finite K := Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hK_le_G
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hcast : (Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G
        (⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G ⟨A, hA⟩⟩)) : ℚ)
        * ((Nat.card Q : ℚ) * Nat.card K)
      = (Nat.card (noncenter A : Set SL(2,F)) : ℚ) * Nat.card G := by exact_mod_cast hnat
  have hQK_ne : ((Nat.card Q : ℚ) * Nat.card K) ≠ 0 := by
    have := Nat.mul_pos hQpos hKpos
    exact_mod_cast this.ne'
  rw [div_eq_div_iff (by exact_mod_cast hGpos.ne') hQK_ne]
  exact hcast

/-! #### 5c. Bridging `exists_IsCyclic_K_normalizer_eq_Q_join_K` (`S2_B`) to `SL(2,F)`-subgroups,
with the disjointness of `Q` and `K` surfaced (needed by `card_union_conjClasses_sylow_class`
above), and the extra fact `Nat.card (center SL(2,F)) ∣ Nat.card K` needed for `main_bridge` to
match Butler's `k = |K|/|Z|` notation. -/

/--
A restatement of `exists_IsCyclic_K_normalizer_eq_Q_join_K` (`S2_B`) that additionally exposes
the disjointness of `Q.toSubgroup` and `K` coming from the Schur–Zassenhaus complement
construction underlying it (`Subgroup.exists_left_complement'_of_coprime` produces an
`IsComplement'` witness, which is disjoint by `IsComplement'.disjoint`, but the original
statement only records `IsCyclic K` and the join equation). We reprove it here (rather than
modifying `S2_B`) since the proof is short and self-contained given `S2_B`'s public helper
`isCyclic_normalizer_subgroupOf_quot_of_ne_bot`.
-/
theorem exists_IsCyclic_K_disjoint_normalizer_eq_Q_join_K {G : Subgroup SL(2,F)} [Finite G]
    (S : Sylow p G) (hSne : S.toSubgroup ≠ ⊥) :
    ∃ K : Subgroup ↥G, IsCyclic K ∧
      normalizer (S.toSubgroup : Set ↥G) = S.toSubgroup ⊔ K ∧ Disjoint (S.toSubgroup) K := by
  have hcard_eq : Nat.card (S.toSubgroup.subgroupOf (normalizer (S.toSubgroup : Set ↥G)))
      = Nat.card S.toSubgroup :=
    Nat.card_congr (subgroupOfEquivOfLe (le_normalizer)).toEquiv
  have hindex_dvd : (S.toSubgroup.subgroupOf (normalizer (S.toSubgroup : Set ↥G))).index
      ∣ S.index :=
    relIndex_dvd_index_of_le (le_normalizer)
  have hcop : Nat.Coprime
      (Nat.card (S.toSubgroup.subgroupOf (normalizer (S.toSubgroup : Set ↥G))))
      (S.toSubgroup.subgroupOf (normalizer (S.toSubgroup : Set ↥G))).index := by
    rw [hcard_eq]
    exact S.card_coprime_index.of_dvd_right hindex_dvd
  obtain ⟨K', hK'⟩ := Subgroup.exists_left_complement'_of_coprime hcop
  refine ⟨K'.map (normalizer (S.toSubgroup : Set ↥G)).subtype, ?_, ?_, ?_⟩
  · have equivKQuot : (↥(normalizer (S.toSubgroup : Set ↥G))
        ⧸ (S.toSubgroup.subgroupOf (normalizer (S.toSubgroup : Set ↥G)))) ≃* K' :=
      hK'.QuotientMulEquiv
    haveI : IsCyclic K' :=
      (MulEquiv.isCyclic equivKQuot).mp
        (isCyclic_normalizer_subgroupOf_quot_of_ne_bot G S hSne)
    exact (MulEquiv.isCyclic
      (K'.equivMapOfInjective (normalizer (S.toSubgroup : Set ↥G)).subtype
        (Subgroup.subtype_injective _))).mp inferInstance
  · have hsup : K' ⊔ (S.toSubgroup.subgroupOf (normalizer (S.toSubgroup : Set ↥G))) = ⊤ :=
      hK'.sup_eq_top
    have hmap := congrArg (Subgroup.map (normalizer (S.toSubgroup : Set ↥G)).subtype) hsup
    rw [Subgroup.map_sup, subgroupOf_map_subtype, inf_eq_left.mpr le_normalizer,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at hmap
    rw [sup_comm]
    exact hmap.symm
  · have hdisj : Disjoint K' (S.toSubgroup.subgroupOf (normalizer (S.toSubgroup : Set ↥G))) :=
      hK'.disjoint
    have hmapdisj := Subgroup.disjoint_map (Subgroup.subtype_injective _) hdisj.symm
    rwa [map_subgroupOf_eq_of_le le_normalizer] at hmapdisj

/--
Packages a Sylow `p`-subgroup `S` of `G` (nontrivial) into the `SL(2,F)`-subgroup data `Q, K`
needed by `card_union_conjClasses_sylow_class`, together with the extra fact
`Nat.card (center SL(2,F)) ∣ Nat.card K` (needed to match Butler's `k = |K|/|Z|`): `Q` is the
image of `S` and `K` the image of the cyclic complement from
`exists_IsCyclic_K_disjoint_normalizer_eq_Q_join_K`, both pushed up to `SL(2,F)`-subgroups via
`Subgroup.map G.subtype` (so that `Q.subgroupOf G = S.toSubgroup` and `K.subgroupOf G = K'`
*exactly*, not just up to isomorphism, by `Subgroup.comap_map_eq_self_of_injective`).

The divisibility `|Z| ∣ |K|` is proved without needing to know anything more about `K` beyond
the join/disjointness data: since `Z.subgroupOf G` is central (hence normalizes `Q.subgroupOf G`)
and disjoint from it (coprime orders), `card_sup_eq_of_disjoint_of_le_normalizer` gives
`|Z ⊔ Q| = |Z| * |Q|`; since `Z ⊔ Q ≤ N_G(Q) = Q ⊔ K` (with `|N_G(Q)| = |Q| * |K|` by
`card_normalizer_join_eq_of_disjoint_of_le`), Lagrange gives `|Z| * |Q| ∣ |Q| * |K|`, and
cancelling `|Q| ≠ 0` gives `|Z| ∣ |K|`.
-/
theorem sylow_class_data {G : Subgroup SL(2,F)} [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (S : Sylow p G) (hSne : S.toSubgroup ≠ ⊥) :
    ∃ Q K : Subgroup SL(2,F), Q ≤ G ∧ Q.subgroupOf G = S.toSubgroup ∧ K ≤ G ∧ IsCyclic K ∧
      normalizer (Q.subgroupOf G : Set ↥G) = Q.subgroupOf G ⊔ K.subgroupOf G ∧
      Disjoint (Q.subgroupOf G) (K.subgroupOf G) ∧
      Nat.card (center SL(2,F)) ∣ Nat.card K := by
  obtain ⟨K', hK'cyc, hK'NG, hK'disj⟩ := exists_IsCyclic_K_disjoint_normalizer_eq_Q_join_K S hSne
  set Q : Subgroup SL(2,F) := S.toSubgroup.map G.subtype with hQ_def
  set K : Subgroup SL(2,F) := K'.map G.subtype with hK_def
  have hQ_le_G : Q ≤ G := Subgroup.map_subtype_le S.toSubgroup
  have hQ_subgroupOf : Q.subgroupOf G = S.toSubgroup :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective G) S.toSubgroup
  have hK_le_G : K ≤ G := Subgroup.map_subtype_le K'
  have hK_subgroupOf : K.subgroupOf G = K' :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective G) K'
  refine ⟨Q, K, hQ_le_G, hQ_subgroupOf, hK_le_G, ?_, ?_, ?_, ?_⟩
  · exact (MulEquiv.isCyclic
      (K'.equivMapOfInjective G.subtype (Subgroup.subtype_injective G))).mp hK'cyc
  · rw [hQ_subgroupOf, hK_subgroupOf]; exact hK'NG
  · rw [hQ_subgroupOf, hK_subgroupOf]; exact hK'disj
  · have hZF_le_G : Z F ≤ G := center_SL2_eq_Z F ▸ center_le_G
    set Zg : Subgroup ↥G := (Z F).subgroupOf G with hZg_def
    have hZg_central : Zg ≤ center (↥G) := by
      intro z hz
      rw [hZg_def, mem_subgroupOf] at hz
      rw [mem_center_iff]
      intro g
      have hz' : (z : SL(2,F)) ∈ center SL(2,F) := by
        rw [center_SL2_eq_Z]; exact hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact mem_center_iff.mp hz' (g : SL(2,F))
    have hZg_le_normalizerQ : Zg ≤ normalizer (Q.subgroupOf G : Set ↥G) := by
      intro z hz
      rw [mem_normalizer_iff]
      intro q
      have hcomm : (z : ↥G) * q = q * z := (mem_center_iff.mp (hZg_central hz) q).symm
      have heq : (z : ↥G) * q * z⁻¹ = q := by rw [hcomm, mul_inv_cancel_right]
      rw [heq]
    have hQg_pgroup : IsPGroup p (Q.subgroupOf G) := hQ_subgroupOf ▸ S.isPGroup'
    have hcard_Zg : Nat.card Zg = Nat.card (Z F) :=
      Nat.card_congr (subgroupOfEquivOfLe hZF_le_G).toEquiv
    have hcop_ZP : Nat.Coprime (Nat.card Zg) p := hcard_Zg ▸ coprime_card_Z_prime
    have hcop : Nat.Coprime (Nat.card (Q.subgroupOf G)) (Nat.card Zg) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQg_pgroup
      rw [hn]
      exact (Nat.Coprime.pow_right n hcop_ZP).symm
    have hdisj_ZQ : Disjoint Zg (Q.subgroupOf G) :=
      (Subgroup.disjoint_of_coprime_natCard hcop).symm
    have hcard_sup : Nat.card ((Zg ⊔ Q.subgroupOf G : Subgroup ↥G))
        = Nat.card Zg * Nat.card (Q.subgroupOf G) :=
      card_sup_eq_of_disjoint_of_le_normalizer hZg_le_normalizerQ hdisj_ZQ
    have hsup_le : (Zg ⊔ Q.subgroupOf G : Subgroup ↥G) ≤ normalizer (Q.subgroupOf G : Set ↥G) :=
      sup_le hZg_le_normalizerQ le_normalizer
    have hdvd1 : Nat.card ((Zg ⊔ Q.subgroupOf G : Subgroup ↥G))
        ∣ Nat.card (normalizer (Q.subgroupOf G : Set ↥G)) :=
      Subgroup.card_dvd_of_le hsup_le
    have hcard_normalizer : Nat.card (normalizer (Q.subgroupOf G : Set ↥G))
        = Nat.card (Q.subgroupOf G) * Nat.card (K.subgroupOf G) := by
      rw [hQ_subgroupOf, hK_subgroupOf]
      exact card_normalizer_join_eq_of_disjoint_of_le hK'NG hK'disj
    rw [hcard_sup, hcard_normalizer, mul_comm (Nat.card Zg) (Nat.card (Q.subgroupOf G))] at hdvd1
    have hQpos : 0 < Nat.card (Q.subgroupOf G) := Nat.card_pos
    have hdvd2 : Nat.card Zg ∣ Nat.card (K.subgroupOf G) :=
      (mul_dvd_mul_iff_left hQpos.ne').mp hdvd1
    have hcard_Kg : Nat.card (K.subgroupOf G) = Nat.card K :=
      Nat.card_congr (subgroupOfEquivOfLe hK_le_G).toEquiv
    rw [hcard_Zg, hcard_Kg] at hdvd2
    rwa [center_SL2_eq_Z]

omit [IsAlgClosed F] [DecidableEq F] in
/-- For a Sylow-type maximal abelian subgroup `A = Q ⊔ Z F` with `Q.subgroupOf G` the Sylow
`p`-subgroup witnessed by `S`: `|A| = |Q| \cdot |Z|`. Used in `main_bridge` to compute
`|A^*| = |A| - |Z| = |Z| \cdot (|Q| - 1)`, matching the `(q-1)` numerator of the `(q-1)/(qk)` term
of `CaseArithmetic.ClassEquation`. -/
theorem card_eq_card_Q_mul_card_Z_of_isSylowType {G Q A : Subgroup SL(2,F)} [Finite G]
    (center_le_G : center SL(2,F) ≤ G)
    (S : Sylow p G) (hS : Q.subgroupOf G = S.toSubgroup) (hQ_le_G : Q ≤ G)
    (hAeq : A = Q ⊔ Z F) :
    Nat.card A = Nat.card Q * Nat.card (Z F) := by
  have hZF_le_G : Z F ≤ G := center_SL2_eq_Z F ▸ center_le_G
  have hA_le_G : A ≤ G := hAeq ▸ sup_le hQ_le_G hZF_le_G
  set Qg : Subgroup ↥G := Q.subgroupOf G with hQg_def
  set Zg : Subgroup ↥G := (Z F).subgroupOf G with hZg_def
  have hQg_pgroup : IsPGroup p Qg := hS ▸ S.isPGroup'
  have hZg_central : Zg ≤ center (↥G) := by
    intro z hz
    rw [hZg_def, mem_subgroupOf] at hz
    rw [mem_center_iff]
    intro g
    have hz' : (z : SL(2,F)) ∈ center SL(2,F) := by rw [center_SL2_eq_Z]; exact hz
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact mem_center_iff.mp hz' (g : SL(2,F))
  haveI hZg_normal : Zg.Normal := instNormalLeCenter Zg hZg_central
  have hcard_Zg : Nat.card Zg = Nat.card (Z F) :=
    Nat.card_congr (subgroupOfEquivOfLe hZF_le_G).toEquiv
  have hcop_ZP : Nat.Coprime (Nat.card Zg) p := hcard_Zg ▸ coprime_card_Z_prime
  have hcop : Nat.Coprime (Nat.card Qg) (Nat.card Zg) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQg_pgroup
    rw [hn]
    exact (Nat.Coprime.pow_right n hcop_ZP).symm
  have hdisj : Disjoint Qg Zg := Subgroup.disjoint_of_coprime_natCard hcop
  have hcard_sup : Nat.card ((Qg ⊔ Zg : Subgroup ↥G)) = Nat.card Qg * Nat.card Zg :=
    card_sup_eq_of_disjoint_of_normal hdisj
  have hAg_eq : A.subgroupOf G = Qg ⊔ Zg := by
    rw [hAeq, Subgroup.subgroupOf_sup hQ_le_G hZF_le_G]
  have hcard_A : Nat.card (A.subgroupOf G) = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hA_le_G).toEquiv
  have hcard_Qg : Nat.card Qg = Nat.card Q :=
    Nat.card_congr (subgroupOfEquivOfLe hQ_le_G).toEquiv
  rw [← hcard_A, hAg_eq, hcard_sup, hcard_Qg, hcard_Zg]

end SylowClassCard

/-! ### 6. The main bridge: assembling a `CaseArithmetic.ClassEquation`

`main_bridge` constructs Butler's numeric data `g, q, k, s, t, gs, gt` from a finite
`G ≤ SL(2,F)` (with `center SL(2,F) ≤ G` and `G ≠ center SL(2,F)`) and proves the equation, by
assembling the taxonomy/cardinality lemmas above with `S3`'s
`card_noncenter_fin_subgroup_eq_sum_card_noncenter_mul_index_normalizer`; feeding the result into
`CaseArithmetic.case_enumeration` recovers Butler's 6-case split (tex ~1206-1270). See its
docstring for the construction. -/

section MainBridge

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
variable {p : ℕ} [Fact (Nat.Prime p)] [CharP F p]

/--
**Witness-carrying companion to `main_bridge`.** `main_bridge` only exports the *numerals*
`g, q, k, s, t, gs, gt` of Butler's class equation; but Butler's own case-by-case proofs (Ch7,
`case_I` ... `case_VI`) need the actual *subgroups* those numerals count -- the per-class
representatives `As i`/`At i` for the two families of coprime-type conjugacy classes, and (when
a Sylow-type class exists, i.e. `q ≠ 1`) the actual Sylow `p`-subgroup and Schur–Zassenhaus
complement realizing `q`/`k` -- so that facts like `IsCyclic`/`Normal`/coprimality can be attached
to a concrete subgroup rather than a bare number. `exists_bridgeData` below produces exactly this
data; `main_bridge` is recovered from it by discarding the witnesses (projecting to the numerals).

The Sylow/complement data is guarded by the disjunction `hSylow : (q = 1 ∧ k = 1) ∨ (...)` rather
than being unconditionally present, matching *exactly* `main_bridge`'s own case split on whether
a Sylow-type conjugacy class exists (`Sfin.card = 0` vs. `= 1`, see its construction below): in
the `q = 1` branch there is no witness Sylow subgroup to attach `k` to -- Butler's numeral `k` is
a free, contentless placeholder there, since `(q-1)/(qk) = 0` regardless of `k` once `q = 1` -- so
we honestly assert only the numeric `q = 1 ∧ k = 1` (exactly what `main_bridge` proves in that
branch) rather than fabricating a spurious witness subgroup for it (e.g. asserting `IsCyclic K`
for `K := ⊤`/`G` itself would beg the very question -- "is `G` cyclic when `p ∤ |G|`?" -- that
Butler's Case Ia is trying to prove; see `Ch7`'s `case_I` docstring for why this is not otherwise
available). In the `q ≠ 1` branch, `Q, K : Subgroup SL(2,F)` are genuine subgroups of `G`
(`Q ≤ G`, `K ≤ G`) with `Q.subgroupOf G` equal to the toSubgroup of an actual `S : Sylow p G`
(matching the shape Ch7's `case_I` expects for its own `Q : Sylow p G` parameter) and `K` cyclic,
disjoint from `Q`, with `N_G(Q) = Q ⊔ K` and `Nat.card K = Nat.card (center SL(2,F)) * k` exactly
(not just up to divisibility, unlike `sylow_class_data`'s bare conclusion). -/
structure BridgeData (p : ℕ) (F : Type*) [Field F] [IsAlgClosed F] [DecidableEq F]
    [Fact (Nat.Prime p)] [CharP F p] (G : Subgroup SL(2,F)) where
  /-- `g := Nat.card G / Nat.card (center SL(2,F))`. -/
  g : ℕ
  /-- `q := Nat.card Q` for the (unique, if it exists) Sylow-type witness `Q`; `1` if none. -/
  q : ℕ
  /-- `k := Nat.card K / Nat.card (center SL(2,F))` for the Sylow-type witness `K`; `1` if none. -/
  k : ℕ
  /-- number of coprime-type conjugacy classes with normalizer index `1`. -/
  s : ℕ
  /-- number of coprime-type conjugacy classes with normalizer index `2`. -/
  t : ℕ
  /-- `gs i := Nat.card (As i) / Nat.card (center SL(2,F))`. -/
  gs : Fin s → ℕ
  /-- `gt i := Nat.card (At i) / Nat.card (center SL(2,F))`. -/
  gt : Fin t → ℕ
  /-- the `s` representative cyclic maximal abelian subgroups of normalizer index `1`. -/
  As : Fin s → Subgroup SL(2,F)
  /-- the `t` representative cyclic maximal abelian subgroups of normalizer index `2`. -/
  At : Fin t → Subgroup SL(2,F)
  hAs_mem : ∀ i, As i ∈ MaximalAbelianSubgroupsOf G
  hAt_mem : ∀ i, At i ∈ MaximalAbelianSubgroupsOf G
  hAs_card : ∀ i, Nat.card (As i) = Nat.card (center SL(2,F)) * gs i
  hAt_card : ∀ i, Nat.card (At i) = Nat.card (center SL(2,F)) * gt i
  hAs_relIndex : ∀ i, relIndex ((As i).subgroupOf G)
      (normalizer (((As i).subgroupOf G) : Set ↥G)) = 1
  hAt_relIndex : ∀ i, relIndex ((At i).subgroupOf G)
      (normalizer (((At i).subgroupOf G) : Set ↥G)) = 2
  hg : Nat.card G = Nat.card (center SL(2,F)) * g
  /-- either there is no Sylow-type class (`q = k = 1`, a contentless placeholder), or `Q, K`
  are genuine witness subgroups of `G` realizing `q, k` exactly. -/
  hSylow : (q = 1 ∧ k = 1) ∨
    (∃ (Q K : Subgroup SL(2,F)) (S : Sylow p G), Q ≤ G ∧ Q.subgroupOf G = S.toSubgroup ∧
      Q.subgroupOf G ≠ ⊥ ∧ Nat.card Q = q ∧ K ≤ G ∧ IsCyclic K ∧
      normalizer (Q.subgroupOf G : Set ↥G) = Q.subgroupOf G ⊔ K.subgroupOf G ∧
      Disjoint (Q.subgroupOf G) (K.subgroupOf G) ∧
      Nat.card K = Nat.card (center SL(2,F)) * k)
  hg_pos : 1 ≤ g
  hq_pos : 1 ≤ q
  hk_pos : 1 ≤ k
  hgs_ge : ∀ i, 2 ≤ gs i
  hgt_ge : ∀ i, 2 ≤ gt i
  heq : CaseArithmetic.ClassEquation g q k gs gt

/--
RESTATED+PROVED (justification: the original statement needed `hp2 : p ≠ 2` for the
`{1,2}`-dichotomy of `relIndex_normalizer_le_two`, Butler handling `p = 2` separately in Ch7):
from a finite `G ≤ SL(2,F)` containing the center and strictly larger than it, produce Butler's
numeric data `g, q, k` and the two families of cyclic-class sizes `gs : Fin s → ℕ`,
`gt : Fin t → ℕ` (`s` = number of coprime-type conjugacy classes with `[N_G(Aᵢ):Aᵢ] = 1`, `t` =
number with `[N_G(Aᵢ):Aᵢ] = 2`), *together with the actual witness subgroups realizing them*
(`BridgeData`, see its docstring), and a proof of `CaseArithmetic.ClassEquation g q k gs gt`.
Feeding the numerals into `CaseArithmetic.case_enumeration` recovers Butler's 6-case split (tex
~1206-1270); `main_bridge` below is the numerals-only corollary.

Construction: `e := Nat.card (center SL(2,F))` divides `Nat.card G` and every maximal abelian
subgroup's cardinality (Lagrange, `center_le`); `g := Nat.card G / e`. Every noncentral maximal
abelian conjugacy class (`Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G)`, a Fintype) is
classified, via a chosen representative and `isCoprimeType_or_isSylowType`, as coprime-type
(`Cfin`) or Sylow-type (`Sfin`, of cardinality `≤ 1` by `isSylowType_conj_of_isSylowType`); `Cfin`
is further split by normalizer-index (`relIndex_normalizer_le_two` gives the `{1,2}`-dichotomy)
into `S1fin`/`S2fin` of cardinalities `s`/`t`, reindexed via `Finset.equivFin` to give
`As`/`At` (the chosen class representatives) and `gs`/`gt := Nat.card Aᵢ / e`. If `Sfin` is empty,
`q := 1, k := 1` (`hSylow`'s left disjunct, no witness needed); otherwise (`Sfin = {cls₀}`) `Q, K`
come from `sylow_class_data`, `q := Nat.card Q`, `k := Nat.card K / e` (`hSylow`'s right
disjunct). The equation is assembled by dividing
`S3.card_noncenter_fin_subgroup_eq_sum_card_noncenter_mul_index_normalizer` through by
`Nat.card G`, using `card_noncenter_add_card_center_eq_card'` for the `1/g` term,
`card_union_conjClasses_coprime_class_rat` for each `S1fin`/`S2fin` term, and
`card_union_conjClasses_sylow_class_rat` together with `card_eq_card_Q_mul_card_Z_of_isSylowType`
for the (at most one) Sylow term.

Stated as `Nonempty (BridgeData p F G)` rather than a bare `BridgeData p F G` term: the
construction below repeatedly destructures existentials (`IsSylowType`, `sylow_class_data`,
`Finset.card_eq_one`, ...) whose witnesses are genuine data (subgroups, `Sylow` structures), and
Lean's recursor for `Exists`/`Or` can only eliminate into `Prop` (`Exists.casesOn`/`Or.casesOn`
"large elimination" is disallowed) -- so those `obtain`/`rcases` steps require a `Prop`-valued
goal to typecheck. `Nonempty` is itself a `Prop`, so keeping the goal `Nonempty (BridgeData p F
G)` throughout keeps every such step legal; the actual `BridgeData` *term* is assembled at the
very end from the (by then already-destructured, ordinary local) witnesses and wrapped in
`Nonempty.intro`. -/
theorem exists_bridgeData (G : Subgroup SL(2,F)) [Finite G] (hp2 : p ≠ 2)
    (center_le_G : center SL(2,F) ≤ G) (hG_ne : G ≠ center SL(2,F)) :
    Nonempty (BridgeData p F G) := by
  classical
  -- ### `e`, `g`
  set e : ℕ := Nat.card (center SL(2,F)) with he_def
  have hepos : 0 < e := Nat.card_pos
  have heG : e ∣ Nat.card G := Subgroup.card_dvd_of_le center_le_G
  set g : ℕ := Nat.card G / e with hg_def
  have hg_eq : Nat.card G = e * g := (Nat.mul_div_cancel' heG).symm
  have hGpos : 0 < Nat.card G := Nat.card_pos
  have hgpos : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h0 | h0
    · rw [h0, mul_zero] at hg_eq; omega
    · exact h0
  have he_div_g : (e : ℚ) / (Nat.card G : ℚ) = 1 / (g : ℚ) := by
    have hcast : (Nat.card G : ℚ) = (e : ℚ) * (g : ℚ) := by exact_mod_cast hg_eq
    have hene : (e : ℚ) ≠ 0 := by exact_mod_cast hepos.ne'
    rw [hcast, div_mul_eq_div_div, div_self hene]
  -- ### per-class data
  let ι := Quotient (lift_noncenter_MaximalAbelianSubgroupsOf G)
  let A : ι → Subgroup SL(2,F) := fun cls =>
    (cls.out : noncenter_MaximalAbelianSubgroupsOf G).prop.choose
  have hA_mem : ∀ cls : ι, A cls ∈ MaximalAbelianSubgroupsOf G :=
    fun cls => (cls.out : noncenter_MaximalAbelianSubgroupsOf G).prop.choose_spec.1
  have hA_eq : ∀ cls : ι,
      noncenter (A cls) = (cls.out : noncenter_MaximalAbelianSubgroupsOf G).val :=
    fun cls => (cls.out : noncenter_MaximalAbelianSubgroupsOf G).prop.choose_spec.2
  have hA_le_G : ∀ cls : ι, A cls ≤ G := fun cls => (hA_mem cls).right
  have hA_fin : ∀ cls : ι, Finite (A cls) := fun cls =>
    Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) (hA_le_G cls)
  have hA_ne_center : ∀ cls : ι, A cls ≠ center SL(2,F) := fun cls hEq =>
    center_not_mem_of_center_ne hG_ne.symm (hEq ▸ hA_mem cls)
  have hf_eq : ∀ cls : ι, lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls
      = union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G cls.out := by
    intro cls
    induction cls using Quotient.inductionOn with
    | h B =>
      show union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G B
          = union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G
              (Quotient.mk (lift_noncenter_MaximalAbelianSubgroupsOf G) B).out
      have hrel : (Quotient.mk (lift_noncenter_MaximalAbelianSubgroupsOf G) B).out ≈ B :=
        Quotient.exact (Quotient.out_eq _)
      exact (union_conjClasses_noncenter_eq_of_related G _ _ hrel).symm
  have hDichotomy : ∀ cls : ι, IsCoprimeType p (A cls) ∨ IsSylowType p G (A cls) :=
    fun cls => isCoprimeType_or_isSylowType G center_le_G ⟨A cls, hA_mem cls⟩
  have hExcl : ∀ cls : ι, ¬ (IsCoprimeType p (A cls) ∧ IsSylowType p G (A cls)) := by
    intro cls
    haveI := hA_fin cls
    exact not_isCoprimeType_and_isSylowType
  have hSylowUnique : ∀ cls1 cls2 : ι, IsSylowType p G (A cls1) → IsSylowType p G (A cls2) →
      cls1 = cls2 := by
    intro cls1 cls2 h1 h2
    obtain ⟨c, hc, hconj⟩ := isSylowType_conj_of_isSylowType h1 h2
    have hnc : conj c • noncenter (A cls1) = noncenter (A cls2) := by
      rw [← conj_noncenter_eq_noncenter_conj ⟨A cls1, hA_mem cls1⟩, hconj]
    rw [hA_eq cls1, hA_eq cls2] at hnc
    have hrel : cls1.out ≈ cls2.out := ⟨c, hc, hnc⟩
    have heq := Quotient.sound hrel
    rwa [Quotient.out_eq, Quotient.out_eq] at heq
  -- ### `e < |A cls|` and `e ∣ |A cls|`, hence `|A cls| / e ≥ 2`, for every class
  have hcard_gt : ∀ cls : ι, e < Nat.card (A cls) := by
    intro cls
    haveI := hA_fin cls
    have hZ_lt_A : center SL(2,F) < A cls :=
      lt_of_le_of_ne (center_le G (A cls) (hA_mem cls) center_le_G) (hA_ne_center cls).symm
    have hss : (center SL(2,F) : Set SL(2,F)) ⊂ (A cls : Set SL(2,F)) :=
      SetLike.coe_ssubset_coe.mpr hZ_lt_A
    have hlt := Set.ncard_lt_ncard hss (Set.toFinite _)
    rwa [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq] at hlt
  have hdvd_e : ∀ cls : ι, e ∣ Nat.card (A cls) := fun cls =>
    Subgroup.card_dvd_of_le (center_le G (A cls) (hA_mem cls) center_le_G)
  have hge2 : ∀ cls : ι, 2 ≤ Nat.card (A cls) / e := by
    intro cls
    have heqA : Nat.card (A cls) = e * (Nat.card (A cls) / e) :=
      (Nat.mul_div_cancel' (hdvd_e cls)).symm
    have hlt := hcard_gt cls
    by_contra hcon
    push_neg at hcon
    have hm1 : Nat.card (A cls) / e ≤ 1 := by omega
    have : e * (Nat.card (A cls) / e) ≤ e * 1 := Nat.mul_le_mul_left e hm1
    omega
  -- ### relIndex dichotomy for coprime classes
  let δ : ι → ℕ := fun cls =>
    relIndex ((A cls).subgroupOf G) (normalizer (((A cls).subgroupOf G) : Set ↥G))
  have hδ_dichotomy : ∀ cls : ι, IsCoprimeType p (A cls) → δ cls = 1 ∨ δ cls = 2 := by
    intro cls hcop
    haveI := hA_fin cls
    have h1 : 0 < δ cls := (card_pos_and_relIndex_pos (hA_mem cls)).2
    have h2 : δ cls ≤ 2 := relIndex_normalizer_le_two hp2 (A cls) G center_le_G (hA_mem cls) hcop.2
    omega
  -- ### the finsets: `Sfin` (Sylow-type classes), `Cfin` (coprime-type classes), and the
  -- normalizer-index split `S1fin`/`S2fin` of `Cfin`
  let Sfin : Finset ι := Finset.univ.filter (fun cls => IsSylowType p G (A cls))
  let Cfin : Finset ι := Finset.univ.filter (fun cls => IsCoprimeType p (A cls))
  have hSfin_card_le_one : Sfin.card ≤ 1 := by
    by_contra hgt
    push_neg at hgt
    obtain ⟨cls1, h1, cls2, h2, hne⟩ := Finset.one_lt_card.mp hgt
    simp only [Sfin, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact hne (hSylowUnique cls1 cls2 h1 h2)
  have hCS_disjoint : Disjoint Cfin Sfin := by
    rw [Finset.disjoint_left]
    intro cls hC hS
    simp only [Cfin, Finset.mem_filter, Finset.mem_univ, true_and] at hC
    simp only [Sfin, Finset.mem_filter, Finset.mem_univ, true_and] at hS
    exact hExcl cls ⟨hC, hS⟩
  have hCS_union : Cfin ∪ Sfin = Finset.univ := by
    apply Finset.eq_univ_of_forall
    intro cls
    rw [Finset.mem_union]
    simp only [Cfin, Sfin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hDichotomy cls
  let S1fin : Finset ι := Cfin.filter (fun cls => δ cls = 1)
  let S2fin : Finset ι := Cfin.filter (fun cls => δ cls = 2)
  have hS12_disjoint : Disjoint S1fin S2fin := by
    rw [Finset.disjoint_left]
    intro cls h1 h2
    simp only [S1fin, S2fin, Finset.mem_filter] at h1 h2
    omega
  have hS12_union : S1fin ∪ S2fin = Cfin := by
    apply Finset.Subset.antisymm
    · exact Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
    · intro cls hC
      rw [Finset.mem_union]
      simp only [S1fin, S2fin, Finset.mem_filter]
      have hCmem : IsCoprimeType p (A cls) := by
        simpa [Cfin, Finset.mem_filter] using hC
      rcases hδ_dichotomy cls hCmem with h1 | h2
      · left; exact ⟨hC, h1⟩
      · right; exact ⟨hC, h2⟩
  set s : ℕ := S1fin.card with hs_def
  set t : ℕ := S2fin.card with ht_def
  let eS1 : {x // x ∈ S1fin} ≃ Fin s := Finset.equivFin S1fin
  let eS2 : {x // x ∈ S2fin} ≃ Fin t := Finset.equivFin S2fin
  let gs : Fin s → ℕ := fun i => Nat.card (A ((eS1.symm i).val)) / e
  let gt : Fin t → ℕ := fun i => Nat.card (A ((eS2.symm i).val)) / e
  have hgs_ge2 : ∀ i, 2 ≤ gs i := fun i => hge2 _
  have hgt_ge2 : ∀ i, 2 ≤ gt i := fun i => hge2 _
  -- ### the witness subgroups `As i`/`At i` (for `BridgeData`) and their basic properties
  let As : Fin s → Subgroup SL(2,F) := fun i => A ((eS1.symm i).val)
  let At : Fin t → Subgroup SL(2,F) := fun i => A ((eS2.symm i).val)
  have hAs_mem : ∀ i, As i ∈ MaximalAbelianSubgroupsOf G := fun i => hA_mem _
  have hAt_mem : ∀ i, At i ∈ MaximalAbelianSubgroupsOf G := fun i => hA_mem _
  have hAs_card : ∀ i, Nat.card (As i) = e * gs i := fun i =>
    (Nat.mul_div_cancel' (hdvd_e ((eS1.symm i).val))).symm
  have hAt_card : ∀ i, Nat.card (At i) = e * gt i := fun i =>
    (Nat.mul_div_cancel' (hdvd_e ((eS2.symm i).val))).symm
  have hAs_relIndex : ∀ i, relIndex ((As i).subgroupOf G)
      (normalizer (((As i).subgroupOf G) : Set ↥G)) = 1 := fun i =>
    (Finset.mem_filter.mp (eS1.symm i).property).2
  have hAt_relIndex : ∀ i, relIndex ((At i).subgroupOf G)
      (normalizer (((At i).subgroupOf G) : Set ↥G)) = 2 := fun i =>
    (Finset.mem_filter.mp (eS2.symm i).property).2
  -- ### the value, as a rational number, of each coprime-type class's contribution
  have hCterm : ∀ cls : ι, IsCoprimeType p (A cls) →
      (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ) / (Nat.card G : ℚ)
      = (((Nat.card (A cls) / e : ℕ) : ℚ) - 1)
        / ((δ cls : ℚ) * ((Nat.card (A cls) / e : ℕ) : ℚ)) := by
    intro cls hCmem'
    haveI := hA_fin cls
    have hAstar_eq : (⟨noncenter (A cls),
          noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G ⟨A cls, hA_mem cls⟩⟩
        : noncenter_MaximalAbelianSubgroupsOf G) = cls.out := Subtype.ext (hA_eq cls)
    have hrat := card_union_conjClasses_coprime_class_rat center_le_G (hA_mem cls)
    rw [hAstar_eq] at hrat
    rw [hf_eq cls, hrat]
    have heqA : Nat.card (A cls) = e * (Nat.card (A cls) / e) :=
      (Nat.mul_div_cancel' (hdvd_e cls)).symm
    have hadd := card_noncenter_add_card_center_eq_card (hA_mem cls) center_le_G
    have hgi_pos : 0 < Nat.card (A cls) / e := by have := hge2 cls; omega
    have hgi_pos' : (0 : ℚ) < ((Nat.card (A cls) / e : ℕ) : ℚ) := by exact_mod_cast hgi_pos
    have hnc_eq : (Nat.card (noncenter (A cls) : Set SL(2,F)) : ℚ)
        = (e : ℚ) * (((Nat.card (A cls) / e : ℕ) : ℚ) - 1) := by
      have hnat_eq : Nat.card (noncenter (A cls) : Set SL(2,F)) + e
          = e * (Nat.card (A cls) / e) := by rw [← heqA]; exact hadd
      have hQeq : (Nat.card (noncenter (A cls) : Set SL(2,F)) : ℚ) + (e : ℚ)
          = (e : ℚ) * ((Nat.card (A cls) / e : ℕ) : ℚ) := by exact_mod_cast hnat_eq
      linarith
    have heqA' : (Nat.card (A cls) : ℚ) = (e : ℚ) * ((Nat.card (A cls) / e : ℕ) : ℚ) := by
      exact_mod_cast heqA
    rw [hnc_eq, heqA']
    have hδ_rfl : δ cls
        = relIndex ((A cls).subgroupOf G) (normalizer (((A cls).subgroupOf G) : Set ↥G)) := rfl
    have hδpos' : (0 : ℚ) < (δ cls : ℚ) := by
      rcases hδ_dichotomy cls hCmem' with h | h <;> rw [h] <;> norm_num
    rw [hδ_rfl] at hδpos' ⊢
    have hepos' : (0 : ℚ) < (e : ℚ) := by exact_mod_cast hepos
    field_simp [hδpos'.ne']
  -- ### reindexing the `S1fin`/`S2fin` sums into `Fin s`/`Fin t` sums
  have hS1_eq : (∑ cls ∈ S1fin,
        (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
          / (Nat.card G : ℚ))
      = ∑ i : Fin s, ((gs i : ℚ) - 1) / (gs i) := by
    refine Finset.sum_bij' (fun (x : ι) (hx : x ∈ S1fin) => eS1 ⟨x, hx⟩)
      (fun (i : Fin s) (_ : i ∈ (Finset.univ : Finset (Fin s))) => (eS1.symm i).val)
      ?_ ?_ ?_ ?_ ?_
    case refine_1 => intro a ha; exact Finset.mem_univ _
    case refine_2 => intro a ha; exact (eS1.symm a).property
    case refine_3 => intro a ha; exact congrArg Subtype.val (eS1.symm_apply_apply ⟨a, ha⟩)
    case refine_4 => intro a ha; exact Equiv.apply_symm_apply eS1 a
    case refine_5 =>
      intro a ha
      have hmemC : a ∈ Cfin := (Finset.filter_subset _ _) ha
      have hCmem' : IsCoprimeType p (A a) := by simpa [Cfin, Finset.mem_filter] using hmemC
      have hδ1 : δ a = 1 := (Finset.mem_filter.mp ha).2
      have hgs_eq : gs (eS1 ⟨a, ha⟩) = Nat.card (A a) / e := by
        show Nat.card (A ((eS1.symm (eS1 ⟨a, ha⟩)).val)) / e = Nat.card (A a) / e
        rw [Equiv.symm_apply_apply]
      rw [hgs_eq, hCterm a hCmem', hδ1]
      norm_num
  have hS2_eq : (∑ cls ∈ S2fin,
        (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
          / (Nat.card G : ℚ))
      = ∑ i : Fin t, ((gt i : ℚ) - 1) / (2 * (gt i)) := by
    refine Finset.sum_bij' (fun (x : ι) (hx : x ∈ S2fin) => eS2 ⟨x, hx⟩)
      (fun (i : Fin t) (_ : i ∈ (Finset.univ : Finset (Fin t))) => (eS2.symm i).val)
      ?_ ?_ ?_ ?_ ?_
    case refine_1 => intro a ha; exact Finset.mem_univ _
    case refine_2 => intro a ha; exact (eS2.symm a).property
    case refine_3 => intro a ha; exact congrArg Subtype.val (eS2.symm_apply_apply ⟨a, ha⟩)
    case refine_4 => intro a ha; exact Equiv.apply_symm_apply eS2 a
    case refine_5 =>
      intro a ha
      have hmemC : a ∈ Cfin := (Finset.filter_subset _ _) ha
      have hCmem' : IsCoprimeType p (A a) := by simpa [Cfin, Finset.mem_filter] using hmemC
      have hδ2 : δ a = 2 := (Finset.mem_filter.mp ha).2
      have hgt_eq : gt (eS2 ⟨a, ha⟩) = Nat.card (A a) / e := by
        show Nat.card (A ((eS2.symm (eS2 ⟨a, ha⟩)).val)) / e = Nat.card (A a) / e
        rw [Equiv.symm_apply_apply]
      rw [hgt_eq, hCterm a hCmem', hδ2]
      norm_num
  -- ### the master identity: `1 = 1/g + (coprime classes) + (Sylow classes, if any)`
  have hsplitCS : (∑ cls : ι,
        (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ))
      = (∑ cls ∈ Cfin, (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ))
        + (∑ cls ∈ Sfin,
            (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)) := by
    rw [← hCS_union, Finset.sum_union hCS_disjoint]
  have hsplitS12 : (∑ cls ∈ Cfin,
        (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ))
      = (∑ cls ∈ S1fin, (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ))
        + (∑ cls ∈ S2fin,
            (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)) := by
    rw [← hS12_union, Finset.sum_union hS12_disjoint]
  have hStep3 :
      (∑ cls : ι, Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls)) + e
      = Nat.card G := by
    have h1 := card_noncenter_add_card_center_eq_card' (G := G) center_le_G
    have h2 := card_noncenter_fin_subgroup_eq_sum_card_noncenter_mul_index_normalizer G center_le_G
    rw [show (noncenter G : Set SL(2,F)) = G.carrier \ (center SL(2,F)).carrier from rfl] at h1
    rw [h2] at h1
    exact h1
  have hcast : (∑ cls : ι,
        (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)) + (e : ℚ)
      = (Nat.card G : ℚ) := by exact_mod_cast hStep3
  have hGpos' : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast hGpos
  have hdiv_eq : (∑ cls : ι,
        (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ))
          / (Nat.card G : ℚ)
      = 1 - (e : ℚ) / (Nat.card G : ℚ) := by
    rw [eq_sub_iff_add_eq, ← add_div, hcast, div_self hGpos'.ne']
  have hsum_div_eq : (∑ cls : ι,
        (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
          / (Nat.card G : ℚ))
      = 1 - (e : ℚ) / (Nat.card G : ℚ) := by
    rw [Finset.sum_div] at hdiv_eq
    exact hdiv_eq
  have hsum_div : (∑ cls : ι,
        (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
          / (Nat.card G : ℚ))
      = (∑ cls ∈ S1fin,
            (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
              / (Nat.card G : ℚ))
        + (∑ cls ∈ S2fin,
            (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
              / (Nat.card G : ℚ))
        + (∑ cls ∈ Sfin,
            (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
              / (Nat.card G : ℚ)) := by
    have e1 : (∑ cls : ι,
          (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
            / (Nat.card G : ℚ))
        = (∑ cls ∈ Cfin,
              (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
                / (Nat.card G : ℚ))
          + (∑ cls ∈ Sfin,
              (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
                / (Nat.card G : ℚ)) := by
      rw [← hCS_union, Finset.sum_union hCS_disjoint]
    have e2 : (∑ cls ∈ Cfin,
          (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
            / (Nat.card G : ℚ))
        = (∑ cls ∈ S1fin,
              (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
                / (Nat.card G : ℚ))
          + (∑ cls ∈ S2fin,
              (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
                / (Nat.card G : ℚ)) := by
      rw [← hS12_union, Finset.sum_union hS12_disjoint]
    rw [e1, e2]
  have hcombined : (1 : ℚ) - (e : ℚ) / (Nat.card G : ℚ)
      = (∑ cls ∈ S1fin,
            (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
              / (Nat.card G : ℚ))
        + (∑ cls ∈ S2fin,
            (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
              / (Nat.card G : ℚ))
        + (∑ cls ∈ Sfin,
            (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
              / (Nat.card G : ℚ)) := by
    rw [← hsum_div_eq, hsum_div]
  rw [hS1_eq, hS2_eq] at hcombined
  have hmaster : (1 : ℚ) = (e : ℚ) / (Nat.card G : ℚ)
      + (∑ i : Fin s, ((gs i : ℚ) - 1) / (gs i)) + (∑ i : Fin t, ((gt i : ℚ) - 1) / (2 * (gt i)))
      + (∑ cls ∈ Sfin,
          (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
            / (Nat.card G : ℚ)) := by
    linarith [hcombined]
  -- ### case split: does a Sylow-type class exist?
  -- (`by_cases`, not `rcases`/`cases` on a bare `∨`, since the goal `BridgeData p F G` is not a
  -- `Prop`: `Or.casesOn` cannot eliminate into non-`Prop` sorts, but `Decidable.rec` -- underlying
  -- `by_cases` on the decidable proposition `Sfin.card = 0` -- can.)
  by_cases hS0 : Sfin.card = 0
  · -- no Sylow-type class: `q := 1`, `k := 1`
    have hSfin_empty : Sfin = (∅ : Finset ι) := Finset.card_eq_zero.mp hS0
    have heq : CaseArithmetic.ClassEquation g 1 1 gs gt := by
      unfold CaseArithmetic.ClassEquation
      rw [hSfin_empty, Finset.sum_empty, add_zero] at hmaster
      rw [he_div_g] at hmaster
      simpa using hmaster
    exact ⟨⟨g, 1, 1, s, t, gs, gt, As, At, hAs_mem, hAt_mem, hAs_card, hAt_card,
      hAs_relIndex, hAt_relIndex, hg_eq, Or.inl ⟨rfl, rfl⟩, hgpos, le_refl 1, le_refl 1,
      hgs_ge2, hgt_ge2, heq⟩⟩
  · -- the unique Sylow-type class `cls0`
    have hS1 : Sfin.card = 1 := by omega
    obtain ⟨cls0, hSfin_eq⟩ := Finset.card_eq_one.mp hS1
    have hcls0_Sylow : IsSylowType p G (A cls0) := by
      have hmem : cls0 ∈ Sfin := by rw [hSfin_eq]; exact Finset.mem_singleton_self cls0
      simpa [Sfin, Finset.mem_filter] using hmem
    obtain ⟨Qw, hQw_nontriv, hQw_fin, hQw_le_G, hAeq, hQw_elem, S, hS⟩ := hcls0_Sylow
    have hQw_ne_bot : Qw ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot Qw).mp hQw_nontriv
    have hSne : S.toSubgroup ≠ ⊥ := by
      rw [← hS]
      intro hbot
      apply hQw_ne_bot
      have h2 := congrArg (Subgroup.map G.subtype) hbot
      rwa [map_subgroupOf_eq_of_le hQw_le_G, Subgroup.map_bot] at h2
    obtain ⟨Q, K, hQ_le_G, hQ_subgroupOf, hK_le_G, hK_cyc, hNG, hQK, hZK_dvd⟩ :=
      sylow_class_data center_le_G S hSne
    have hQeq : Q = Qw := by
      have h1 : Q.subgroupOf G = Qw.subgroupOf G := hQ_subgroupOf.trans hS.symm
      have h2 := congrArg (Subgroup.map G.subtype) h1
      rwa [map_subgroupOf_eq_of_le hQ_le_G, map_subgroupOf_eq_of_le hQw_le_G] at h2
    subst hQeq
    set q : ℕ := Nat.card Q with hq_def
    set k : ℕ := Nat.card K / e with hk_def
    have hqpos : 1 ≤ q := Nat.card_pos
    have hk_eq : Nat.card K = e * k := (Nat.mul_div_cancel' hZK_dvd).symm
    haveI hK_fin : Finite K := Set.Finite.subset (Set.toFinite (G : Set SL(2,F))) hK_le_G
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hkpos : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · exfalso; rw [h0, mul_zero] at hk_eq; omega
      · exact h0
    have hQsg_ne_bot : Q.subgroupOf G ≠ ⊥ := by rw [hQ_subgroupOf]; exact hSne
    have heq2 : CaseArithmetic.ClassEquation g q k gs gt := by
      unfold CaseArithmetic.ClassEquation
      -- compute the (unique) Sylow class's contribution
      have hAmem0 : A cls0 ∈ MaximalAbelianSubgroupsOf G := hA_mem cls0
      have hSylowrat := card_union_conjClasses_sylow_class_rat (A := A cls0) (Q := Q) (K := K)
        center_le_G hAmem0 S hQ_subgroupOf hAeq hQw_ne_bot hK_cyc hK_le_G hNG hQK
      have hAstar_eq0 : (⟨noncenter (A cls0),
            noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G ⟨A cls0, hAmem0⟩⟩
          : noncenter_MaximalAbelianSubgroupsOf G) = cls0.out := Subtype.ext (hA_eq cls0)
      rw [hAstar_eq0, ← hf_eq cls0] at hSylowrat
      have hcardA0 : Nat.card (A cls0) = Nat.card Q * Nat.card (Z F) :=
        card_eq_card_Q_mul_card_Z_of_isSylowType center_le_G S hQ_subgroupOf hQ_le_G hAeq
      have hcard_ZF : Nat.card (Z F) = e := by rw [← center_SL2_eq_Z]
      have hnc0 := card_noncenter_add_card_center_eq_card hAmem0 center_le_G
      have hqpos' : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hqpos
      have hkpos' : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hkpos
      have hepos' : (0 : ℚ) < (e : ℚ) := by exact_mod_cast hepos
      have hGpos' : (0 : ℚ) < (Nat.card G : ℚ) := by exact_mod_cast hGpos
      have hnc0_eq : (Nat.card (noncenter (A cls0) : Set SL(2,F)) : ℚ)
          = (e : ℚ) * ((q : ℚ) - 1) := by
        have hnat_eq : Nat.card (noncenter (A cls0) : Set SL(2,F)) + e
            = Nat.card Q * Nat.card (Z F) := by rw [hcardA0] at hnc0; exact hnc0
        rw [hcard_ZF] at hnat_eq
        have hQeq' : (Nat.card (noncenter (A cls0) : Set SL(2,F)) : ℚ) + (e : ℚ)
            = (q : ℚ) * (e : ℚ) := by exact_mod_cast hnat_eq
        linarith
      have hK_ne : (Nat.card K : ℚ) = (e : ℚ) * (k : ℚ) := by exact_mod_cast hk_eq
      have hfinal : (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls0) : ℚ)
          / (Nat.card G : ℚ) = ((q : ℚ) - 1) / ((q : ℚ) * (k : ℚ)) := by
        rw [hSylowrat, hnc0_eq, hK_ne, show (Nat.card Q : ℚ) = (q : ℚ) from rfl]
        field_simp
      have hSfin_singleton_sum : (∑ cls ∈ Sfin,
            (Nat.card (lift_union_conj_noncenter_MaximalAbelianSubgroupsOf G cls) : ℚ)
              / (Nat.card G : ℚ))
          = ((q : ℚ) - 1) / ((q : ℚ) * (k : ℚ)) := by
        rw [hSfin_eq, Finset.sum_singleton, hfinal]
      -- assemble
      rw [hSfin_singleton_sum, he_div_g] at hmaster
      linarith [hmaster]
    exact ⟨⟨g, q, k, s, t, gs, gt, As, At, hAs_mem, hAt_mem, hAs_card, hAt_card,
      hAs_relIndex, hAt_relIndex, hg_eq,
      Or.inr ⟨Q, K, S, hQ_le_G, hQ_subgroupOf, hQsg_ne_bot, hq_def.symm, hK_le_G, hK_cyc,
        hNG, hQK, hk_eq⟩,
      hgpos, hqpos, hkpos, hgs_ge2, hgt_ge2, heq2⟩⟩

/--
RESTATED+PROVED (justification: as above, `hp2 : p ≠ 2` is needed for the `{1,2}`-dichotomy of
`relIndex_normalizer_le_two`, Butler handling `p = 2` separately in Ch7): the numerals-only
corollary of `exists_bridgeData`, discarding its witness subgroups. This is the statement used by
`CaseArithmetic.case_enumeration` to recover Butler's 6-case split (tex ~1206-1270); see
`exists_bridgeData` for the construction and for the witness subgroups themselves. -/
theorem main_bridge (G : Subgroup SL(2,F)) [Finite G] (hp2 : p ≠ 2)
    (center_le_G : center SL(2,F) ≤ G) (hG_ne : G ≠ center SL(2,F)) :
    ∃ (g q k s t : ℕ) (gs : Fin s → ℕ) (gt : Fin t → ℕ),
      1 ≤ g ∧ 1 ≤ q ∧ 1 ≤ k ∧ (∀ i, 2 ≤ gs i) ∧ (∀ i, 2 ≤ gt i) ∧
      CaseArithmetic.ClassEquation g q k gs gt := by
  obtain ⟨d⟩ := exists_bridgeData G hp2 center_le_G hG_ne
  exact ⟨d.g, d.q, d.k, d.s, d.t, d.gs, d.gt, d.hg_pos, d.hq_pos, d.hk_pos, d.hgs_ge, d.hgt_ge,
    d.heq⟩

end MainBridge

end NumericClassEquation
