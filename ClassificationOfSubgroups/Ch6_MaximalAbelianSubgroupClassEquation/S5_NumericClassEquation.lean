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

Full closure into a single instance of `CaseArithmetic.ClassEquation` is NOT attempted here;
`main_bridge` at the end states the target shape and is left as an honestly-documented
`sorry` (the missing steps -- indexing the finitely many coprime-type classes by `Fin s`/`Fin t`
according to their normalizer index, and matching Butler's `g, q, k` to
`Nat.card G / Nat.card Z`, `Nat.card Q`, `Nat.card K / Nat.card Z` -- are genuinely new
bookkeeping, not just consequences of what is proved so far).
-/
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S3_NoncenterClassEquation
import ClassificationOfSubgroups.Ch6_MaximalAbelianSubgroupClassEquation.S4_CaseArithmetic

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

end SylowClassCard

/-! ### 6. The main bridge (stretch): assembling a `CaseArithmetic.ClassEquation`

STRETCH: this is the target shape feeding into `CaseArithmetic.case_enumeration`; the
bookkeeping needed to actually construct `g, q, k, s, t, gs, gt` and prove the equation from
`S3`'s `card_noncenter_fin_subgroup_eq_sum_card_noncenter_mul_index_normalizer` together with
the taxonomy/cardinality lemmas above is *not* attempted (see the module docstring). -/

section MainBridge

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
variable {p : ℕ} [Fact (Nat.Prime p)] [CharP F p]

/--
STRETCH (not proved): from a finite `G ≤ SL(2,F)` containing the center and strictly larger than
it, produce Butler's numeric data `g, q, k` and the two families of cyclic-class sizes
`gs : Fin s → ℕ`, `gt : Fin t → ℕ` (`s` = number of coprime-type conjugacy classes with
`[N_G(Aᵢ):Aᵢ] = 1`, `t` = number with `[N_G(Aᵢ):Aᵢ] = 2`), together with a proof of
`CaseArithmetic.ClassEquation g q k gs gt`. Feeding this directly into
`CaseArithmetic.case_enumeration` would recover Butler's 6-case split (tex ~1206-1270). The
intended construction: `e := Nat.card (center SL(2,F))` divides `Nat.card G` and every maximal
abelian subgroup's cardinality (Lagrange, since `center SL(2,F) ≤ A` by `center_le`); set
`g := Nat.card G / e`, and for each conjugacy class of a coprime-type `Aᵢ`, `gᵢ := Nat.card Aᵢ / e`
(split into the `s` classes of normalizer-index `1` and the `t` of index `2`); if a Sylow-type
class exists, set `q := Nat.card Q`, `k := Nat.card K / e` (`K` as in
`exists_IsCyclic_K_normalizer_eq_Q_join_K`), otherwise `q := 1`; then divide
`S3.card_noncenter_fin_subgroup_eq_sum_card_noncenter_mul_index_normalizer` through by `e * g`
using `card_noncenter_add_card_center_eq_card`,
`card_union_conjClasses_coprime_class_rat` and `card_union_conjClasses_sylow_class` on each
summand. -/
theorem main_bridge (G : Subgroup SL(2,F)) [Finite G] (center_le_G : center SL(2,F) ≤ G)
    (hG_ne : G ≠ center SL(2,F)) :
    ∃ (g q k s t : ℕ) (gs : Fin s → ℕ) (gt : Fin t → ℕ),
      1 ≤ g ∧ 1 ≤ q ∧ 1 ≤ k ∧ (∀ i, 2 ≤ gs i) ∧ (∀ i, 2 ≤ gt i) ∧
      CaseArithmetic.ClassEquation g q k gs gt := by
  sorry

end MainBridge

end NumericClassEquation
