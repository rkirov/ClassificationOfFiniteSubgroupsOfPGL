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
* For the (unique, if it exists) Sylow-type class, the analogous statement is recorded using
  `normalizer_Sylow_join_center_eq_normalizer_Sylow` and
  `exists_IsCyclic_K_normalizer_eq_Q_join_K` (`S2_B`/`S3`).

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

/-! ### 5. Cardinality of the Sylow-type conjugacy class (Butler ~1150-1180, second half)

STRETCH: the direct analogue of `card_union_conjClasses_coprime_class` for the (unique, by
`isSylowType_conj_of_isSylowType`) Sylow-type class. -/

section SylowClassCard

variable {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
variable {p : ℕ} [Fact (Nat.Prime p)] [CharP F p]

/--
STRETCH (not proved): the analogue of `card_union_conjClasses_coprime_class` for a Sylow-type
maximal abelian subgroup `A = Q ⊔ Z`. The intended proof: `N_G(A) = N_G(Q)`
(`normalizer_noncentral_eq` + `normalizer_Sylow_join_center_eq_normalizer_Sylow`) and (Theorem
6.8(v-a), `exists_IsCyclic_K_normalizer_eq_Q_join_K`) `N_G(Q) = Q ⊔ K` for a cyclic `K` with
`Q ⊓ K = ⊥` (Schur–Zassenhaus complement), so `|N_G(A)| = |Q| \cdot |K|`
(`IsComplement'.card_mul`/Lagrange); feeding this into the same three `S3` bijections used in
`card_union_conjClasses_coprime_class`
(`card_ConjClassOf_eq_index_normalizer`, `card_noncenter_ConjClassOfSet_eq_card_ConjClassOfSet`,
`card_noncenter_C_eq_noncenter_MaximalAbelianSubgroup_mul_noncenter_ConjClassOfSet`) gives the
stated identity. What is missing to complete this is transporting
`normalizer_Sylow_join_center_eq_normalizer_Sylow` (an ambient-`SL(2,F)`-normalizer statement)
through `Subgroup.subgroupOf G` to the in-`G` normalizer that `card_ConjClassOf_eq_index_normalizer`
is stated in terms of; this is routine but not yet formalized. -/
theorem card_union_conjClasses_sylow_class {G A Q K : Subgroup SL(2,F)} [Finite G]
    (center_le_G : center SL(2,F) ≤ G) (hA : A ∈ MaximalAbelianSubgroupsOf G)
    (S : Sylow p G) (hS : Q.subgroupOf G = S) (hAeq : A = Q ⊔ Z F) (hK : IsCyclic K)
    (hNG : normalizer (Q.subgroupOf G : Set ↥G) = Q.subgroupOf G ⊔ K.subgroupOf G) :
    Nat.card (union_conjClasses_noncenter_MaximalAbelianSubgroupsOf G
        (⟨noncenter A, noncenter_mem_noncenter_MaximalAbelianSubgroupsOf G ⟨A, hA⟩⟩))
      * (Nat.card Q * Nat.card K)
      = Nat.card (noncenter A : Set SL(2,F)) * Nat.card G := by
  sorry

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
