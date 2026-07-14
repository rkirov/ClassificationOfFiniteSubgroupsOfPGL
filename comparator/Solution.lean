import Mathlib
import Submission

/-!
# Solution — bridge from the repository's main theorem to the challenge statement

Restates `Challenge.lean`'s statement verbatim and discharges it from
`FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod`. The only non-definitional
step is unfolding the repository's `IsElementaryAbelian` (a conjunction of commutativity and
exponent-`p`) into the challenge's plain quantifiers; every other conversion (`PGL`/`PSL`
abbreviations, `Isomorphic := Nonempty (· ≃* ·)`) is definitional.
-/

namespace DicksonChallenge

/-- `PGL(2, K) := GL(2, K) ⧸ Z(GL(2, K))`, the projective general linear group. -/
abbrev PGL2 (K : Type) [Field K] : Type :=
  Matrix.GeneralLinearGroup (Fin 2) K ⧸ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)

/-- `PSL(2, K) := SL(2, K) ⧸ Z(SL(2, K))`, the projective special linear group. -/
abbrev PSL2 (K : Type) [Field K] : Type :=
  Matrix.SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)

theorem dickson_classification_PGL2 (p : ℕ) [Fact (Nat.Prime p)] (hp2 : p ≠ 2)
    (G : Subgroup (PGL2 (AlgebraicClosure (ZMod p)))) [Finite G] :
    IsCyclic G ∨
      (∃ n, Nonempty (G ≃* DihedralGroup n)) ∨
      (∃ Q : Subgroup G,
        ((∀ a b : Q, a * b = b * a) ∧ (∀ h : Q, h ≠ 1 → orderOf h = p)) ∧ Q.Normal ∧
        ∃ K : Subgroup G,
          Subgroup.IsComplement' Q K ∧ IsCyclic K ∧ Nat.Coprime p (Nat.card K)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 5)) ∨
      (∃ k : ℕ+, Nonempty (G ≃* PSL2 (GaloisField p k.val))) ∨
      (∃ k : ℕ+, Nonempty (G ≃* PGL2 (GaloisField p k.val))) := by
  rcases FLT_classification_fin_subgroups_of_PGL2_over_AlgClosure_ZMod (p := p) hp2 G with
    h | h | ⟨Q, hQe, hQn, K, hK⟩ | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inl ⟨Q, ⟨?_, hQe.2⟩, hQn, K, hK⟩))
    intro a b
    exact hQe.1.is_comm.comm a b
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))))

/-!
## Dickson's two `SL₂` theorems — statements restated and discharged from the repository

The following block restates `Challenge.lean`'s two `SL₂` theorems verbatim (with the same
Mathlib-only inline definitions of the binary octahedral group `2O` and the diagonal twist `D`)
and discharges each from the repository's `dicksons_classification_theorem_class_I / _II`.

The only non-trivial glue is:
* the **2O transport** `BinaryOctahedral2O ≃* Ch7GroupRecognition.BinaryOctahedralGroup`: both are
  the same presentation `⟨x, y | x⁴ = y³ = (xy)²⟩` over different two-symbol types, so the transport
  is a pair of `PresentedGroup.toGroup` homomorphisms that are mutually inverse on generators; and
* the **`D`-matrix identification** `D π = SpecialMatrices.d π` (a plain matrix `ext`), which makes
  the challenge's twisted subgroup literally equal to the repository's `SL2_join_d p k π`.
-/

-- The inline `2O` presentation and diagonal twist `D`, *identical* to `Challenge.lean` (so the
-- comparator sees the same statement-level declarations in both environments).
inductive S2O
  | x
  | y

/-- The relators of `2O = ⟨x, y | x⁴ = y³ = (xy)²⟩`. -/
def BinaryOctahedralRelations : Set (FreeGroup S2O) :=
  { FreeGroup.of S2O.x ^ 4 * (FreeGroup.of S2O.y ^ 3)⁻¹ } ∪
  { FreeGroup.of S2O.x ^ 4 * ((FreeGroup.of S2O.x * FreeGroup.of S2O.y) ^ 2)⁻¹ }

/-- The binary octahedral group `2O`, as the group presented by `BinaryOctahedralRelations`. -/
abbrev BinaryOctahedral2O := PresentedGroup BinaryOctahedralRelations

/-- The explicit diagonal element `diag(π, π⁻¹) ∈ SL₂(𝔽_{p^{2k}})` adjoined in Class II item (x). -/
noncomputable def D {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ+} (π : (GaloisField p (2 * k.val))ˣ) :
    Matrix.SpecialLinearGroup (Fin 2) (GaloisField p (2 * k.val)) :=
  ⟨!![(π : GaloisField p (2 * k.val)), 0; 0, (π : GaloisField p (2 * k.val))⁻¹],
    by rw [Matrix.det_fin_two_of]; simp⟩

/-! ### Transport: challenge `2O` ≃* repository `2O` (same relators, renamed symbols) -/

open Ch7GroupRecognition in
/-- Symbol map `S2O → repository-2O`. -/
def sym_fwd : S2O → Ch7GroupRecognition.BinaryOctahedralGroup
  | .x => PresentedGroup.of BinaryOctahedralSymbols.x
  | .y => PresentedGroup.of BinaryOctahedralSymbols.y

/-- Symbol map `repository-2O → S2O`. -/
def sym_bwd : Ch7GroupRecognition.BinaryOctahedralSymbols → BinaryOctahedral2O
  | .x => PresentedGroup.of S2O.x
  | .y => PresentedGroup.of S2O.y

open Ch7GroupRecognition in
theorem hfwd_rels : ∀ r ∈ BinaryOctahedralRelations, FreeGroup.lift sym_fwd r = 1 := by
  intro r hr
  simp only [BinaryOctahedralRelations, Set.mem_union, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · simp only [map_mul, map_pow, map_inv, FreeGroup.lift_apply_of]
    show (PresentedGroup.of BinaryOctahedralSymbols.x : BinaryOctahedralGroup) ^ 4 *
      ((PresentedGroup.of BinaryOctahedralSymbols.y : BinaryOctahedralGroup) ^ 3)⁻¹ = 1
    rw [binaryOctahedral_x_pow_four_eq_y_pow_three, mul_inv_cancel]
  · simp only [map_mul, map_pow, map_inv, FreeGroup.lift_apply_of]
    show (PresentedGroup.of BinaryOctahedralSymbols.x : BinaryOctahedralGroup) ^ 4 *
      ((PresentedGroup.of BinaryOctahedralSymbols.x *
        PresentedGroup.of BinaryOctahedralSymbols.y : BinaryOctahedralGroup) ^ 2)⁻¹ = 1
    rw [binaryOctahedral_x_pow_four_eq_x_mul_y_sq, mul_inv_cancel]

/-- First challenge-side relation `x⁴ = y³`, read off `BinaryOctahedralRelations`. -/
theorem chal_rel1 : (PresentedGroup.of S2O.x : BinaryOctahedral2O) ^ 4 =
    (PresentedGroup.of S2O.y : BinaryOctahedral2O) ^ 3 := by
  have h : PresentedGroup.mk BinaryOctahedralRelations
      (FreeGroup.of S2O.x ^ 4 * (FreeGroup.of S2O.y ^ 3)⁻¹) = 1 :=
    PresentedGroup.one_of_mem (Or.inl rfl)
  rw [map_mul, map_pow, map_inv, map_pow] at h
  exact mul_inv_eq_one.mp h

/-- Second challenge-side relation `x⁴ = (xy)²`, read off `BinaryOctahedralRelations`. -/
theorem chal_rel2 : (PresentedGroup.of S2O.x : BinaryOctahedral2O) ^ 4 =
    (PresentedGroup.of S2O.x * PresentedGroup.of S2O.y : BinaryOctahedral2O) ^ 2 := by
  have h : PresentedGroup.mk BinaryOctahedralRelations
      (FreeGroup.of S2O.x ^ 4 * ((FreeGroup.of S2O.x * FreeGroup.of S2O.y) ^ 2)⁻¹) = 1 :=
    PresentedGroup.one_of_mem (Or.inr rfl)
  rw [map_mul, map_pow, map_inv, map_pow, map_mul] at h
  exact mul_inv_eq_one.mp h

open Ch7GroupRecognition in
theorem hbwd_rels : ∀ r ∈ Ch7GroupRecognition.BinaryOctahedralRelations,
    FreeGroup.lift sym_bwd r = 1 := by
  intro r hr
  simp only [Ch7GroupRecognition.BinaryOctahedralRelations, Set.mem_union,
    Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl
  · simp only [map_mul, map_pow, map_inv, FreeGroup.lift_apply_of]
    show (PresentedGroup.of S2O.x : BinaryOctahedral2O) ^ 4 *
      ((PresentedGroup.of S2O.y : BinaryOctahedral2O) ^ 3)⁻¹ = 1
    rw [chal_rel1, mul_inv_cancel]
  · simp only [map_mul, map_pow, map_inv, FreeGroup.lift_apply_of]
    show (PresentedGroup.of S2O.x : BinaryOctahedral2O) ^ 4 *
      ((PresentedGroup.of S2O.x * PresentedGroup.of S2O.y : BinaryOctahedral2O) ^ 2)⁻¹ = 1
    rw [chal_rel2, mul_inv_cancel]

noncomputable def φ : BinaryOctahedral2O →* Ch7GroupRecognition.BinaryOctahedralGroup :=
  PresentedGroup.toGroup hfwd_rels

noncomputable def ψ : Ch7GroupRecognition.BinaryOctahedralGroup →* BinaryOctahedral2O :=
  PresentedGroup.toGroup hbwd_rels

open Ch7GroupRecognition in
theorem hψφ : ψ.comp φ = MonoidHom.id BinaryOctahedral2O := by
  apply PresentedGroup.ext
  intro s
  cases s with
  | x =>
    show ψ (φ (PresentedGroup.of S2O.x)) = PresentedGroup.of S2O.x
    rw [φ, ψ, PresentedGroup.toGroup.of]
    show ψ (sym_fwd S2O.x) = _
    rw [ψ]; exact PresentedGroup.toGroup.of hbwd_rels
  | y =>
    show ψ (φ (PresentedGroup.of S2O.y)) = PresentedGroup.of S2O.y
    rw [φ, ψ, PresentedGroup.toGroup.of]
    show ψ (sym_fwd S2O.y) = _
    rw [ψ]; exact PresentedGroup.toGroup.of hbwd_rels

open Ch7GroupRecognition in
theorem hφψ : φ.comp ψ = MonoidHom.id Ch7GroupRecognition.BinaryOctahedralGroup := by
  apply PresentedGroup.ext
  intro s
  cases s with
  | x =>
    show φ (ψ (PresentedGroup.of BinaryOctahedralSymbols.x)) =
      PresentedGroup.of BinaryOctahedralSymbols.x
    rw [ψ, φ, PresentedGroup.toGroup.of]
    show φ (sym_bwd BinaryOctahedralSymbols.x) = _
    rw [φ]; exact PresentedGroup.toGroup.of hfwd_rels
  | y =>
    show φ (ψ (PresentedGroup.of BinaryOctahedralSymbols.y)) =
      PresentedGroup.of BinaryOctahedralSymbols.y
    rw [ψ, φ, PresentedGroup.toGroup.of]
    show φ (sym_bwd BinaryOctahedralSymbols.y) = _
    rw [φ]; exact PresentedGroup.toGroup.of hfwd_rels

/-- The transport isomorphism identifying the challenge's inline `2O` with the repository's `2O`. -/
noncomputable def transport2O :
    BinaryOctahedral2O ≃* Ch7GroupRecognition.BinaryOctahedralGroup where
  toFun := φ
  invFun := ψ
  left_inv := fun z => by
    have := DFunLike.congr_fun hψφ z; simpa [MonoidHom.comp_apply] using this
  right_inv := fun z => by
    have := DFunLike.congr_fun hφψ z; simpa [MonoidHom.comp_apply] using this
  map_mul' := φ.map_mul

/-! ### Class I bridge -/

theorem dickson_classification_SL2_coprime {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
    {p : ℕ} [CharP F p] (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [Finite G]
    (hcop : Nat.Coprime (Nat.card G) p) :
    IsCyclic G ∨
      (∃ n, Nonempty (G ≃* QuaternionGroup n)) ∨
      Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∨
      Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∨
      Nonempty (G ≃* BinaryOctahedral2O) := by
  rcases dicksons_classification_theorem_class_I' hp.prime G (Or.inr hcop) hp2 with
    h | ⟨n, h⟩ | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨n, h⟩)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · -- the `2O` leg: compose the repository's iso with the presentation transport
    obtain ⟨e⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e.trans transport2O.symm⟩)))

/-! ### Class II bridge -/

theorem dickson_classification_SL2_dvd {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
    {p : ℕ} [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [Finite G] (hp : p ∣ Nat.card G)
    (hp2 : p ≠ 2) :
    (∃ Q : Subgroup G,
        ((∀ a b : Q, a * b = b * a) ∧ (∀ h : Q, h ≠ 1 → orderOf h = p)) ∧ Q.Normal ∧
        ∃ K : Subgroup G,
          Subgroup.IsComplement' Q K ∧ IsCyclic K ∧ Nat.Coprime p (Nat.card K)) ∨
      (p = 2 ∧ ∃ n : ℕ, Odd n ∧ Nonempty (G ≃* DihedralGroup n)) ∨
      (p = 3 ∧ Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) ∨
      (∃ k : ℕ+, Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p k.val))) ∨
      (∃ k : ℕ+, ∃ f : GaloisField p k.val →+* GaloisField p (2 * k.val),
        ∃ π : (GaloisField p (2 * k.val))ˣ,
          (π : GaloisField p (2 * k.val)) ∉ Set.range f ∧
          ((π : GaloisField p (2 * k.val)) ^ 2) ∈ Set.range f ∧
          Nonempty (G ≃* ↥(Subgroup.map (Matrix.SpecialLinearGroup.map f) ⊤ ⊔
            Subgroup.closure {D π}))) := by
  rcases dicksons_classification_theorem_class_II' G hp hp2 with
    ⟨Q, hQe, hQn, K, hK⟩ | ⟨hp2eq, n, hodd, h⟩ | ⟨hp3, h⟩ | ⟨k, h⟩ | ⟨k, π, hπspec, hiso⟩
  · -- (vi): unfold the repository's `IsElementaryAbelian` into plain quantifiers
    exact Or.inl ⟨Q, ⟨fun a b => hQe.1.is_comm.comm a b, hQe.2⟩, hQn, K, hK⟩
  · exact Or.inr (Or.inl ⟨hp2eq, n, hodd, h⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hp3, h⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨k, h⟩)))
  · -- (x): instantiate `f` with the repository's canonical Galois embedding, then identify the
    -- twisted subgroup via `SL2_monoidHom_SL2 = SpecialLinearGroup.map f` and `D π = d π`
    refine Or.inr (Or.inr (Or.inr (Or.inr
      ⟨k, GaloisField_ringHom p k, π, hπspec.1, hπspec.2, ?_⟩)))
    obtain ⟨e⟩ := hiso
    have hmap : Matrix.SpecialLinearGroup.map (GaloisField_ringHom p k)
        = @SL2_monoidHom_SL2 p _ k := rfl
    have hd : D π = SpecialMatrices.d π := by
      apply Subtype.ext
      funext i j
      fin_cases i <;> fin_cases j <;> simp [D, SpecialMatrices.d]
    have hjoin : (Subgroup.map (Matrix.SpecialLinearGroup.map (GaloisField_ringHom p k)) ⊤ ⊔
        Subgroup.closure {D π}) = SL2_join_d p k π := by
      rw [hmap, hd]; rfl
    exact ⟨e.trans (MulEquiv.subgroupCongr hjoin.symm)⟩

end DicksonChallenge
