import Mathlib

/-!
# Dickson's classification of the finite subgroups of `PGL₂(F̄_p)` — challenge statement

This file is the **independently auditable statement** of the main theorem of this repository.
It imports only Mathlib, defines every non-Mathlib notion it uses explicitly below (two
one-line quotient abbreviations), and states the classification with `sorry`.

`Solution.lean` discharges the identical statement from the repository's proof, and
`../verify.sh` runs the official `leanprover/comparator` toolchain against the pair:
statement match, permitted-axiom check (`propext`, `Classical.choice`, `Quot.sound` only),
and independent kernel replay of the whole proof term via `lean4export`.

**To trust the result you need only:** read this file, trust the Lean kernel + Mathlib,
and run `../verify.sh`. Nothing else in the repository needs to be read.
-/

namespace DicksonChallenge

/-- `PGL(2, K) := GL(2, K) ⧸ Z(GL(2, K))`, the projective general linear group. -/
abbrev PGL2 (K : Type) [Field K] : Type :=
  Matrix.GeneralLinearGroup (Fin 2) K ⧸ Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K)

/-- `PSL(2, K) := SL(2, K) ⧸ Z(SL(2, K))`, the projective special linear group. -/
abbrev PSL2 (K : Type) [Field K] : Type :=
  Matrix.SpecialLinearGroup (Fin 2) K ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)

/-- **Dickson's classification of the finite subgroups of `PGL₂` over `F̄_p`** (`p` an odd
prime): every finite subgroup `G ≤ PGL(2, F̄_p)` is

1. cyclic, or
2. dihedral, or
3. contained in a Borel: `G` has an abelian normal subgroup `Q` of exponent `p` with a cyclic
   complement `K` of order coprime to `p`, or
4. isomorphic to `A₄`, or
5. isomorphic to `S₄`, or
6. isomorphic to `A₅`, or
7. isomorphic to `PSL(2, 𝔽_{p^k})` for some `k ≥ 1`, or
8. isomorphic to `PGL(2, 𝔽_{p^k})` for some `k ≥ 1`,

where `𝔽_{p^k}` is the Galois field `GaloisField p k`. -/
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
  sorry

/-!
## Dickson's two seminal `SL₂` theorems

Below are the two theorems that underlie the `PGL₂` classification above: Dickson's classification
of the finite subgroups `G ≤ SL(2, F)` of the special linear group over an algebraically closed
field `F` of odd characteristic `p`, split according to whether `p` divides `|G|`.

Both are stated over the same generality as the repository's proofs (`[Field F] [IsAlgClosed F]
[DecidableEq F] [CharP F p]`, all Mathlib type classes), reference only Mathlib notions, and are
**fully general**: they hold for *every* finite subgroup `G ≤ SL(2, F)` of the relevant order,
with no center-containment hypothesis. (Dickson's classical treatment normalizes to subgroups
containing the center `{±1}`; the repository discharges these general statements from that
normalized form via the `G⟨−1⟩` lift — see `dicksons_classification_theorem_class_I'` / `_II'` —
so the earlier center-normalization caveat is gone.)
-/

/-! ### The binary octahedral group `2O`, presented explicitly (Class I, disjunct 5)

The binary octahedral group `2O` (Butler's `Ŝ₄`, the binary cover of the octahedral rotation
group `S₄`) is the `⟨2, 3, 4⟩` binary polyhedral / von Dyck group with presentation
`⟨x, y | x⁴ = y³ = (xy)²⟩`; it has order `48` (the common central value `x⁴ = y³ = (xy)²` is the
order-`2` element `-1`, and modulo it one recovers the `(2,3,4)` triangle-group presentation of
`S₄`). We spell it out from first principles as a `PresentedGroup` over a two-symbol type, so the
challenge statement is fully auditable and depends on nothing outside Mathlib. -/

/-- The two generators `x`, `y` of the binary octahedral presentation. -/
inductive S2O
  | x
  | y

/-- The relators of `2O = ⟨x, y | x⁴ = y³ = (xy)²⟩`. As is standard for `PresentedGroup`, a
presentation is given by the set of *words that are trivial* in the group; here the two words
`x⁴·(y³)⁻¹` (encoding `x⁴ = y³`) and `x⁴·((xy)²)⁻¹` (encoding `x⁴ = (xy)²`). -/
def BinaryOctahedralRelations : Set (FreeGroup S2O) :=
  { FreeGroup.of S2O.x ^ 4 * (FreeGroup.of S2O.y ^ 3)⁻¹ } ∪
  { FreeGroup.of S2O.x ^ 4 * ((FreeGroup.of S2O.x * FreeGroup.of S2O.y) ^ 2)⁻¹ }

/-- The binary octahedral group `2O`, as the group presented by `BinaryOctahedralRelations`. -/
abbrev BinaryOctahedral2O := PresentedGroup BinaryOctahedralRelations

/-- The explicit diagonal element `diag(π, π⁻¹) ∈ SL₂(𝔽_{p^{2k}})` adjoined in Class II item (x),
i.e. the matrix

    ⎡ π    0  ⎤
    ⎣ 0   π⁻¹ ⎦

whose determinant `π · π⁻¹ = 1` places it in the special linear group. Its entries are chosen to
match the repository's diagonal generator (`SpecialMatrices.d π`) verbatim, which is what lets the
bridge in `Solution.lean` identify the two "twisted" subgroups by a plain matrix `ext`. -/
noncomputable def D {p : ℕ} [Fact (Nat.Prime p)] {k : ℕ+} (π : (GaloisField p (2 * k.val))ˣ) :
    Matrix.SpecialLinearGroup (Fin 2) (GaloisField p (2 * k.val)) :=
  ⟨!![(π : GaloisField p (2 * k.val)), 0; 0, (π : GaloisField p (2 * k.val))⁻¹],
    by rw [Matrix.det_fin_two_of]; simp⟩

/-- **Dickson's classification of finite `G ≤ SL(2, F)` — Class I** (the coprime /
binary-polyhedral case).

Let `F` be algebraically closed of odd prime characteristic `p`, and let `G ≤ SL(2, F)` be a
finite subgroup whose order `|G|` is coprime to `p`. Then `G` is one of the following five types:

1. cyclic; or
2. a generalised quaternion (dicyclic) group `QuaternionGroup n` (order `4n`); or
3. `SL(2, 𝔽₃)`, the binary tetrahedral group `2T` (order `24`); or
4. `SL(2, 𝔽₅)`, the binary icosahedral group `2I` (order `120`); or
5. the binary octahedral group `2O = ⟨x, y | x⁴ = y³ = (xy)²⟩` (order `48`, `BinaryOctahedral2O`).

**Fully general.** No center-containment hypothesis is required: the statement holds for every
finite `G ≤ SL(2, F)` with `|G|` coprime to `p`. -/
theorem dickson_classification_SL2_coprime {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
    {p : ℕ} [CharP F p] (hp : Nat.Prime p) (hp2 : p ≠ 2)
    (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [Finite G]
    (hcop : Nat.Coprime (Nat.card G) p) :
    -- (1) cyclic
    IsCyclic G ∨
      -- (2) generalised quaternion / dicyclic of order `4n`
      (∃ n, Nonempty (G ≃* QuaternionGroup n)) ∨
      -- (3) binary tetrahedral `2T ≅ SL(2, 𝔽₃)`
      Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∨
      -- (4) binary icosahedral `2I ≅ SL(2, 𝔽₅)`
      Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∨
      -- (5) binary octahedral `2O = ⟨x, y | x⁴ = y³ = (xy)²⟩`
      Nonempty (G ≃* BinaryOctahedral2O) := sorry

/-- **Dickson's classification of finite `G ≤ SL(2, F)` — Class II** (the modular case).

Let `F` be algebraically closed of odd prime characteristic `p`, and let `G ≤ SL(2, F)` be a
finite subgroup whose order is *divisible* by `p`. Then `G` is one of five types, numbered
`(vi)`–`(x)` to continue Butler's enumeration:

- (vi) a "Borel"-type group: an elementary-abelian normal `p`-subgroup `Q` (here spelled as plain
  quantifiers: `Q` is commutative and every non-identity element has order exactly `p`) with a
  cyclic complement `K` of order coprime to `p`; or
- (vii) `p = 2` and `G ≅ DihedralGroup n` for some odd `n` (vacuous here since `p ≠ 2`, but kept to
  mirror the repository statement); or
- (viii) `p = 3` and `G ≅ SL(2, 𝔽₅)`; or
- (ix) `G ≅ SL(2, 𝔽_{p^k})` for some `k ≥ 1` (`GaloisField p k`); or
- (x) a "twisted" group `⟨SL(2, 𝔽_q), d_π⟩ ≤ SL(2, 𝔽_{q²})`, `q = p^k`: the image of `SL(2, 𝔽_q)`
  under a field embedding `f : 𝔽_q ↪ 𝔽_{q²}`, joined with the diagonal twist `d_π = D π` for a
  unit `π ∈ 𝔽_{q²}` with `π ∉ 𝔽_q` but `π² ∈ 𝔽_q` (so `𝔽_q ↦ Set.range f`, and `SL(2, 𝔽_q)` is
  normal of index `2`). The embedding `f` is quantified existentially: this keeps the statement
  self-contained and Mathlib-only, and is faithful in the sense that it is *implied by* the
  repository's specific-embedding statement — the bridge discharges it by supplying the repository's
  canonical Galois embedding for `f`.

**Fully general.** As in Class I, no center-containment hypothesis is required: the statement
holds for every finite `G ≤ SL(2, F)` whose order is divisible by `p`. -/
theorem dickson_classification_SL2_dvd {F : Type*} [Field F] [IsAlgClosed F] [DecidableEq F]
    {p : ℕ} [Fact (Nat.Prime p)] [CharP F p]
    (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) [Finite G] (hp : p ∣ Nat.card G)
    (hp2 : p ≠ 2) :
    -- (vi) elementary-abelian normal `p`-subgroup `Q` with cyclic complement `K`, `p ∤ |K|`
    (∃ Q : Subgroup G,
        ((∀ a b : Q, a * b = b * a) ∧ (∀ h : Q, h ≠ 1 → orderOf h = p)) ∧ Q.Normal ∧
        ∃ K : Subgroup G,
          Subgroup.IsComplement' Q K ∧ IsCyclic K ∧ Nat.Coprime p (Nat.card K)) ∨
      -- (vii) `p = 2` and dihedral of odd order (vacuous under `p ≠ 2`, kept to mirror the repo)
      (p = 2 ∧ ∃ n : ℕ, Odd n ∧ Nonempty (G ≃* DihedralGroup n)) ∨
      -- (viii) `p = 3` and `G ≅ SL(2, 𝔽₅)`
      (p = 3 ∧ Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5))) ∨
      -- (ix) `G ≅ SL(2, 𝔽_{p^k})`
      (∃ k : ℕ+, Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField p k.val))) ∨
      -- (x) twisted `⟨SL(2, 𝔽_q), d_π⟩ ≤ SL(2, 𝔽_{q²})` for an embedding `f` and twist `π`
      (∃ k : ℕ+, ∃ f : GaloisField p k.val →+* GaloisField p (2 * k.val),
        ∃ π : (GaloisField p (2 * k.val))ˣ,
          (π : GaloisField p (2 * k.val)) ∉ Set.range f ∧
          ((π : GaloisField p (2 * k.val)) ^ 2) ∈ Set.range f ∧
          Nonempty (G ≃* ↥(Subgroup.map (Matrix.SpecialLinearGroup.map f) ⊤ ⊔
            Subgroup.closure {D π}))) := sorry

/-!
## Klein's classification in characteristic zero

The two theorems below are the classical characteristic-`0` counterparts (Klein, 1876):
the classification of the finite subgroups of `SL(2, K)` and of `PGL(2, K)` for `K`
algebraically closed of characteristic zero — e.g. `K = ℂ`, where `PGL(2, ℂ)` is the Möbius
group and the `PGL₂` list (cyclic, dihedral, `A₄`, `S₄`, `A₅`) is the symmetry classification
of the platonic solids. No hypotheses beyond finiteness: any finite subgroup.
-/

/-- **Klein's classification of the finite subgroups of `SL(2, K)`**, `K` algebraically closed
of characteristic zero (e.g. `K = ℂ`): every finite subgroup is

1. cyclic, or
2. dicyclic / binary dihedral (`QuaternionGroup n`, order `4n`), or
3. the binary tetrahedral group `2T ≅ SL(2, 𝔽₃)` (order `24`), or
4. the binary icosahedral group `2I ≅ SL(2, 𝔽₅)` (order `120`), or
5. the binary octahedral group `2O = ⟨x, y | x⁴ = y³ = (xy)²⟩` (order `48`,
   `BinaryOctahedral2O` as defined above). -/
theorem klein_classification_SL2 {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) [Finite G] :
    IsCyclic G ∨
      (∃ n, Nonempty (G ≃* QuaternionGroup n)) ∨
      Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) ∨
      Nonempty (G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∨
      Nonempty (G ≃* BinaryOctahedral2O) := sorry

/-- **Klein's classification of the finite subgroups of `PGL(2, K)`**, `K` algebraically closed
of characteristic zero (for `K = ℂ`: the finite groups of Möbius transformations): every finite
subgroup is cyclic, dihedral, `A₄`, `S₄` or `A₅`. -/
theorem klein_classification_PGL2 {K : Type} [Field K] [IsAlgClosed K] [CharZero K]
    (G : Subgroup (PGL2 K)) [Finite G] :
    IsCyclic G ∨
      (∃ n, Nonempty (G ≃* DihedralGroup n)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (G ≃* Equiv.Perm (Fin 4)) ∨
      Nonempty (G ≃* alternatingGroup (Fin 5)) := sorry

end DicksonChallenge
