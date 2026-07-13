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

end DicksonChallenge
