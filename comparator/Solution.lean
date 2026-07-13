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

end DicksonChallenge
