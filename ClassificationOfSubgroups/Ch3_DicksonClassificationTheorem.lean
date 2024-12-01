import Mathlib

universe u

variable (F : Type u) [Field F]

open Matrix MatrixGroups

/- Theorem 3.6 -/
theorem dickson_classification_theorem_class_I {p : ℕ} [CharP F p] (hp : Prime p) (hp' : p = 0 ∨ Nat.Coprime (Nat.card G) p)
  (G : Subgroup (SL(2,F))) [Finite G] : SL(2,F) = SL(2,F) := sorry
