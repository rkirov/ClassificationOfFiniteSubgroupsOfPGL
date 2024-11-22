import Mathlib

open Subgroup MatrixGroups

def IsMaximalAbelian (G : Type*) [Group G] (H : Subgroup G) : Prop := Maximal (IsCommutative) H

-- def NonCentral
def MaximalAbelianSubgroups { G : Type*} [Group G](H : Subgroup G) : Set (Subgroup H) :=
  { K : Subgroup H | @IsMaximalAbelian H _ K}

variable (F : Type u) [Field F]

/- Let G be an arbitrary finite subgroup of SL(2, F) containing Z(SL(2, F)) -/
variable {G : Type*} (G : Subgroup (SL(2,F))) [Finite G] (hG : center (SL(2, F)) ≤ G)

/- Theorem 2.3 (iii) An element A of M is either a cyclic group whose order is relatively prime
to p, or of the form Q × Z where Q is an elementary abelian Sylow p-subgroup
of G. -/
def theorem_2_6_iii_a
  (A : Subgroup G)
  (hA : A ∈ MaximalAbelianSubgroups G)
  (h : ¬ (IsCyclic A ∧ Nat.Coprime (Nat.card A) p)) :
   A ≃* (Q.toSubgroup.prod (center SL(2,F))) := by sorry
