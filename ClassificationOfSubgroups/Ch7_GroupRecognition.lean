/-
This file collects abstract group-theoretic *recognition lemmas*: given an explicit
generator/relation description of a finite group `G` in terms of two elements `x y : G`,
these lemmas identify `G` (up to isomorphism) with the corresponding `Mathlib`
`DihedralGroup n` / `QuaternionGroup n`.

They are used by the case analysis in Christopher Butler's classification of the finite
subgroups of `SL(2,F)` (`ChristopherButler.tex`), specifically cases II(a), IV(a), VI(a),
where a subgroup is shown to satisfy one of the two presentations

  `⟨x, y | xⁿ = 1 = y², y x y⁻¹ = x⁻¹⟩`          (dihedral of order `2n`), or
  `⟨x, y | xⁿ = y², y x y⁻¹ = x⁻¹⟩` (with `orderOf x = 2n`)  (dicyclic/quaternion of order `4n`)

and one wants to conclude that the ambient group is (abstractly) the corresponding
`DihedralGroup`/`QuaternionGroup`.

This file is deliberately self-contained abstract group theory: it contains no reference
to `SL(2,F)`, matrices, or fields.

## Implementation notes

Both proofs follow the same recipe:

* build the (unique) candidate homomorphism `φ : DihedralGroup n →* G` (resp.
  `QuaternionGroup n →* G`) sending the standard generators to `x`/`y`, using that
  `Mathlib`'s multiplication tables for `DihedralGroup`/`QuaternionGroup` are literally the
  defining relations of the presentations above;
* show `φ` is injective, using `orderOf x = n` (resp. `2 * n`) to control the "rotation"
  part and `y ∉ Subgroup.zpowers x` to rule out collisions between the two "sides"
  (`r`/`sr`, resp. `a`/`xa`);
* upgrade injectivity to bijectivity using the matching (finite) cardinalities;
* take `MulEquiv.ofBijective` and flip it to land on `G ≃* DihedralGroup n`
  (resp. `G ≃* QuaternionGroup n`).
-/
import Mathlib

set_option autoImplicit false

open Subgroup

namespace Ch7GroupRecognition

variable {G : Type*} [Group G] [Finite G]

section Dihedral

variable {n : ℕ} [NeZero n]

/-- **Recognition lemma for the dihedral group.**

If `G` is a finite group containing `x y : G` with `x` of order `n`, `y` an involution not
lying in `⟨x⟩`, satisfying the dihedral relation `y * x * y⁻¹ = x⁻¹`, and `Nat.card G = 2 * n`,
then `G` is (abstractly) the dihedral group of order `2n`.

This is the presentation `⟨x, y | xⁿ = 1 = y², y x y⁻¹ = x⁻¹⟩` used by Butler for cases in
which a finite subgroup of `SL(2,F)` is shown to be dihedral. -/
noncomputable def mulEquiv_dihedralGroup_of (x y : G)
    (hx : orderOf x = n) (hy2 : y ^ 2 = 1) (hy1 : y ≠ 1)
    (hconj : y * x * y⁻¹ = x⁻¹) (hyx : y ∉ Subgroup.zpowers x)
    (hcard : Nat.card G = 2 * n) :
    G ≃* DihedralGroup n := by
  have hyy : y * y = 1 := by have h2 := hy2; rwa [sq] at h2
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  -- transport equalities of powers of `x` along congruences mod `n = orderOf x`
  have hxpow_eq : ∀ {k l : ℕ}, k ≡ l [MOD n] → x ^ k = x ^ l := by
    intro k l hkl
    rw [pow_eq_pow_iff_modEq, hx]
    exact hkl
  -- `x ^ a.val * x ^ b.val = x ^ (a + b).val` for `a b : ZMod n`
  have L1 : ∀ a b : ZMod n, x ^ a.val * x ^ b.val = x ^ (a + b).val := by
    intro a b
    rw [← pow_add]
    apply hxpow_eq
    rw [ZMod.val_add]
    exact (Nat.mod_modEq _ _).symm
  -- conjugation of `x^k` by `y`
  have hconjpow : ∀ k : ℕ, y * x ^ k * y⁻¹ = (x ^ k)⁻¹ := by
    intro k
    have h := map_pow (MulAut.conj y) x k
    rw [MulAut.conj_apply, MulAut.conj_apply, hconj, inv_pow] at h
    exact h
  have hconjpowy : ∀ k : ℕ, y * x ^ k * y = (x ^ k)⁻¹ := by
    intro k
    have h := hconjpow k
    rwa [hyinv] at h
  -- `x^k * y = y * (x^k)⁻¹`, the key commutation rule
  have L2b : ∀ k : ℕ, x ^ k * y = y * (x ^ k)⁻¹ := by
    intro k
    have h := hconjpowy k
    calc x ^ k * y = y * (y * x ^ k * y) := by
          rw [← mul_assoc, ← mul_assoc, hyy, one_mul]
      _ = y * (x ^ k)⁻¹ := by rw [h]
  -- `(x^a.val)⁻¹ * x^b.val = x^(b - a).val`
  have L3 : ∀ a b : ZMod n, (x ^ a.val)⁻¹ * x ^ b.val = x ^ (b - a).val := by
    intro a b
    have h := L1 a (b - a)
    rw [add_sub_cancel] at h
    rw [← h, inv_mul_cancel_left]
  -- the candidate map, following `Mathlib`'s `DihedralGroup` multiplication table exactly
  let φ : DihedralGroup n → G := fun g => match g with
    | .r i => x ^ i.val
    | .sr i => y * x ^ i.val
  have hmul : ∀ g h : DihedralGroup n, φ (g * h) = φ g * φ h := by
    rintro (i | i) (j | j)
    · show x ^ (i + j).val = x ^ i.val * x ^ j.val
      rw [L1]
    · show y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
      calc y * x ^ (j - i).val = y * ((x ^ i.val)⁻¹ * x ^ j.val) := by rw [L3]
        _ = (y * (x ^ i.val)⁻¹) * x ^ j.val := by rw [mul_assoc]
        _ = x ^ i.val * (y * x ^ j.val) := by rw [← L2b, mul_assoc]
    · show y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
      rw [mul_assoc, L1]
    · show x ^ (j - i).val = y * x ^ i.val * (y * x ^ j.val)
      calc x ^ (j - i).val = (x ^ i.val)⁻¹ * x ^ j.val := by rw [L3]
        _ = (y * y) * (x ^ i.val)⁻¹ * x ^ j.val := by rw [hyy, one_mul]
        _ = y * (y * (x ^ i.val)⁻¹) * x ^ j.val := by group
        _ = y * (x ^ i.val * y) * x ^ j.val := by rw [L2b]
        _ = y * x ^ i.val * (y * x ^ j.val) := by group
  let φhom : DihedralGroup n →* G := MonoidHom.mk' φ hmul
  -- injectivity of `φ`
  have hval_inj : ∀ i j : ZMod n, x ^ i.val = x ^ j.val → i = j := by
    intro i j h
    have hcong : i.val ≡ j.val [MOD n] := by
      have := pow_eq_pow_iff_modEq.mp h
      rwa [hx] at this
    apply ZMod.val_injective
    have h1 : i.val % n = i.val := Nat.mod_eq_of_lt i.val_lt
    have h2 : j.val % n = j.val := Nat.mod_eq_of_lt j.val_lt
    rw [← h1, ← h2]
    exact hcong
  have hxpow_mem : ∀ k : ℕ, x ^ k ∈ Subgroup.zpowers x := fun k =>
    (Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) k
  have hinj : Function.Injective φhom := by
    rintro (i | i) (j | j) heq
    · have : x ^ i.val = x ^ j.val := heq
      rw [hval_inj i j this]
    · exfalso
      have heq' : x ^ i.val = y * x ^ j.val := heq
      have hy_mem : y ∈ Subgroup.zpowers x := by
        have : y = x ^ i.val * (x ^ j.val)⁻¹ := by rw [heq']; group
        rw [this]
        exact Subgroup.mul_mem _ (hxpow_mem i.val) (Subgroup.inv_mem _ (hxpow_mem j.val))
      exact hyx hy_mem
    · exfalso
      have heq' : y * x ^ i.val = x ^ j.val := heq
      have hy_mem : y ∈ Subgroup.zpowers x := by
        have : y = x ^ j.val * (x ^ i.val)⁻¹ := by rw [← heq']; group
        rw [this]
        exact Subgroup.mul_mem _ (hxpow_mem j.val) (Subgroup.inv_mem _ (hxpow_mem i.val))
      exact hyx hy_mem
    · have h' : y * x ^ i.val = y * x ^ j.val := heq
      have : x ^ i.val = x ^ j.val := mul_left_cancel h'
      rw [hval_inj i j this]
  have hbij : Function.Bijective φhom :=
    (Nat.bijective_iff_injective_and_card φhom).mpr
      ⟨hinj, by rw [DihedralGroup.nat_card, hcard]⟩
  exact (MulEquiv.ofBijective φhom hbij).symm

end Dihedral

section Quaternion

variable {n : ℕ} [NeZero n]

/-- **Recognition lemma for the (generalised) quaternion / dicyclic group.**

If `G` is a finite group containing `x y : G` with `x` of order `2n`, `y ^ 2 = x ^ n`, `y`
not lying in `⟨x⟩`, satisfying the relation `y * x * y⁻¹ = x⁻¹`, and `Nat.card G = 4 * n`,
then `G` is (abstractly) the (generalised) quaternion group `QuaternionGroup n` of order `4n`.

This is the presentation `⟨x, y | x^(2n) = 1, y² = xⁿ, y x y⁻¹ = x⁻¹⟩` (matching `Mathlib`'s
`QuaternionGroup`, cf. `Mathlib.GroupTheory.SpecificGroups.Quaternion`) used by Butler for
cases in which a finite subgroup of `SL(2,F)` is shown to be dicyclic. -/
noncomputable def mulEquiv_quaternionGroup_of (x y : G)
    (hx : orderOf x = 2 * n) (hy2 : y ^ 2 = x ^ n)
    (hconj : y * x * y⁻¹ = x⁻¹) (hyx : y ∉ Subgroup.zpowers x)
    (hcard : Nat.card G = 4 * n) :
    G ≃* QuaternionGroup n := by
  -- transport equalities of powers of `x` along congruences mod `2n = orderOf x`
  have hxpow_eq : ∀ {k l : ℕ}, k ≡ l [MOD 2 * n] → x ^ k = x ^ l := by
    intro k l hkl
    rw [pow_eq_pow_iff_modEq, hx]
    exact hkl
  -- `x ^ a.val * x ^ b.val = x ^ (a + b).val` for `a b : ZMod (2n)`
  have L1 : ∀ a b : ZMod (2 * n), x ^ a.val * x ^ b.val = x ^ (a + b).val := by
    intro a b
    rw [← pow_add]
    apply hxpow_eq
    rw [ZMod.val_add]
    exact (Nat.mod_modEq _ _).symm
  -- variant of `L1` allowing a bare nat exponent (needed for the `n + j - i` offset)
  have L1' : ∀ (k : ℕ) (c : ZMod (2 * n)),
      x ^ k * x ^ c.val = x ^ ((k : ZMod (2 * n)) + c).val := by
    intro k c
    have hk : x ^ k = x ^ (k : ZMod (2 * n)).val := by
      apply hxpow_eq
      rw [ZMod.val_natCast]
      exact (Nat.mod_modEq k (2 * n)).symm
    rw [hk, L1]
  -- conjugation of `x ^ k` (`k : ℤ`) by `y`; no involution assumption on `y` is needed here
  have hconjzpow : ∀ k : ℤ, y * x ^ k * y⁻¹ = (x ^ k)⁻¹ := by
    intro k
    have h := map_zpow (MulAut.conj y) x k
    rw [MulAut.conj_apply, MulAut.conj_apply, hconj, inv_zpow] at h
    exact h
  have L2a : ∀ k : ℤ, y * x ^ k = (x ^ k)⁻¹ * y := by
    intro k
    have h := hconjzpow k
    calc y * x ^ k = y * x ^ k * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = (x ^ k)⁻¹ * y := by rw [h]
  have L2bZ : ∀ k : ℤ, x ^ k * y = y * (x ^ k)⁻¹ := by
    intro k
    have h := L2a (-k)
    rw [zpow_neg, inv_inv] at h
    exact h.symm
  -- `x^k * y = y * (x^k)⁻¹`, the key commutation rule (nat exponent version)
  have L2b : ∀ k : ℕ, x ^ k * y = y * (x ^ k)⁻¹ := by
    intro k
    have h := L2bZ (k : ℤ)
    simpa using h
  -- `(x^a.val)⁻¹ * x^b.val = x^(b - a).val`
  have L3 : ∀ a b : ZMod (2 * n), (x ^ a.val)⁻¹ * x ^ b.val = x ^ (b - a).val := by
    intro a b
    have h := L1 a (b - a)
    rw [add_sub_cancel] at h
    rw [← h, inv_mul_cancel_left]
  have hyy : y * y = x ^ n := by rw [← sq]; exact hy2
  -- the candidate map, following `Mathlib`'s `QuaternionGroup` multiplication table exactly
  let φ : QuaternionGroup n → G := fun g => match g with
    | .a i => x ^ i.val
    | .xa i => y * x ^ i.val
  have hmul : ∀ g h : QuaternionGroup n, φ (g * h) = φ g * φ h := by
    rintro (i | i) (j | j)
    · show x ^ (i + j).val = x ^ i.val * x ^ j.val
      rw [L1]
    · show y * x ^ (j - i).val = x ^ i.val * (y * x ^ j.val)
      calc y * x ^ (j - i).val = y * ((x ^ i.val)⁻¹ * x ^ j.val) := by rw [L3]
        _ = (y * (x ^ i.val)⁻¹) * x ^ j.val := by rw [mul_assoc]
        _ = x ^ i.val * (y * x ^ j.val) := by rw [← L2b, mul_assoc]
    · show y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
      rw [mul_assoc, L1]
    · show x ^ ((n : ZMod (2 * n)) + j - i).val = y * x ^ i.val * (y * x ^ j.val)
      calc x ^ ((n : ZMod (2 * n)) + j - i).val
          = x ^ ((n : ZMod (2 * n)) + (j - i)).val := by rw [add_sub_assoc]
        _ = x ^ n * x ^ (j - i).val := by rw [L1']
        _ = x ^ n * ((x ^ i.val)⁻¹ * x ^ j.val) := by rw [L3]
        _ = (x ^ n) * (x ^ i.val)⁻¹ * x ^ j.val := by rw [mul_assoc]
        _ = (y * y) * (x ^ i.val)⁻¹ * x ^ j.val := by rw [hyy]
        _ = y * (y * (x ^ i.val)⁻¹) * x ^ j.val := by group
        _ = y * (x ^ i.val * y) * x ^ j.val := by rw [L2b]
        _ = y * x ^ i.val * (y * x ^ j.val) := by group
  let φhom : QuaternionGroup n →* G := MonoidHom.mk' φ hmul
  -- injectivity of `φ`
  have hval_inj : ∀ i j : ZMod (2 * n), x ^ i.val = x ^ j.val → i = j := by
    intro i j h
    have hcong : i.val ≡ j.val [MOD 2 * n] := by
      have := pow_eq_pow_iff_modEq.mp h
      rwa [hx] at this
    apply ZMod.val_injective
    have h1 : i.val % (2 * n) = i.val := Nat.mod_eq_of_lt i.val_lt
    have h2 : j.val % (2 * n) = j.val := Nat.mod_eq_of_lt j.val_lt
    rw [← h1, ← h2]
    exact hcong
  have hxpow_mem : ∀ k : ℕ, x ^ k ∈ Subgroup.zpowers x := fun k =>
    (Subgroup.zpowers x).pow_mem (Subgroup.mem_zpowers x) k
  have hinj : Function.Injective φhom := by
    rintro (i | i) (j | j) heq
    · have : x ^ i.val = x ^ j.val := heq
      rw [hval_inj i j this]
    · exfalso
      have heq' : x ^ i.val = y * x ^ j.val := heq
      have hy_mem : y ∈ Subgroup.zpowers x := by
        have : y = x ^ i.val * (x ^ j.val)⁻¹ := by rw [heq']; group
        rw [this]
        exact Subgroup.mul_mem _ (hxpow_mem i.val) (Subgroup.inv_mem _ (hxpow_mem j.val))
      exact hyx hy_mem
    · exfalso
      have heq' : y * x ^ i.val = x ^ j.val := heq
      have hy_mem : y ∈ Subgroup.zpowers x := by
        have : y = x ^ j.val * (x ^ i.val)⁻¹ := by rw [← heq']; group
        rw [this]
        exact Subgroup.mul_mem _ (hxpow_mem j.val) (Subgroup.inv_mem _ (hxpow_mem i.val))
      exact hyx hy_mem
    · have h' : y * x ^ i.val = y * x ^ j.val := heq
      have : x ^ i.val = x ^ j.val := mul_left_cancel h'
      rw [hval_inj i j this]
  have hbij : Function.Bijective φhom :=
    (Nat.bijective_iff_injective_and_card φhom).mpr
      ⟨hinj, by rw [Nat.card_eq_fintype_card, QuaternionGroup.card, hcard]⟩
  exact (MulEquiv.ofBijective φhom hbij).symm

end Quaternion

end Ch7GroupRecognition
