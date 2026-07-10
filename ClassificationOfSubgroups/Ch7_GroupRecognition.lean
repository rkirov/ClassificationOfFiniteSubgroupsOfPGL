/-
This file collects abstract group-theoretic *recognition lemmas*: given an explicit
generator/relation description of a finite group `G` in terms of two or three elements
`x y (r) : G`, these lemmas identify `G` (up to isomorphism) with the corresponding `Mathlib`
`DihedralGroup n` / `QuaternionGroup n`, or with `SL(2, ZMod 3)`.

They are used by the case analysis in Christopher Butler's classification of the finite
subgroups of `SL(2,F)` (`ChristopherButler.tex`), specifically cases II(a), IV(a), VI(a) (dihedral
/ dicyclic recognition) and II(b), IV(b) (`SL(2,3)` recognition), where a subgroup is shown to
satisfy one of the presentations

  `⟨x, y | xⁿ = 1 = y², y x y⁻¹ = x⁻¹⟩`          (dihedral of order `2n`), or
  `⟨x, y | xⁿ = y², y x y⁻¹ = x⁻¹⟩` (with `orderOf x = 2n`)  (dicyclic/quaternion of order `4n`), or
  `⟨x, y, r | x² = y², y x y⁻¹ = x⁻¹, r³ = 1, r x r⁻¹ = y, r y r⁻¹ = x y⟩`  (order `24`)

and one wants to conclude that the ambient group is (abstractly) the corresponding
`DihedralGroup`/`QuaternionGroup`/`SL(2, ZMod 3)`.

Sections `Dihedral` and `Quaternion` are deliberately self-contained abstract group theory: they
contain no reference to `SL(2,F)`, matrices, or fields. The final section, `SL2ZMod3`, is a
genuine exception (see its own docstring / item 8 of `DIVERGENCES.md`): the *statement* of its
public lemma, `mulEquiv_SL2_ZMod3_of`, necessarily mentions `SL(2, ZMod 3)` as the target type,
though its *proof* (via `equiv_of_SL2ZMod3_data`) is again abstract group theory, applied once to
the (abstract) hypothesis group `G` and once to the concrete matrix group `SL(2, ZMod 3)`.

## Implementation notes

The `Dihedral`/`Quaternion` proofs follow the same recipe:

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

The `SL2ZMod3` recognition lemma instead uses a **semidirect-product gluing** route (see its own
docstring for the full recipe): rather than building a single explicit bijection by hand (as
above), it exhibits `G` (and, separately, `SL(2, ZMod 3)`) as an *internal* semidirect product
`N ⋊ ⟨r⟩` of its `Q₈` Sylow `2`-subgroup `N = ⟨x, y⟩` by the order-`3` complement `⟨r⟩`
(`Mathlib`'s `SemidirectProduct.mulEquivSubgroup`), then glues the two semidirect decompositions
along matched generator-to-generator isomorphisms of `N` and `⟨r⟩`
(`Mathlib`'s `SemidirectProduct.congr`). This is recorded as a divergence from Butler, who
instead pins down the isomorphism by direct matrix inspection (tex ~1642-1653): see
`DIVERGENCES.md`, item 8.
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

section SL2ZMod3

/-!
### `SL(2, ZMod 3)` recognition (Butler Case IIb / IVb, tex ~1512-1653 / ~1785)

**Target**: `mulEquiv_SL2_ZMod3_of`, at the end of this section.

**Route** ("semidirect gluing", divergence item 8 in `DIVERGENCES.md`): given `x y r : G` with
`x, y` generating a copy of `Q₈` (`⟨x,y | x²=y², yxy⁻¹=x⁻¹⟩`, `orderOf x = 4`) and `r` of order
`3` acting on `⟨x,y⟩` by `r x r⁻¹ = y`, `r y r⁻¹ = x y`, and `Nat.card G = 24`:

1. (`quaternionGroup_hom_injective`) build the injective hom `QuaternionGroup 2 →* G` sending the
   standard generators to `x, y` (exactly as in `mulEquiv_quaternionGroup_of` above, but *without*
   needing `Nat.card G` to upgrade injectivity to bijectivity onto all of `G` -- only onto its
   *range* `N`, since here `N` is a proper subgroup of `G`, of index `3`, not all of `G`).
2. (`SL2ZMod3_side`) show `N := range` (order `8`, a copy of `Q₈`) is *normal* in `G` (`r`
   normalizes it, being finite-to-finite injective-hence-bijective on it) and is complemented by
   the order-`3` subgroup `⟨r⟩` (`IsComplement'`, from the coprime cardinalities `8`, `3`
   multiplying to `24`).
3. (`equiv_of_SL2ZMod3_data`) apply step 1-2 to *both* `G` and (with concrete matrix witnesses,
   verified by `decide`) `SL(2, ZMod 3)`, obtaining `G ≃* N ⋊ ⟨r⟩` and
   `SL(2,ZMod 3) ≃* N' ⋊ ⟨r'⟩` (`Mathlib`'s `SemidirectProduct.mulEquivSubgroup`); glue these via
   `SemidirectProduct.congr`, matching generator-to-generator isomorphisms `N ≃* N'` (the two
   `Q₈`-embeddings composed) and `⟨r⟩ ≃* ⟨r'⟩` (`zpowersMulEquivZPowers`, generator to generator).
   The one nontrivial compatibility check `SemidirectProduct.congr` demands (that the two
   conjugation actions agree after transport) reduces, since `⟨r⟩` has only `3` elements, to a
   `3`-way case split (`r⁰, r¹, r²`), each closed by direct computation using `r`'s (and, for
   `r²`, the derived `r²`-conjugation formula `rsq_conj_formula`) defining relations.
4. (`mulEquiv_SL2_ZMod3_of`) the public wrapper, instantiating step 3 with Butler's own matrix
   witnesses for `SL(2,3)` (tex ~1642-1650) -- up to replacing his `c` by `c⁻¹`, since with our
   `r x r⁻¹ = y` convention it is `c⁻¹`, not `c`, that conjugates `a ↦ b` (verified directly by
   `decide`; a minor, presentation-level divergence, not a mathematical one -- `⟨a,b,c⟩ =
   ⟨a,b,c⁻¹⟩`).
-/

/-- Build the (unique) hom `QuaternionGroup n →* G` sending the standard generators to `x`, `y`,
and show it is injective, WITHOUT needing to know `Nat.card G` (unlike
`mulEquiv_quaternionGroup_of` above, which additionally needs `Nat.card G = 4*n` to upgrade
injectivity to bijectivity onto all of `G`). This is the "half" of that lemma's construction
needed when `⟨x,y⟩` is only a *proper* subgroup of the ambient group. -/
private lemma quaternionGroup_hom_injective {n : ℕ} [NeZero n] {G : Type*} [Group G] (x y : G)
    (hx : orderOf x = 2 * n) (hy2 : y ^ 2 = x ^ n)
    (hconj : y * x * y⁻¹ = x⁻¹) (hyx : y ∉ Subgroup.zpowers x) :
    ∃ φ : QuaternionGroup n →* G, Function.Injective φ ∧
      (∀ i : ZMod (2 * n), φ (.a i) = x ^ i.val) ∧
      (∀ i : ZMod (2 * n), φ (.xa i) = y * x ^ i.val) := by
  have hxpow_eq : ∀ {k l : ℕ}, k ≡ l [MOD 2 * n] → x ^ k = x ^ l := by
    intro k l hkl
    rw [pow_eq_pow_iff_modEq, hx]
    exact hkl
  have L1 : ∀ a b : ZMod (2 * n), x ^ a.val * x ^ b.val = x ^ (a + b).val := by
    intro a b
    rw [← pow_add]
    apply hxpow_eq
    rw [ZMod.val_add]
    exact (Nat.mod_modEq _ _).symm
  have L1' : ∀ (k : ℕ) (c : ZMod (2 * n)),
      x ^ k * x ^ c.val = x ^ ((k : ZMod (2 * n)) + c).val := by
    intro k c
    have hk : x ^ k = x ^ (k : ZMod (2 * n)).val := by
      apply hxpow_eq
      rw [ZMod.val_natCast]
      exact (Nat.mod_modEq k (2 * n)).symm
    rw [hk, L1]
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
  have L2b : ∀ k : ℕ, x ^ k * y = y * (x ^ k)⁻¹ := by
    intro k
    have h := L2bZ (k : ℤ)
    simpa using h
  have L3 : ∀ a b : ZMod (2 * n), (x ^ a.val)⁻¹ * x ^ b.val = x ^ (b - a).val := by
    intro a b
    have h := L1 a (b - a)
    rw [add_sub_cancel] at h
    rw [← h, inv_mul_cancel_left]
  have hyy : y * y = x ^ n := by rw [← sq]; exact hy2
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
  exact ⟨φhom, hinj, fun i => rfl, fun i => rfl⟩

/-- The `Q₈` Sylow `2`-subgroup `N = range φ` (`φ` from `quaternionGroup_hom_injective`, `n = 2`)
generated by `x, y` is normal in `G` and complemented by `⟨r⟩` (order `3`), given `Nat.card G =
24` and `r`'s prescribed action on `x, y`. -/
private lemma SL2ZMod3_side {G : Type*} [Group G] [Finite G] (x y r : G)
    (hx : orderOf x = 4) (hxy2 : x ^ 2 = y ^ 2) (hconj : y * x * y⁻¹ = x⁻¹)
    (hyx : y ∉ Subgroup.zpowers x) (hr3 : r ^ 3 = 1)
    (hrx : r * x * r⁻¹ = y) (hry : r * y * r⁻¹ = x * y) (hcard : Nat.card G = 24) :
    ∃ (φ : QuaternionGroup 2 →* G), Function.Injective φ ∧
      (∀ i : ZMod 4, φ (.a i) = x ^ i.val) ∧ (∀ i : ZMod 4, φ (.xa i) = y * x ^ i.val) ∧
      (φ.range).Normal ∧ orderOf r = 3 ∧
      IsComplement' φ.range (Subgroup.zpowers r) := by
  obtain ⟨φ, hinj, hφa, hφxa⟩ := quaternionGroup_hom_injective (n := 2) x y
    (by rw [hx]) hxy2.symm hconj hyx
  have hφx : φ (.a 1) = x := by
    have h1 : (1 : ZMod (2 * 2)).val = 1 := by decide
    have h := hφa 1
    rwa [h1, pow_one] at h
  have hφy : φ (.xa 0) = y := by
    have h0 : (0 : ZMod (2 * 2)).val = 0 := by decide
    have h := hφxa 0
    rwa [h0, pow_zero, mul_one] at h
  set N := φ.range with hN_def
  have hNcard : Nat.card N = 8 := by
    have h1 : Nat.card (QuaternionGroup 2) = Nat.card N :=
      Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card] at h1
    omega
  have hxmem : x ∈ N := hφx ▸ MonoidHom.mem_range.mpr ⟨.a 1, rfl⟩
  have hymem : y ∈ N := hφy ▸ MonoidHom.mem_range.mpr ⟨.xa 0, rfl⟩
  -- `r ≠ 1`, else `hrx` forces `y = x ∈ zpowers x`, contradicting `hyx`.
  have hrne1 : r ≠ 1 := by
    intro hr1
    apply hyx
    have : y = x := by rw [← hrx, hr1]; group
    rw [this]; exact Subgroup.mem_zpowers x
  have hordr : orderOf r = 3 := by
    have hdvd : orderOf r ∣ 3 := orderOf_dvd_of_pow_eq_one hr3
    have hne1 : orderOf r ≠ 1 := by rw [Ne, orderOf_eq_one_iff]; exact hrne1
    rcases Nat.prime_three.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hCcard : Nat.card (Subgroup.zpowers r) = 3 := by rw [Nat.card_zpowers, hordr]
  -- conjugation-by-`r` formulas for powers of `x`/`y`, needed to show `r` normalizes `N`.
  have hstepN : ∀ n ∈ N, r * n * r⁻¹ ∈ N := by
    intro n hn
    obtain ⟨q, hq⟩ := hn
    rcases q with i | i
    · have hn' : n = x ^ i.val := by rw [← hq]; exact hφa i
      rw [hn']
      have hpow : r * x ^ i.val * r⁻¹ = y ^ i.val := by
        have h := map_pow (MulAut.conj r) x i.val
        rw [MulAut.conj_apply, MulAut.conj_apply, hrx] at h
        exact h
      rw [hpow]
      exact Subgroup.pow_mem N hymem i.val
    · have hn' : n = y * x ^ i.val := by rw [← hq]; exact hφxa i
      rw [hn']
      have hpow : r * (y * x ^ i.val) * r⁻¹ = (x * y) * y ^ i.val := by
        have h1 : r * (y * x ^ i.val) * r⁻¹ = (r * y * r⁻¹) * (r * x ^ i.val * r⁻¹) := by
          group
        have h2 : r * x ^ i.val * r⁻¹ = y ^ i.val := by
          have h := map_pow (MulAut.conj r) x i.val
          rw [MulAut.conj_apply, MulAut.conj_apply, hrx] at h
          exact h
        rw [h1, hry, h2]
      rw [hpow]
      exact Subgroup.mul_mem N (Subgroup.mul_mem N hxmem hymem) (Subgroup.pow_mem N hymem i.val)
  have hrmemNorm : r ∈ Subgroup.normalizer N := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    haveI hNfin : Finite N := Nat.finite_of_card_ne_zero (by omega)
    constructor
    · intro hh; exact hstepN h hh
    · intro hh
      -- the restriction of `conj r` to `N` is an injective self-map of the finite set `N`,
      -- hence bijective; use surjectivity to invert.
      set ψ : N → N := fun n => ⟨r * (n : G) * r⁻¹, hstepN n n.2⟩ with hψ_def
      have hψ_inj : Function.Injective ψ := by
        intro a b hab
        apply Subtype.ext
        have heq : r * (a : G) * r⁻¹ = r * (b : G) * r⁻¹ := congrArg Subtype.val hab
        exact mul_left_cancel (mul_right_cancel heq)
      have hψ_surj : Function.Surjective ψ := Finite.surjective_of_injective hψ_inj
      obtain ⟨⟨h', hh'⟩, hkey⟩ := hψ_surj ⟨r * h * r⁻¹, hh⟩
      have heq : r * h' * r⁻¹ = r * h * r⁻¹ := congrArg Subtype.val hkey
      have hh'h : h' = h := mul_left_cancel (mul_right_cancel heq)
      rwa [hh'h] at hh'
  have hNnormal : N.Normal := by
    have hcompl0 := isComplement'_of_coprime (H := N) (K := Subgroup.zpowers r)
      (show Nat.card N * Nat.card (Subgroup.zpowers r) = Nat.card G by
        rw [hNcard, hCcard, hcard])
      (show Nat.Coprime (Nat.card N) (Nat.card (Subgroup.zpowers r)) by
        rw [hNcard, hCcard]; decide)
    have hsupp : N ⊔ Subgroup.zpowers r = ⊤ := hcompl0.sup_eq_top
    have htop : Subgroup.normalizer (N : Set G) = ⊤ := by
      apply top_unique
      rw [← hsupp]
      exact sup_le Subgroup.le_normalizer (by
        rw [Subgroup.zpowers_le]; exact hrmemNorm)
    exact Subgroup.normalizer_eq_top_iff.mp htop
  refine ⟨φ, hinj, hφa, hφxa, hNnormal, hordr, ?_⟩
  exact isComplement'_of_coprime (by rw [hNcard, hCcard, hcard])
    (by rw [hNcard, hCcard]; decide)

/-- The plain `Equiv` between `zpowers r₁` and `zpowers r₂` (possibly different ambient groups)
sending `r₁ ^ n ↦ r₂ ^ n`, given `r₁`, `r₂` have the same finite order. This is the cross-group
generalization of `Mathlib`'s `zpowersEquivZPowers` (stated for `x y` in the *same* group). -/
private noncomputable def crossZpowersEquiv {G₁ : Type*} [Group G₁] {G₂ : Type*} [Group G₂]
    {r₁ : G₁} {r₂ : G₂}
    (h1 : IsOfFinOrder r₁) (h2 : IsOfFinOrder r₂) (horder : orderOf r₁ = orderOf r₂) :
    Subgroup.zpowers r₁ ≃ Subgroup.zpowers r₂ :=
  (finEquivZPowers h1).symm.trans ((finCongr horder).trans (finEquivZPowers h2))

private lemma crossZpowersEquiv_apply {G₁ : Type*} [Group G₁] {G₂ : Type*} [Group G₂]
    {r₁ : G₁} {r₂ : G₂}
    (h1 : IsOfFinOrder r₁) (h2 : IsOfFinOrder r₂) (horder : orderOf r₁ = orderOf r₂) (n : ℕ) :
    crossZpowersEquiv h1 h2 horder ⟨r₁ ^ n, n, zpow_natCast r₁ n⟩
      = ⟨r₂ ^ n, n, zpow_natCast r₂ n⟩ := by
  rw [crossZpowersEquiv, Equiv.trans_apply, Equiv.trans_apply, finEquivZPowers_symm_apply, ←
    Equiv.eq_symm_apply, finEquivZPowers_symm_apply]
  simp [horder]

/-- The `MulEquiv` between `zpowers r₁` and `zpowers r₂` sending `r₁ ↦ r₂` (generator to
generator), given `r₁`, `r₂` have the same (finite) order. Cross-group generalization of
`Mathlib`'s `zpowersEquivZPowers`, upgraded to a `MulEquiv`. -/
private noncomputable def zpowersMulEquivZPowers {G₁ : Type*} [Group G₁] {G₂ : Type*} [Group G₂]
    {r₁ : G₁} {r₂ : G₂}
    (h1 : IsOfFinOrder r₁) (h2 : IsOfFinOrder r₂) (horder : orderOf r₁ = orderOf r₂) :
    Subgroup.zpowers r₁ ≃* Subgroup.zpowers r₂ :=
  { crossZpowersEquiv h1 h2 horder with
    map_mul' := by
      classical
      intro a b
      obtain ⟨na, hna_mem, hna_eq⟩ :=
        Finset.mem_image.mp (h1.mem_zpowers_iff_mem_range_orderOf.mp a.2)
      obtain ⟨nb, hnb_mem, hnb_eq⟩ :=
        Finset.mem_image.mp (h1.mem_zpowers_iff_mem_range_orderOf.mp b.2)
      have ha_eq : a = (⟨r₁ ^ na, na, zpow_natCast r₁ na⟩ : Subgroup.zpowers r₁) :=
        Subtype.ext hna_eq.symm
      have hb_eq : b = (⟨r₁ ^ nb, nb, zpow_natCast r₁ nb⟩ : Subgroup.zpowers r₁) :=
        Subtype.ext hnb_eq.symm
      have hab_eq : a * b =
          (⟨r₁ ^ (na + nb), na + nb, zpow_natCast r₁ (na + nb)⟩ : Subgroup.zpowers r₁) := by
        rw [ha_eq, hb_eq]; exact Subtype.ext (pow_add r₁ na nb).symm
      simp only [Equiv.toFun_as_coe]
      rw [show a * b = _ from hab_eq, ha_eq, hb_eq, crossZpowersEquiv_apply,
        crossZpowersEquiv_apply, crossZpowersEquiv_apply]
      exact Subtype.ext (pow_add r₂ na nb) }

@[simp] private lemma zpowersMulEquivZPowers_apply {G₁ : Type*} [Group G₁] {G₂ : Type*} [Group G₂]
    {r₁ : G₁} {r₂ : G₂}
    (h1 : IsOfFinOrder r₁) (h2 : IsOfFinOrder r₂) (horder : orderOf r₁ = orderOf r₂) (n : ℕ) :
    (zpowersMulEquivZPowers h1 h2 horder ⟨r₁ ^ n, n, zpow_natCast r₁ n⟩ : G₂) = r₂ ^ n :=
  congrArg Subtype.val (crossZpowersEquiv_apply h1 h2 horder n)

/-- If conjugation by `rr` sends `x ↦ A`, `y ↦ B`, it sends `x^i ↦ A^i` and `y*x^i ↦ B*A^i`. -/
private lemma conj_pow_of {G : Type*} [Group G] (x y rr A B : G)
    (hA : rr * x * rr⁻¹ = A) (hB : rr * y * rr⁻¹ = B) (i : ℕ) :
    rr * x ^ i * rr⁻¹ = A ^ i ∧ rr * (y * x ^ i) * rr⁻¹ = B * A ^ i := by
  have hxi : rr * x ^ i * rr⁻¹ = A ^ i := by
    have h := map_pow (MulAut.conj rr) x i
    rw [MulAut.conj_apply, MulAut.conj_apply, hA] at h
    exact h
  refine ⟨hxi, ?_⟩
  have h1 : rr * (y * x ^ i) * rr⁻¹ = (rr * y * rr⁻¹) * (rr * x ^ i * rr⁻¹) := by group
  rw [h1, hB, hxi]

/-- The conjugation action of `r²` on `x`, `y`, derived from `r`'s action (Butler's "other orbit
direction", tex ~1635-1637). -/
private lemma rsq_conj_formula {G : Type*} [Group G] (x y r : G)
    (hconj : y * x * y⁻¹ = x⁻¹) (hxy2 : x ^ 2 = y ^ 2)
    (hrx : r * x * r⁻¹ = y) (hry : r * y * r⁻¹ = x * y) :
    r ^ 2 * x * (r ^ 2)⁻¹ = x * y ∧ r ^ 2 * y * (r ^ 2)⁻¹ = x := by
  have hstepx : r ^ 2 * x * (r ^ 2)⁻¹ = r * (r * x * r⁻¹) * r⁻¹ := by
    rw [sq, mul_inv_rev]; group
  have hx2 : r ^ 2 * x * (r ^ 2)⁻¹ = x * y := by rw [hstepx, hrx, hry]
  refine ⟨hx2, ?_⟩
  have hstepy : r ^ 2 * y * (r ^ 2)⁻¹ = r * (r * y * r⁻¹) * r⁻¹ := by
    rw [sq, mul_inv_rev]; group
  have hy2 : r ^ 2 * y * (r ^ 2)⁻¹ = r * (x * y) * r⁻¹ := by rw [hstepy, hry]
  have hstepxy : r * (x * y) * r⁻¹ = (r * x * r⁻¹) * (r * y * r⁻¹) := by group
  rw [hy2, hstepxy, hrx, hry]
  -- goal: `y * (x * y) = x`
  have hyx : y * x = x⁻¹ * y := by
    have h := hconj
    have h2 : y * x * y⁻¹ * y = x⁻¹ * y := by rw [h]
    simpa [mul_assoc] using h2
  calc y * (x * y) = (y * x) * y := by group
    _ = (x⁻¹ * y) * y := by rw [hyx]
    _ = x⁻¹ * y ^ 2 := by rw [sq]; group
    _ = x⁻¹ * x ^ 2 := by rw [← hxy2]
    _ = x := by rw [sq]; group

/-- **General recognition/gluing lemma.** If `G₁` and `G₂` are both finite groups of order `24`
carrying elements `x,y,r` satisfying the presentation
`⟨x,y,r | x²=y², yxy⁻¹=x⁻¹, r³=1, rxr⁻¹=y, ryr⁻¹=xy⟩` (Butler's Case IIb / IVb data, tex
~1632/~1639), then `G₁ ≃* G₂`. This is the "semidirect gluing" recognition lemma (divergence
item 8 in `DIVERGENCES.md`): it builds `G₁ ≃* N₁ ⋊ ⟨r₁⟩` and `G₂ ≃* N₂ ⋊ ⟨r₂⟩` (`Nᵢ` the normal
`Q₈` Sylow `2`-subgroup generated by `xᵢ,yᵢ`) via `SemidirectProduct.mulEquivSubgroup`, then glues
the two semidirect products via `SemidirectProduct.congr`, matched generator-to-generator (`N₁ ≃*
N₂` via the two `Q₈` embeddings, `⟨r₁⟩ ≃* ⟨r₂⟩` via `zpowersMulEquivZPowers`). Applying this with
`G₂ := SL(2, ZMod 3)` and Butler's own matrix witnesses gives `mulEquiv_SL2_ZMod3_of` below. -/
private noncomputable def equiv_of_SL2ZMod3_data
    {G₁ : Type*} [Group G₁] [Finite G₁] {G₂ : Type*} [Group G₂] [Finite G₂]
    (x₁ y₁ r₁ : G₁) (hx₁ : orderOf x₁ = 4) (hxy2₁ : x₁ ^ 2 = y₁ ^ 2)
    (hconj₁ : y₁ * x₁ * y₁⁻¹ = x₁⁻¹) (hyx₁ : y₁ ∉ Subgroup.zpowers x₁)
    (hr3₁ : r₁ ^ 3 = 1) (hrx₁ : r₁ * x₁ * r₁⁻¹ = y₁) (hry₁ : r₁ * y₁ * r₁⁻¹ = x₁ * y₁)
    (hcard₁ : Nat.card G₁ = 24)
    (x₂ y₂ r₂ : G₂) (hx₂ : orderOf x₂ = 4) (hxy2₂ : x₂ ^ 2 = y₂ ^ 2)
    (hconj₂ : y₂ * x₂ * y₂⁻¹ = x₂⁻¹) (hyx₂ : y₂ ∉ Subgroup.zpowers x₂)
    (hr3₂ : r₂ ^ 3 = 1) (hrx₂ : r₂ * x₂ * r₂⁻¹ = y₂) (hry₂ : r₂ * y₂ * r₂⁻¹ = x₂ * y₂)
    (hcard₂ : Nat.card G₂ = 24) :
    G₁ ≃* G₂ := by
  classical
  set φ1 := (SL2ZMod3_side x₁ y₁ r₁ hx₁ hxy2₁ hconj₁ hyx₁ hr3₁ hrx₁ hry₁ hcard₁).choose
    with hφ1_def
  obtain ⟨hinj1, hφ1a, hφ1xa, hN1normal, hordr1, hcompl1⟩ :=
    (SL2ZMod3_side x₁ y₁ r₁ hx₁ hxy2₁ hconj₁ hyx₁ hr3₁ hrx₁ hry₁ hcard₁).choose_spec
  set φ2 := (SL2ZMod3_side x₂ y₂ r₂ hx₂ hxy2₂ hconj₂ hyx₂ hr3₂ hrx₂ hry₂ hcard₂).choose
    with hφ2_def
  obtain ⟨hinj2, hφ2a, hφ2xa, hN2normal, hordr2, hcompl2⟩ :=
    (SL2ZMod3_side x₂ y₂ r₂ hx₂ hxy2₂ hconj₂ hyx₂ hr3₂ hrx₂ hry₂ hcard₂).choose_spec
  haveI := hN1normal
  haveI := hN2normal
  set N1 := φ1.range with hN1_def
  set N2 := φ2.range with hN2_def
  -- `N1 ≃* N2` via the two `Q₈` embeddings
  set fn : N1 ≃* N2 := (MonoidHom.ofInjective hinj1).symm.trans (MonoidHom.ofInjective hinj2)
    with hfn_def
  have hfn_formula : ∀ q : QuaternionGroup 2,
      fn ⟨φ1 q, MonoidHom.mem_range.mpr ⟨q, rfl⟩⟩ = ⟨φ2 q, MonoidHom.mem_range.mpr ⟨q, rfl⟩⟩ := by
    intro q
    have h1 : (MonoidHom.ofInjective hinj1) q = (⟨φ1 q, MonoidHom.mem_range.mpr ⟨q, rfl⟩⟩ : N1) :=
      Subtype.ext (MonoidHom.ofInjective_apply hinj1)
    have h2 : (MonoidHom.ofInjective hinj2) q = (⟨φ2 q, MonoidHom.mem_range.mpr ⟨q, rfl⟩⟩ : N2) :=
      Subtype.ext (MonoidHom.ofInjective_apply hinj2)
    show (MonoidHom.ofInjective hinj2) ((MonoidHom.ofInjective hinj1).symm _) = _
    rw [← h1, MulEquiv.symm_apply_apply, h2]
  have hφ1x : φ1 (.a 1) = x₁ := by
    have h1 : (1 : ZMod 4).val = 1 := by decide
    have h := hφ1a 1; rwa [h1, pow_one] at h
  have hφ1y : φ1 (.xa 0) = y₁ := by
    have h0 : (0 : ZMod 4).val = 0 := by decide
    have h := hφ1xa 0; rwa [h0, pow_zero, mul_one] at h
  have hφ2x : φ2 (.a 1) = x₂ := by
    have h1 : (1 : ZMod 4).val = 1 := by decide
    have h := hφ2a 1; rwa [h1, pow_one] at h
  have hφ2y : φ2 (.xa 0) = y₂ := by
    have h0 : (0 : ZMod 4).val = 0 := by decide
    have h := hφ2xa 0; rwa [h0, pow_zero, mul_one] at h
  have hxmem1 : x₁ ∈ N1 := ⟨.a 1, hφ1x⟩
  have hymem1 : y₁ ∈ N1 := ⟨.xa 0, hφ1y⟩
  have hxmem2 : x₂ ∈ N2 := ⟨.a 1, hφ2x⟩
  have hymem2 : y₂ ∈ N2 := ⟨.xa 0, hφ2y⟩
  have hfnx : fn (⟨x₁, hxmem1⟩ : N1) = (⟨x₂, hxmem2⟩ : N2) := by
    have hpre : (⟨φ1 (.a 1), MonoidHom.mem_range.mpr ⟨.a 1, rfl⟩⟩ : N1) = ⟨x₁, hxmem1⟩ :=
      Subtype.ext hφ1x
    have hpost : (⟨φ2 (.a 1), MonoidHom.mem_range.mpr ⟨.a 1, rfl⟩⟩ : N2) = ⟨x₂, hxmem2⟩ :=
      Subtype.ext hφ2x
    rw [← hpre, ← hpost]; exact hfn_formula (.a 1)
  have hfny : fn (⟨y₁, hymem1⟩ : N1) = (⟨y₂, hymem2⟩ : N2) := by
    have hpre : (⟨φ1 (.xa 0), MonoidHom.mem_range.mpr ⟨.xa 0, rfl⟩⟩ : N1) = ⟨y₁, hymem1⟩ :=
      Subtype.ext hφ1y
    have hpost : (⟨φ2 (.xa 0), MonoidHom.mem_range.mpr ⟨.xa 0, rfl⟩⟩ : N2) = ⟨y₂, hymem2⟩ :=
      Subtype.ext hφ2y
    rw [← hpre, ← hpost]; exact hfn_formula (.xa 0)
  -- `zpowers r₁ ≃* zpowers r₂`, generator to generator
  have hr1fin : IsOfFinOrder r₁ := orderOf_pos_iff.mp (by rw [hordr1]; norm_num)
  have hr2fin : IsOfFinOrder r₂ := orderOf_pos_iff.mp (by rw [hordr2]; norm_num)
  have hordeq : orderOf r₁ = orderOf r₂ := hordr1.trans hordr2.symm
  set fg : Subgroup.zpowers r₁ ≃* Subgroup.zpowers r₂ := zpowersMulEquivZPowers hr1fin hr2fin hordeq
    with hfg_def
  set gen1 : Subgroup.zpowers r₁ := ⟨r₁, Subgroup.mem_zpowers r₁⟩ with hgen1_def
  set gen2 : Subgroup.zpowers r₂ := ⟨r₂, Subgroup.mem_zpowers r₂⟩ with hgen2_def
  have hfg_gen : fg gen1 = gen2 := by
    apply Subtype.ext
    have hval_eq : (gen1 : G₁) = r₁ ^ 1 := (pow_one r₁).symm
    have hcast : gen1 = (⟨r₁ ^ 1, 1, zpow_natCast r₁ 1⟩ : Subgroup.zpowers r₁) :=
      Subtype.ext hval_eq
    have hstep := congrArg (fun z => (fg z : G₂)) hcast
    have h := zpowersMulEquivZPowers_apply hr1fin hr2fin hordeq 1
    rw [hstep, h, pow_one]
  -- the (concrete, `rfl`-provable) conjugation action underlying `SemidirectProduct.mulEquivSubgroup`
  set φ1' : Subgroup.zpowers r₁ →* MulAut N1 :=
    N1.normalizerMonoidHom.comp (Subgroup.inclusion (N1.normalizer_eq_top ▸ le_top))
    with hφ1'_def
  set φ2' : Subgroup.zpowers r₂ →* MulAut N2 :=
    N2.normalizerMonoidHom.comp (Subgroup.inclusion (N2.normalizer_eq_top ▸ le_top))
    with hφ2'_def
  have hφ1'_apply : ∀ (c : Subgroup.zpowers r₁) (n : N1),
      ((φ1' c) n : G₁) = (c : G₁) * (n : G₁) * (c : G₁)⁻¹ := fun _ _ => rfl
  have hφ2'_apply : ∀ (c : Subgroup.zpowers r₂) (n : N2),
      ((φ2' c) n : G₂) = (c : G₂) * (n : G₂) * (c : G₂)⁻¹ := fun _ _ => rfl
  -- conjugation-by-`r²` formulas (Butler's "other orbit direction")
  obtain ⟨hr1sq_x, hr1sq_y⟩ := rsq_conj_formula x₁ y₁ r₁ hconj₁ hxy2₁ hrx₁ hry₁
  obtain ⟨hr2sq_x, hr2sq_y⟩ := rsq_conj_formula x₂ y₂ r₂ hconj₂ hxy2₂ hrx₂ hry₂
  -- core step: matching conjugation-of-generators data on both sides propagates to all of `N1`
  have hcore : ∀ (c1 : Subgroup.zpowers r₁) (A1 B1 : G₁) (c2 : Subgroup.zpowers r₂) (A2 B2 : G₂)
      (_ : (c1 : G₁) * x₁ * (c1 : G₁)⁻¹ = A1) (_ : (c1 : G₁) * y₁ * (c1 : G₁)⁻¹ = B1)
      (_ : (c2 : G₂) * x₂ * (c2 : G₂)⁻¹ = A2) (_ : (c2 : G₂) * y₂ * (c2 : G₂)⁻¹ = B2)
      (hAmem1 : A1 ∈ N1) (hBmem1 : B1 ∈ N1) (hAmem2 : A2 ∈ N2) (hBmem2 : B2 ∈ N2)
      (_ : fn (⟨A1, hAmem1⟩ : N1) = (⟨A2, hAmem2⟩ : N2))
      (_ : fn (⟨B1, hBmem1⟩ : N1) = (⟨B2, hBmem2⟩ : N2)),
      (φ1' c1).trans fn = fn.trans (φ2' c2) := by
    intro c1 A1 B1 c2 A2 B2 hA1 hB1 hA2 hB2 hAmem1 hBmem1 hAmem2 hBmem2 hfnA hfnB
    apply MulEquiv.ext
    intro n
    obtain ⟨q, hq⟩ := n.2
    rcases q with i | i
    · have hn_eq : n = (⟨x₁, hxmem1⟩ : N1) ^ i.val := by
        apply Subtype.ext; rw [SubmonoidClass.coe_pow, ← hq]; exact hφ1a i
      obtain ⟨hform1, -⟩ := conj_pow_of x₁ y₁ (c1 : G₁) A1 B1 hA1 hB1 i.val
      obtain ⟨hform2, -⟩ := conj_pow_of x₂ y₂ (c2 : G₂) A2 B2 hA2 hB2 i.val
      have hkey : (φ1' c1) n = (⟨A1, hAmem1⟩ : N1) ^ i.val := by
        apply Subtype.ext
        rw [hφ1'_apply, hn_eq, SubmonoidClass.coe_pow, hform1, SubmonoidClass.coe_pow]
      have hfnn : (fn n : G₂) = x₂ ^ i.val := by
        rw [hn_eq, map_pow, hfnx, SubmonoidClass.coe_pow]
      apply Subtype.ext
      show (fn ((φ1' c1) n) : G₂) = ((φ2' c2) (fn n) : G₂)
      rw [hkey, map_pow, hfnA, hφ2'_apply, hfnn, hform2, SubmonoidClass.coe_pow]
    · have hn_eq : n = (⟨y₁, hymem1⟩ : N1) * (⟨x₁, hxmem1⟩ : N1) ^ i.val := by
        apply Subtype.ext
        rw [Subgroup.coe_mul, SubmonoidClass.coe_pow, ← hq]; exact hφ1xa i
      obtain ⟨hform1, hform1'⟩ := conj_pow_of x₁ y₁ (c1 : G₁) A1 B1 hA1 hB1 i.val
      obtain ⟨hform2, hform2'⟩ := conj_pow_of x₂ y₂ (c2 : G₂) A2 B2 hA2 hB2 i.val
      have hkey : (φ1' c1) n = (⟨B1, hBmem1⟩ : N1) * (⟨A1, hAmem1⟩ : N1) ^ i.val := by
        apply Subtype.ext
        rw [hφ1'_apply, hn_eq, Subgroup.coe_mul, SubmonoidClass.coe_pow, hform1',
          Subgroup.coe_mul, SubmonoidClass.coe_pow]
      have hfnn : (fn n : G₂) = y₂ * x₂ ^ i.val := by
        rw [hn_eq, map_mul, map_pow, hfnx, hfny, Subgroup.coe_mul, SubmonoidClass.coe_pow]
      apply Subtype.ext
      show (fn ((φ1' c1) n) : G₂) = ((φ2' c2) (fn n) : G₂)
      rw [hkey, map_mul, map_pow, hfnA, hfnB, hφ2'_apply, hfnn, hform2', Subgroup.coe_mul,
        SubmonoidClass.coe_pow]
  have hxymem1 : x₁ * y₁ ∈ N1 := Subgroup.mul_mem N1 hxmem1 hymem1
  have hxymem2 : x₂ * y₂ ∈ N2 := Subgroup.mul_mem N2 hxmem2 hymem2
  have hfnxy : fn (⟨x₁ * y₁, hxymem1⟩ : N1) = (⟨x₂ * y₂, hxymem2⟩ : N2) := by
    have heq : (⟨x₁ * y₁, hxymem1⟩ : N1) = (⟨x₁, hxmem1⟩ : N1) * (⟨y₁, hymem1⟩ : N1) := rfl
    rw [heq, map_mul, hfnx, hfny]; rfl
  have hcompat : ∀ c : Subgroup.zpowers r₁, (φ1' c).trans fn = fn.trans (φ2' (fg c)) := by
    intro c
    obtain ⟨m, hm_mem, hm_eq⟩ :=
      Finset.mem_image.mp (hr1fin.mem_zpowers_iff_mem_range_orderOf.mp c.2)
    have hm_lt : m < 3 := by have := Finset.mem_range.mp hm_mem; rwa [hordr1] at this
    have hc_eq : c = gen1 ^ m := by
      apply Subtype.ext; rw [SubmonoidClass.coe_pow]; exact hm_eq.symm
    have hfgc_eq : fg c = gen2 ^ m := by rw [hc_eq, map_pow, hfg_gen]
    interval_cases m
    · have hc0 : c = 1 := by rw [hc_eq, pow_zero]
      subst hc0
      rw [map_one fg, map_one, map_one]
      apply MulEquiv.ext
      intro n
      simp
    · have hc1 : (c : G₁) = r₁ := by rw [hc_eq, pow_one]
      have hfgc1 : (fg c : G₂) = r₂ := by rw [hfgc_eq, pow_one]
      exact hcore c y₁ (x₁ * y₁) (fg c) y₂ (x₂ * y₂)
        (by rw [hc1]; exact hrx₁) (by rw [hc1]; exact hry₁)
        (by rw [hfgc1]; exact hrx₂) (by rw [hfgc1]; exact hry₂)
        hymem1 hxymem1 hymem2 hxymem2 hfny hfnxy
    · have hc2 : (c : G₁) = r₁ ^ 2 := by rw [hc_eq, SubmonoidClass.coe_pow]
      have hfgc2 : (fg c : G₂) = r₂ ^ 2 := by rw [hfgc_eq, SubmonoidClass.coe_pow]
      exact hcore c (x₁ * y₁) x₁ (fg c) (x₂ * y₂) x₂
        (by rw [hc2]; exact hr1sq_x) (by rw [hc2]; exact hr1sq_y)
        (by rw [hfgc2]; exact hr2sq_x) (by rw [hfgc2]; exact hr2sq_y)
        hxymem1 hxmem1 hxymem2 hxmem2 hfnxy hfnx
  exact (SemidirectProduct.mulEquivSubgroup hcompl1).symm.trans
    ((SemidirectProduct.congr fn fg hcompat).trans (SemidirectProduct.mulEquivSubgroup hcompl2))

open Matrix MatrixGroups in
/-- Butler's witnesses for `SL(2,3)` (tex ~1642-1650): `a` has order `4`, `b` inverts `a` with
`a² = b²`, and `c` (order `3`) conjugates `a ↦ b`, `b ↦ a b` -- but, with our convention
`r x r⁻¹ = y` (`r`, not `r⁻¹`, does the conjugating), it is `c⁻¹` and not `c` that plays the role
of `r` (verified directly below by `decide`, since `SL(2, ZMod 3)` is a finite `DecidableEq`
type); this is a presentation-level convention mismatch only (`⟨a,b,c⟩ = ⟨a,b,c⁻¹⟩`), not a
mathematical divergence. -/
private def Butler_a : SL(2, ZMod 3) := ⟨!![1, 1; 1, 2], by decide⟩

open Matrix MatrixGroups in
private def Butler_b : SL(2, ZMod 3) := ⟨!![0, 2; 1, 0], by decide⟩

open Matrix MatrixGroups in
private def Butler_c : SL(2, ZMod 3) := ⟨!![2, 1; 2, 0], by decide⟩

open Matrix MatrixGroups in
/-- `r := c⁻¹`, see `Butler_a`'s docstring. -/
private def Butler_r : SL(2, ZMod 3) := Butler_c⁻¹

private lemma Butler_a_orderOf : orderOf Butler_a = 4 := by
  have h4 : Butler_a ^ 4 = 1 := by decide
  have h2 : Butler_a ^ 2 ≠ 1 := by decide
  have h1 : Butler_a ≠ 1 := by decide
  have hdvd : orderOf Butler_a ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have hpos : 0 < orderOf Butler_a := orderOf_pos Butler_a
  have hle : orderOf Butler_a ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  have hpow : Butler_a ^ orderOf Butler_a = 1 := pow_orderOf_eq_one Butler_a
  interval_cases (orderOf Butler_a) <;> simp_all

private lemma Butler_b_notMem_zpowers_a : Butler_b ∉ Subgroup.zpowers Butler_a := by
  classical
  intro hmem
  rw [mem_zpowers_iff_mem_range_orderOf, Butler_a_orderOf] at hmem
  simp only [Finset.mem_image, Finset.mem_range] at hmem
  obtain ⟨k, hk, hke⟩ := hmem
  interval_cases k <;> revert hke <;> decide

open Matrix MatrixGroups in
private lemma card_SL2ZMod3 : Nat.card SL(2, ZMod 3) = 24 := by
  rw [Nat.card_eq_fintype_card]; decide

open Matrix MatrixGroups in
/-- **Recognition lemma for `SL(2,3)`.** If `G` is a finite group of order `24` containing
`x y r : G` with `x² = y²`, `orderOf x = 4`, `y x y⁻¹ = x⁻¹` (i.e. `⟨x,y⟩` is a copy of `Q₈`, cf.
`mulEquiv_quaternionGroup_of` with `n = 2`), and an order-`3` element `r` acting on `⟨x,y⟩` by
`r x r⁻¹ = y`, `r y r⁻¹ = x y`, then `G` is (abstractly) `SL(2, ZMod 3)`.

This is the presentation `⟨x,y,r | x²=y², yxy⁻¹=x⁻¹, r³=1, rxr⁻¹=y, ryr⁻¹=xy⟩` used by Butler for
Case IIb (tex ~1512-1653, `g₁ = 3`) and Case IVb (tex ~1785, "analogous to Case IIb"): `x, y`
generate the normal Sylow `2`-subgroup `N ≅ Q₈`, and `r` generates a complement of order `3`
acting on `N` by the given (`3`-cycle-like) automorphism (Butler's "orbit cycle" on the three
conjugates of `⟨x⟩`, tex ~1589-1637). See `equiv_of_SL2ZMod3_data`'s docstring for the proof
route (semidirect gluing, divergence item 8 in `DIVERGENCES.md`). -/
noncomputable def mulEquiv_SL2_ZMod3_of {G : Type*} [Group G] [Finite G] (x y r : G)
    (hx : orderOf x = 4) (hxy2 : x ^ 2 = y ^ 2) (hconj : y * x * y⁻¹ = x⁻¹)
    (hyx : y ∉ Subgroup.zpowers x) (hr3 : r ^ 3 = 1)
    (hrx : r * x * r⁻¹ = y) (hry : r * y * r⁻¹ = x * y) (hcard : Nat.card G = 24) :
    G ≃* SL(2, ZMod 3) :=
  equiv_of_SL2ZMod3_data x y r hx hxy2 hconj hyx hr3 hrx hry hcard
    Butler_a Butler_b Butler_r Butler_a_orderOf (by decide) (by decide)
    Butler_b_notMem_zpowers_a (by decide) (by decide) (by decide) card_SL2ZMod3

end SL2ZMod3

end Ch7GroupRecognition
