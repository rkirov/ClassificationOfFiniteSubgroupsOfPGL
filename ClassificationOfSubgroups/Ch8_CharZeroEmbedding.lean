import Mathlib

/-!
# Reduction mod ℓ of a finite subgroup of `SL₂` over an algebraically closed field of char 0

This file proves the **Minkowski–Serre reduction lemma** in the special case of `SL(2, K)`:
every finite subgroup `G ≤ SL(2, K)`, where `K` is an algebraically closed field of
characteristic `0`, embeds into `SL(2, 𝔽̄_ℓ)` for a suitable prime `ℓ` coprime to `|G|`
(and different from `2`).

## Mathematical outline (E. Minkowski, J-P. Serre)

1. Let `S ⊆ K` be the (finite) set of all matrix entries of all `g ∈ G` together with a
   chosen eigenvalue of each `g` (a root of its characteristic polynomial
   `X² − (tr g)·X + 1`, which exists because `K` is algebraically closed).  Let
   `R := ℤ[S]` be the finitely generated `ℤ`-subalgebra of `K` they generate.
2. Because `R` is a finite-type `ℤ`-algebra and a domain, it is a Jacobson ring, so its
   Jacobson radical is `0`.  As `N := 2·|G| ≠ 0`, there is a maximal ideal `m` of `R` with
   `N ∉ m`.  By the arithmetic Nullstellensatz (a field of finite type over `ℤ` is finite),
   the residue field `F := R ⧸ m` is **finite**; let `ℓ := ringChar F`, a prime.  Since `N`
   is invertible mod `m`, `ℓ ∤ 2·|G|`, giving `ℓ ≠ 2` and `Nat.Coprime |G| ℓ`.
3. The entries of every `g ∈ G` lie in `R`, so `G` corestricts to `SL(2, R)`; reducing mod
   `m` and embedding `F ↪ 𝔽̄_ℓ` produces `f : G →* SL(2, 𝔽̄_ℓ)`.
4. **Injectivity** (kernel triviality): if `g` reduces to `1` and `g ≠ 1`, examine an
   eigenvalue `λ` of `g`.  If `λ = 1` then `tr g = 2`, `(g − 1)² = 0`, and `gⁿ = 1`
   (`n := orderOf g`) forces `n·(g − 1) = 0`, hence `g = 1` by `CharZero`.  Otherwise `λ`
   is a primitive `d`-th root of unity (`d = orderOf λ > 1`, `d ∣ n`), and cyclotomic
   evaluation `Φ_d(1) ∈ {1, prime factor of d}` shows `1 − λ` cannot become `0` in `F`
   unless `ℓ ∣ n`, contradicting `ℓ ∤ |G|`.

## Note on the statement (deviation from the requested signature)

`AlgebraicClosure (ZMod ℓ)` requires a `Field (ZMod ℓ)` instance, which is only available in
the presence of `Fact (Nat.Prime ℓ)`.  A bare `∃ ℓ, Nat.Prime ℓ ∧ … SL(2, 𝔽̄_ℓ) …` does **not
type-check** (the `Nat.Prime ℓ` conjunct is not an instance when elaborating the codomain of
`f`).  We therefore bundle the primality as an instance argument:
`∃ (ℓ : ℕ) (_ : Fact (Nat.Prime ℓ)), ℓ ≠ 2 ∧ Nat.Coprime (Nat.card G) ℓ ∧ ∃ f …`.
Consumers recover `Nat.Prime ℓ` from the bundled `Fact` via `.out`.

## Main statement

* `CharZeroEmbedding.klein_embed`
-/

open Polynomial
open scoped Matrix

namespace CharZeroEmbedding

-- L1: ℤ is a Jacobson ring.
theorem int_isJacobsonRing : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  rcases eq_or_ne P ⊥ with rfl | hne
  · apply le_antisymm _ Ideal.le_jacobson
    intro x hx
    rw [Ideal.mem_jacobson_bot] at hx
    have hu := hx x
    rw [Int.isUnit_iff] at hu
    rcases hu with h | h
    · have hxx : x * x = 0 := by linarith
      simpa [Ideal.mem_bot] using (mul_self_eq_zero.mp hxx)
    · nlinarith [mul_self_nonneg x]
  · haveI : P.IsMaximal := Ideal.IsPrime.isMaximal hP hne
    exact Ideal.jacobson_eq_self_of_isMaximal

-- L2: ℚ is not finitely generated as ℤ-module.
theorem not_moduleFinite_int_rat : ¬ Module.Finite ℤ ℚ := by
  intro h
  obtain ⟨s, hs⟩ := h.fg_top
  set D : ℕ := ∏ q ∈ s, q.den with hDdef
  have hDpos : 0 < D := Finset.prod_pos (fun q _ => q.pos)
  have hD1 : (1 : ℤ) ≤ (D : ℤ) := by exact_mod_cast hDpos
  let T : Submodule ℤ ℚ :=
    { carrier := {x : ℚ | x.den ∣ D}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at *
        exact (Rat.add_den_dvd_lcm a b).trans (Nat.lcm_dvd ha hb)
      smul_mem' := by
        intro c a ha
        simp only [Set.mem_setOf_eq] at *
        have h1 : (c • a).den ∣ a.den := by
          rw [zsmul_eq_mul]
          refine (Rat.mul_den_dvd _ _).trans ?_
          simp [Rat.den_intCast]
        exact h1.trans ha }
  have hsT : (s : Set ℚ) ⊆ (T : Set ℚ) := by
    intro q hq
    exact Finset.dvd_prod_of_mem (fun q => q.den) hq
  have hTtop : T = ⊤ := by
    apply top_le_iff.mp
    rw [← hs]
    exact Submodule.span_le.mpr hsT
  -- witness
  set q₀ : ℚ := Rat.divInt 1 ((D : ℤ) + 1) with hq0
  have hq0mem : q₀.den ∣ D := by
    have hmem : q₀ ∈ T := by rw [hTtop]; exact Submodule.mem_top
    exact hmem
  have hq0den2 : (q₀.den : ℤ) ∣ ((D : ℤ) + 1) := Rat.den_dvd 1 ((D : ℤ) + 1)
  have hdvd1 : (q₀.den : ℤ) ∣ 1 := by
    have h1 : (q₀.den : ℤ) ∣ (D : ℤ) := Int.natCast_dvd_natCast.mpr hq0mem
    have := dvd_sub hq0den2 h1
    simpa using this
  have hden1 : q₀.den = 1 := by
    have : (q₀.den : ℤ) = 1 := Int.eq_one_of_dvd_one (by positivity) hdvd1
    exact_mod_cast this
  -- q₀.den = 1 ⟹ q₀.num * (D+1) = 1, impossible
  have hnum : (q₀.num : ℚ) = q₀ := (Rat.den_eq_one_iff q₀).mp hden1
  have h2 : Rat.divInt q₀.num 1 = Rat.divInt 1 ((D : ℤ) + 1) := by
    rw [Rat.divInt_one, hnum]
  have hcross : q₀.num * ((D : ℤ) + 1) = 1 * 1 :=
    (Rat.divInt_eq_divInt_iff one_ne_zero (by positivity)).mp h2
  have hle : ((D : ℤ) + 1) ∣ 1 := ⟨q₀.num, by linarith [hcross]⟩
  have := Int.le_of_dvd (by norm_num) hle
  omega

-- L3: a field that is module-finite over ℤ is finite.
theorem finite_of_moduleFinite_int (F : Type*) [Field F] [Module.Finite ℤ F] : Finite F := by
  obtain ⟨p, hp⟩ := CharP.exists F
  rcases eq_or_ne p 0 with rfl | hp0
  · exfalso
    haveI : CharZero F := CharP.charP_to_charZero F
    -- ℚ embeds ℤ-linearly into F
    let f : ℚ →ₗ[ℤ] F := (Rat.castHom F).toAddMonoidHom.toIntLinearMap
    have hf : Function.Injective f := Rat.cast_injective
    haveI : Module.Finite ℤ ℚ :=
      Module.Finite.equiv (LinearEquiv.ofInjective f hf).symm
    exact not_moduleFinite_int_rat ‹_›
  · haveI := hp
    have htor : Module.IsTorsion ℤ F := by
      intro x
      refine ⟨⟨(p : ℤ), ?_⟩, ?_⟩
      · rw [mem_nonZeroDivisors_iff_ne_zero]; exact_mod_cast hp0
      · show (p : ℤ) • x = 0
        have hp0F : ((p : ℤ) : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F p
        rw [zsmul_eq_mul, hp0F, zero_mul]
    exact Module.finite_of_fg_torsion F htor

-- Residue-field step: a finite-type ℤ-domain has a maximal ideal avoiding a given
-- nonzero element, with finite residue field.
theorem residue_of_finiteType (R : Type*) [CommRing R] [IsDomain R]
    [Algebra.FiniteType ℤ R] (N : R) (hN : N ≠ 0) :
    ∃ m : Ideal R, m.IsMaximal ∧ N ∉ m ∧ Finite (R ⧸ m) := by
  haveI : IsJacobsonRing ℤ := int_isJacobsonRing
  haveI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := ℤ) (B := R)
  have hbot : (Ideal.jacobson (⊥ : Ideal R)) = ⊥ :=
    IsJacobsonRing.out ‹IsJacobsonRing R› Ideal.isRadical_bot_of_noZeroDivisors
  have hNnotin : N ∉ Ideal.jacobson (⊥ : Ideal R) := by
    rw [hbot]; simpa [Ideal.mem_bot] using hN
  rw [Ideal.jacobson, Ideal.mem_sInf] at hNnotin
  push_neg at hNnotin
  obtain ⟨m, ⟨_, hmax⟩, hNm⟩ := hNnotin
  refine ⟨m, hmax, hNm, ?_⟩
  haveI : m.IsMaximal := hmax
  letI fld : Field (R ⧸ m) := Ideal.Quotient.field m
  letI alg : Algebra ℤ (R ⧸ m) := Ideal.instAlgebraQuotient ℤ m
  haveI hft : Algebra.FiniteType ℤ (R ⧸ m) :=
    Algebra.FiniteType.trans (S := R) inferInstance inferInstance
  haveI hmf : Module.Finite ℤ (R ⧸ m) :=
    @finite_of_finite_type_of_isJacobsonRing ℤ (R ⧸ m) _ fld alg _ hft
  exact finite_of_moduleFinite_int (R ⧸ m)

-- A finite field embeds into the algebraic closure of its prime field.
theorem finiteField_embeds (F : Type*) [Field F] [Finite F] :
    ∃ (ℓ : ℕ) (_ : Fact (Nat.Prime ℓ)), CharP F ℓ ∧
      ∃ g : F →+* AlgebraicClosure (ZMod ℓ), Function.Injective g := by
  set ℓ := ringChar F with hℓ
  haveI : CharP F ℓ := ringChar.charP F
  have hℓprime : Nat.Prime ℓ := CharP.prime_ringChar F
  haveI hfact : Fact ℓ.Prime := ⟨hℓprime⟩
  letI : Algebra (ZMod ℓ) F := ZMod.algebra _ _
  let emb : F →ₐ[ZMod ℓ] AlgebraicClosure (ZMod ℓ) := IsAlgClosed.lift
  exact ⟨ℓ, hfact, inferInstance, emb.toRingHom, emb.toRingHom.injective⟩

-- Core eigenvalue fact: a root of the char. polynomial of a finite-order SL₂ matrix
-- is a root of unity of the same order dividing.
theorem eigen_pow {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K)
    (hdet : M.det = 1) (μ : K) (hμ : μ ^ 2 - (M 0 0 + M 1 1) * μ + 1 = 0)
    (n : ℕ) (hn : M ^ n = 1) : μ ^ n = 1 := by
  have hdetM : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    rw [← Matrix.det_fin_two]; exact hdet
  have e00 : (M - μ • (1 : Matrix (Fin 2) (Fin 2) K)) 0 0 = M 0 0 - μ := by
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  have e11 : (M - μ • (1 : Matrix (Fin 2) (Fin 2) K)) 1 1 = M 1 1 - μ := by
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  have e01 : (M - μ • (1 : Matrix (Fin 2) (Fin 2) K)) 0 1 = M 0 1 := by
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)]
  have e10 : (M - μ • (1 : Matrix (Fin 2) (Fin 2) K)) 1 0 = M 1 0 := by
    simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
  have hdet0 : (M - μ • (1 : Matrix (Fin 2) (Fin 2) K)).det = 0 := by
    rw [Matrix.det_fin_two, e00, e11, e01, e10]
    linear_combination hμ + hdetM
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet0
  have hMv : M *ᵥ v = μ • v := by
    have h0 : (M - μ • (1 : Matrix (Fin 2) (Fin 2) K)) *ᵥ v = 0 := hv
    rwa [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at h0
  have hpow : ∀ k, M ^ k *ᵥ v = μ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, hMv, smul_smul, pow_succ]
  have hfin := hpow n
  rw [hn, Matrix.one_mulVec] at hfin
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hc : v i = μ ^ n * v i := by
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun hfin i
  have hstep : (μ ^ n - 1) * v i = 0 := by linear_combination -hc
  rcases mul_eq_zero.mp hstep with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hi

-- Cyclotomic contradiction: a primitive d-th root (d>1, d ∣ n) cannot reduce to 1
-- through φ when ℓ = char F does not divide n.
theorem cyclotomic_contra {R : Type*} [CommRing R] [IsDomain R] {F : Type*} [Field F]
    (φ : R →+* F) (ℓ : ℕ) [CharP F ℓ] (n : ℕ) (hℓn : ¬ ℓ ∣ n)
    (μ : R) (d : ℕ) (hd : 1 < d) (hdn : d ∣ n) (hprim : IsPrimitiveRoot μ d)
    (hφμ : φ μ = 1) : False := by
  have hdpos : 0 < d := by omega
  have hroot : (Polynomial.cyclotomic d R).IsRoot μ := hprim.isRoot_cyclotomic hdpos
  obtain ⟨h, hh⟩ := (Polynomial.dvd_iff_isRoot).mpr hroot
  have heval : (Polynomial.cyclotomic d R).eval 1 = (1 - μ) * h.eval 1 := by
    rw [hh]; simp [Polynomial.eval_mul]
  by_cases hpp : IsPrimePow d
  · obtain ⟨q, k, hq, hk, hqd⟩ := hpp
    haveI : Fact (Nat.Prime q) := ⟨Nat.prime_iff.mpr hq⟩
    have hkk : k - 1 + 1 = k := by omega
    have hev1 : (Polynomial.cyclotomic d R).eval 1 = (q : R) := by
      rw [← hqd, ← hkk, Polynomial.eval_one_cyclotomic_prime_pow]
    rw [hev1] at heval
    have hqF : (q : F) = 0 := by
      have := congrArg φ heval
      rw [map_natCast, map_mul, map_sub, map_one, hφμ, sub_self, zero_mul] at this
      exact this
    have hℓq : ℓ ∣ q := (CharP.cast_eq_zero_iff F ℓ q).mp hqF
    have hqdvd : q ∣ d := hqd ▸ dvd_pow_self q (by omega : k ≠ 0)
    exact hℓn (hℓq.trans (hqdvd.trans hdn))
  · have hnpp : ∀ {p : ℕ}, p.Prime → ∀ j : ℕ, p ^ j ≠ d := by
      intro p hp j hpj
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp at hpj; omega
      · exact hpp ⟨p, j, Nat.prime_iff.mp hp, hj, hpj⟩
    have hev1 : (Polynomial.cyclotomic d R).eval 1 = 1 :=
      Polynomial.eval_one_cyclotomic_not_prime_pow hnpp
    rw [hev1] at heval
    have hunit : IsUnit (1 - μ) := IsUnit.of_mul_eq_one _ heval.symm
    have : IsUnit (φ (1 - μ)) := hunit.map φ
    rw [map_sub, map_one, hφμ, sub_self] at this
    exact not_isUnit_zero this

theorem klein_embed {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    (G : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)) [Finite G] :
    ∃ (ℓ : ℕ) (_ : Fact (Nat.Prime ℓ)), ℓ ≠ 2 ∧ Nat.Coprime (Nat.card G) ℓ ∧
      ∃ f : G →* Matrix.SpecialLinearGroup (Fin 2) (AlgebraicClosure (ZMod ℓ)),
        Function.Injective f := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  -- eigenvalue chooser: a root of X² - (tr x)·X + 1 for each matrix x
  have hroot : ∀ x : Matrix.SpecialLinearGroup (Fin 2) K, ∃ μ : K,
      μ ^ 2 - ((x : Matrix (Fin 2) (Fin 2) K) 0 0
        + (x : Matrix (Fin 2) (Fin 2) K) 1 1) * μ + 1 = 0 := by
    intro x
    set t := (x : Matrix (Fin 2) (Fin 2) K) 0 0 + (x : Matrix (Fin 2) (Fin 2) K) 1 1
    have hdeg : (X ^ 2 - C t * X + C 1 : K[X]).degree = 2 := by compute_degree!
    obtain ⟨μ, hμ⟩ := IsAlgClosed.exists_root (p := (X ^ 2 - C t * X + C 1 : K[X]))
      (by rw [hdeg]; decide)
    refine ⟨μ, ?_⟩
    have h2 : (X ^ 2 - C t * X + C 1 : K[X]).eval μ = 0 := hμ
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at h2
    linear_combination h2
  let eig : Matrix.SpecialLinearGroup (Fin 2) K → K := fun x => (hroot x).choose
  have heig : ∀ x, (eig x) ^ 2 - ((x : Matrix (Fin 2) (Fin 2) K) 0 0
      + (x : Matrix (Fin 2) (Fin 2) K) 1 1) * (eig x) + 1 = 0 := fun x => (hroot x).choose_spec
  -- finite generating set of K
  let Sset : Set K :=
    Set.range (fun p : G × Fin 2 × Fin 2 =>
      ((p.1 : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) p.2.1 p.2.2)
    ∪ Set.range (fun g : G => eig (g : Matrix.SpecialLinearGroup (Fin 2) K))
  have hSfin : Sset.Finite := (Set.finite_range _).union (Set.finite_range _)
  set R := Algebra.adjoin ℤ Sset with hRdef
  haveI hRID : IsDomain R := by rw [hRdef]; infer_instance
  haveI hRFT : Algebra.FiniteType ℤ R := by
    rw [hRdef]; exact Algebra.FiniteType.adjoin_of_finite hSfin
  have entry_mem : ∀ (x : Matrix.SpecialLinearGroup (Fin 2) K), x ∈ G → ∀ i j,
      (x : Matrix (Fin 2) (Fin 2) K) i j ∈ R := by
    intro x hx i j
    exact Algebra.subset_adjoin (Or.inl ⟨(⟨x, hx⟩, i, j), rfl⟩)
  have eig_mem : ∀ (g : G), eig (g : Matrix.SpecialLinearGroup (Fin 2) K) ∈ R := by
    intro g
    exact Algebra.subset_adjoin (Or.inr ⟨g, rfl⟩)
  -- N = 2·|G| is a nonzero element of R
  set N : R := ((2 * Nat.card G : ℕ) : R) with hNdef
  have hNne : N ≠ 0 := by
    intro h
    have h2 : ((2 * Nat.card G : ℕ) : K) = 0 := by
      have := congrArg (Subalgebra.val R) h
      simpa [hNdef, map_natCast] using this
    have h3 : (2 * Nat.card G : ℕ) = 0 := by exact_mod_cast h2
    have : 0 < Nat.card G := Nat.card_pos
    omega
  obtain ⟨m, hmax, hNm, hFfin⟩ := @residue_of_finiteType R _ hRID hRFT N hNne
  haveI : m.IsMaximal := hmax
  letI : Field (R ⧸ m) := Ideal.Quotient.field m
  haveI : Finite (R ⧸ m) := hFfin
  obtain ⟨ℓ, hℓfact, hℓchar, g_emb, hg_emb⟩ := finiteField_embeds (R ⧸ m)
  haveI : Fact (Nat.Prime ℓ) := hℓfact
  haveI : CharP (R ⧸ m) ℓ := hℓchar
  -- coprimality facts
  have hmkN : (Ideal.Quotient.mk m) N ≠ 0 := fun h => hNm (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hℓN : ¬ ℓ ∣ (2 * Nat.card G) := by
    intro hdvd
    apply hmkN
    have hz : ((2 * Nat.card G : ℕ) : R ⧸ m) = 0 := (CharP.cast_eq_zero_iff (R ⧸ m) ℓ _).mpr hdvd
    rw [hNdef]; rw [map_natCast]; exact hz
  have hℓ2 : ℓ ≠ 2 := by rintro rfl; exact hℓN ⟨Nat.card G, by ring⟩
  have hcop : Nat.Coprime (Nat.card G) ℓ := by
    have hnd : ¬ ℓ ∣ Nat.card G := fun h => hℓN (Dvd.dvd.mul_left h 2)
    exact (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hℓfact.out).mpr hnd))
  -- the reduction homomorphism
  let e : R →+* K := (Subalgebra.val R).toRingHom
  have he_inj : Function.Injective e := Subtype.val_injective
  let ι : Matrix.SpecialLinearGroup (Fin 2) R →* Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.map e
  have hι_inj : Function.Injective ι := by
    intro A B hAB
    ext i j
    have h1 : (ι A : Matrix (Fin 2) (Fin 2) K) i j = (ι B : Matrix (Fin 2) (Fin 2) K) i j := by
      rw [hAB]
    simpa [ι, e, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using h1
  have hGrange : G ≤ ι.range := by
    intro x hx
    have hAdet : (Matrix.of (fun i j =>
        (⟨(x : Matrix (Fin 2) (Fin 2) K) i j, entry_mem x hx i j⟩ : R))).det = 1 := by
      apply he_inj
      rw [map_one, RingHom.map_det]
      have hmm : e.mapMatrix (Matrix.of (fun i j =>
          (⟨(x : Matrix (Fin 2) (Fin 2) K) i j, entry_mem x hx i j⟩ : R)))
          = (x : Matrix (Fin 2) (Fin 2) K) := by
        ext i j; rfl
      rw [hmm]; exact x.2
    refine ⟨⟨Matrix.of (fun i j =>
        (⟨(x : Matrix (Fin 2) (Fin 2) K) i j, entry_mem x hx i j⟩ : R)), hAdet⟩, ?_⟩
    ext i j
    rfl
  let sec : G →* Matrix.SpecialLinearGroup (Fin 2) R :=
    (MonoidHom.ofInjective hι_inj).symm.toMonoidHom.comp (Subgroup.inclusion hGrange)
  let φ : R →+* R ⧸ m := Ideal.Quotient.mk m
  let red : G →* Matrix.SpecialLinearGroup (Fin 2) (R ⧸ m) :=
    (Matrix.SpecialLinearGroup.map φ).comp sec
  have hmap_gemb_inj :
      Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) g_emb) := by
    intro A B hAB
    ext i j
    apply hg_emb
    have h1 : (Matrix.SpecialLinearGroup.map (n := Fin 2) g_emb A) i j
            = (Matrix.SpecialLinearGroup.map (n := Fin 2) g_emb B) i j := by
      rw [hAB]
    simpa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using h1
  refine ⟨ℓ, hℓfact, hℓ2, hcop,
    (Matrix.SpecialLinearGroup.map g_emb).comp red, ?_⟩
  have hred_inj : Function.Injective red := by
    rw [injective_iff_map_eq_one]
    intro g hg
    set x := (g : Matrix.SpecialLinearGroup (Fin 2) K) with hxdef
    have hxG : x ∈ G := g.2
    -- underlying matrix, trace, determinant
    have hdetMat : (x : Matrix (Fin 2) (Fin 2) K).det = 1 := x.2
    -- order of g
    set n := orderOf g with hndef
    have hgn : g ^ n = 1 := pow_orderOf_eq_one g
    have hMatn : (x : Matrix (Fin 2) (Fin 2) K) ^ n = 1 := by
      have hxn : x ^ n = 1 := by
        have h := congrArg (fun y : G => (y : Matrix.SpecialLinearGroup (Fin 2) K)) hgn
        simpa using h
      have h := congrArg
        (fun y : Matrix.SpecialLinearGroup (Fin 2) K => (y : Matrix (Fin 2) (Fin 2) K)) hxn
      simpa using h
    have hℓn : ¬ ℓ ∣ n := by
      have hdvd : n ∣ Nat.card G := hndef ▸ orderOf_dvd_natCard g
      intro h; exact hℓN (Dvd.dvd.mul_left (h.trans hdvd) 2)
    have hnpos : 0 < n := hndef ▸ orderOf_pos g
    -- λ^n = 1
    have hμpow : (eig x) ^ n = 1 := eigen_pow _ hdetMat (eig x) (heig x) n hMatn
    -- bridge: entries of sec g equal the chosen R-lift of x's entries
    have hsec : ι (sec g) = (g : Matrix.SpecialLinearGroup (Fin 2) K) := by
      have h := MonoidHom.ofInjective_apply hι_inj
        (x := (MonoidHom.ofInjective hι_inj).symm (Subgroup.inclusion hGrange g))
      rw [MulEquiv.apply_symm_apply] at h
      simpa [sec, Subgroup.coe_inclusion] using h.symm
    have hbridge : ∀ i j, (sec g).1 i j
        = (⟨(x : Matrix (Fin 2) (Fin 2) K) i j, entry_mem x hxG i j⟩ : R) := by
      intro i j
      apply he_inj
      have h := congrArg
        (fun (M : Matrix.SpecialLinearGroup (Fin 2) K) => (M : Matrix (Fin 2) (Fin 2) K) i j) hsec
      simpa [ι, e, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using h
    have hφentry : ∀ i j,
        φ (⟨(x : Matrix (Fin 2) (Fin 2) K) i j, entry_mem x hxG i j⟩ : R)
          = (1 : Matrix (Fin 2) (Fin 2) (R ⧸ m)) i j := by
      intro i j
      rw [← hbridge]
      have h := congrArg
        (fun M : Matrix.SpecialLinearGroup (Fin 2) (R ⧸ m) =>
          (M : Matrix (Fin 2) (Fin 2) (R ⧸ m)) i j) hg
      simpa [red, φ, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] using h
    set a : R := ⟨(x : Matrix (Fin 2) (Fin 2) K) 0 0, entry_mem x hxG 0 0⟩ with hadef
    set b : R := ⟨(x : Matrix (Fin 2) (Fin 2) K) 1 1, entry_mem x hxG 1 1⟩ with hbdef
    have hφa : φ a = 1 := by have := hφentry 0 0; simpa [Matrix.one_apply_eq] using this
    have hφb : φ b = 1 := by have := hφentry 1 1; simpa [Matrix.one_apply_eq] using this
    -- the eigenvalue as an element of R and its defining relation
    set μR : R := ⟨eig x, eig_mem g⟩ with hμRdef
    have hμRrel : μR ^ 2 - (a + b) * μR + 1 = 0 := by
      apply he_inj
      rw [map_zero, map_add, map_sub, map_mul, map_add, map_pow, map_one]
      show (eig x) ^ 2
          - ((x : Matrix (Fin 2) (Fin 2) K) 0 0 + (x : Matrix (Fin 2) (Fin 2) K) 1 1) * (eig x) + 1
          = 0
      exact heig x
    have hφμR : φ μR = 1 := by
      have hrel := congrArg φ hμRrel
      rw [map_add, map_sub, map_mul, map_pow, map_add, map_one, map_zero, hφa, hφb] at hrel
      have hsq : (φ μR - 1) ^ 2 = 0 := by linear_combination hrel
      have h0 : φ μR - 1 = 0 := (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hsq
      exact sub_eq_zero.mp h0
    -- case split on whether the eigenvalue is 1
    by_cases hμ1 : eig x = 1
    · -- unipotent case: trace = 2, so (Mat - 1)² = 0 and finite order forces Mat = 1
      have htr : (x : Matrix (Fin 2) (Fin 2) K) 0 0 + (x : Matrix (Fin 2) (Fin 2) K) 1 1 = 2 := by
        have hh := heig x; rw [hμ1] at hh; linear_combination -hh
      set P : Matrix (Fin 2) (Fin 2) K := (x : Matrix (Fin 2) (Fin 2) K) - 1 with hPdef
      have hdet2 : (x : Matrix (Fin 2) (Fin 2) K) 0 0 * (x : Matrix (Fin 2) (Fin 2) K) 1 1
          - (x : Matrix (Fin 2) (Fin 2) K) 0 1 * (x : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
        rw [← Matrix.det_fin_two]; exact hdetMat
      have hP00 : P 0 0 = (x : Matrix (Fin 2) (Fin 2) K) 0 0 - 1 := by
        rw [hPdef]; simp [Matrix.sub_apply, Matrix.one_apply_eq]
      have hP11 : P 1 1 = (x : Matrix (Fin 2) (Fin 2) K) 1 1 - 1 := by
        rw [hPdef]; simp [Matrix.sub_apply, Matrix.one_apply_eq]
      have hP01 : P 0 1 = (x : Matrix (Fin 2) (Fin 2) K) 0 1 := by
        rw [hPdef]; simp [Matrix.sub_apply, Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)]
      have hP10 : P 1 0 = (x : Matrix (Fin 2) (Fin 2) K) 1 0 := by
        rw [hPdef]; simp [Matrix.sub_apply, Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)]
      have hPP : P * P = 0 := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.zero_apply, Fin.mk_zero, Fin.mk_one,
            Fin.isValue, hP00, hP01, hP10, hP11]
        · linear_combination (x : Matrix (Fin 2) (Fin 2) K) 0 0 * htr - hdet2
        · linear_combination (x : Matrix (Fin 2) (Fin 2) K) 0 1 * htr
        · linear_combination (x : Matrix (Fin 2) (Fin 2) K) 1 0 * htr
        · linear_combination (x : Matrix (Fin 2) (Fin 2) K) 1 1 * htr - hdet2
      have hbinom : ∀ k : ℕ, (1 + P) ^ k = 1 + k • P := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have hstep : (1 + k • P) * (1 + P) = 1 + k • P + P := by
            rw [mul_add, mul_one, add_mul, one_mul, smul_mul_assoc, hPP, smul_zero, add_zero]
          rw [pow_succ, ih, hstep, succ_nsmul]; abel
      have hMateq : (x : Matrix (Fin 2) (Fin 2) K) = 1 + P := by rw [hPdef]; abel
      have hnP : n • P = 0 := by
        have h1 : (1 : Matrix (Fin 2) (Fin 2) K) + n • P = 1 := by
          rw [← hbinom, ← hMateq]; exact hMatn
        have h2 : (1 : Matrix (Fin 2) (Fin 2) K) + n • P = 1 + 0 := by rw [add_zero]; exact h1
        exact add_left_cancel h2
      have hP0 : P = 0 := by
        ext i j
        have hcast : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        have hz := congrFun (congrFun hnP i) j
        simp only [Matrix.smul_apply, Matrix.zero_apply, nsmul_eq_mul] at hz
        rcases mul_eq_zero.mp hz with h | h
        · exact absurd h hcast
        · simpa using h
      have hMat1 : (x : Matrix (Fin 2) (Fin 2) K) = 1 := by rw [hMateq, hP0, add_zero]
      have hx1 : x = 1 := by
        apply Subtype.ext; rw [Matrix.SpecialLinearGroup.coe_one]; exact hMat1
      exact Subtype.ext (hxdef ▸ hx1)
    · -- otherwise: the eigenvalue is a nontrivial root of unity — contradiction
      exfalso
      set d := orderOf (eig x) with hddef
      have hfin : IsOfFinOrder (eig x) := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hnpos, hμpow⟩
      have hdpos : 0 < d := by rw [hddef]; exact hfin.orderOf_pos
      have hdne1 : d ≠ 1 := by
        intro h; apply hμ1; rw [hddef] at h; exact orderOf_eq_one_iff.mp h
      have hd1 : 1 < d := by omega
      have hdn : d ∣ n := hddef ▸ orderOf_dvd_of_pow_eq_one hμpow
      have hprimK : IsPrimitiveRoot (eig x) d := hddef ▸ IsPrimitiveRoot.orderOf (eig x)
      have hprimR : IsPrimitiveRoot μR d := by
        have hpe : IsPrimitiveRoot (e μR) d := hprimK
        exact hpe.of_map_of_injective he_inj
      exact cyclotomic_contra φ ℓ n hℓn μR d hd1 hdn hprimR hφμR
  exact hmap_gemb_inj.comp hred_inj

end CharZeroEmbedding
