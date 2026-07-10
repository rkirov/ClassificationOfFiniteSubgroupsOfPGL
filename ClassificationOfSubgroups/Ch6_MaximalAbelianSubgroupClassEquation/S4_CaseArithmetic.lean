/-
This file formalizes the *pure arithmetic* skeleton of Christopher Butler's case analysis
of the Maximal Abelian Subgroup Class Equation of a finite subgroup `G ≤ SL(2,F)`
(`ChristopherButler.tex`, lines 1206-1270 for the rearrangement of the class equation and
the derivation of the 6 possible cases, and lines 1428-1881 for the individual cases).
No group theory or `SL(2,F)` appears here: everything is stated over `ℚ`/`ℕ` so that the
later case-split formalization (which will supply the group-theoretic hypotheses relating
`g`, `q`, `k` and the `g_i` to the actual subgroup `G`) can consume these lemmas directly.

Notation (matching Butler): `e = |Z|`, `|G| = eg`, `|Q| = q` (a Sylow `p`-subgroup),
`|K| = ek` where `K = C_G(x) ∩ G` for `x` a noncentral element of `Q`, and for the cyclic
maximal abelian subgroups `A_i` (of order relatively prime to `p`) we set `|A_i| = e g_i`.
The `g_i` for `i ≤ s` are the classes with `[N_G(A_i) : A_i] = 1` and the `g_i` for
`s < i ≤ s + t` are the classes with `[N_G(A_i) : A_i] = 2`.
-/
import Mathlib

set_option autoImplicit false

open Finset

namespace CaseArithmetic

/-! ### Small algebraic identities used repeatedly below -/

lemma one_sub_inv_self {n : ℚ} (hn : n ≠ 0) : (n - 1) / n = 1 - 1 / n := by
  field_simp

lemma one_sub_inv_two_self {n : ℚ} (hn : n ≠ 0) : (n - 1) / (2 * n) = 1 / 2 - 1 / (2 * n) := by
  field_simp

/-- Each term `(gᵢ - 1)/gᵢ` of an "index 1" summand is at least `1/2`, since `gᵢ ≥ 2`. -/
lemma half_le_term {n : ℕ} (hn : 2 ≤ n) : (1 : ℚ) / 2 ≤ ((n : ℚ) - 1) / n := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  rw [div_le_div_iff₀ (by norm_num) hnpos]
  have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  nlinarith

/-- Each term `(gᵢ - 1)/(2gᵢ)` of an "index 2" summand is at least `1/4`, since `gᵢ ≥ 2`. -/
lemma quarter_le_term {n : ℕ} (hn : 2 ≤ n) : (1 : ℚ) / 4 ≤ ((n : ℚ) - 1) / (2 * n) := by
  have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast (by omega : 0 < n)
  rw [div_le_div_iff₀ (by norm_num) (by positivity)]
  have : (2 : ℚ) ≤ (n : ℚ) := by exact_mod_cast hn
  nlinarith

/-! ### Lower bounds on the two sums appearing in the class equation -/

/-- `∑ i, (gᵢ - 1)/gᵢ ≥ s/2` (tex ~1206-1210: `gᵢ - 1)/gᵢ ≥ 1/2` for each of the `s` terms). -/
lemma sum_half_le {s : ℕ} (gs : Fin s → ℕ) (hgs : ∀ i, 2 ≤ gs i) :
    (s : ℚ) / 2 ≤ ∑ i : Fin s, (((gs i : ℚ) - 1) / (gs i)) := by
  have : (s : ℚ) / 2 = ∑ _i : Fin s, (1 / 2 : ℚ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [this]
  exact Finset.sum_le_sum (fun i _ => half_le_term (hgs i))

/-- `∑ j, (gⱼ - 1)/(2gⱼ) ≥ t/4` (tex ~1206-1210: each of the `t` terms is `≥ 1/4`). -/
lemma sum_quarter_le {t : ℕ} (gt : Fin t → ℕ) (hgt : ∀ i, 2 ≤ gt i) :
    (t : ℚ) / 4 ≤ ∑ i : Fin t, (((gt i : ℚ) - 1) / (2 * gt i)) := by
  have : (t : ℚ) / 4 = ∑ _i : Fin t, (1 / 4 : ℚ) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  rw [this]
  exact Finset.sum_le_sum (fun i _ => quarter_le_term (hgt i))

/-! ### The master equation shape and the case enumeration -/

/-- **The Maximal Abelian Subgroup Class Equation**, rearranged (tex `\eqref{classeq}`,
lines ~1206-1210):
`1 = 1/g + (q-1)/(qk) + ∑_{i ≤ s} (gᵢ-1)/gᵢ + ∑_{j ≤ t} (gⱼ-1)/(2gⱼ)`.
Here `g = |G|/|Z|`, `q = |Q|` for `Q` a Sylow `p`-subgroup, `k = |K|/|Z|` for
`K = C_G(x) ∩ G` (`x` noncentral in `Q`), and the `gs i`/`gt j` are the
`|A_i|/|Z|` for the cyclic maximal abelian subgroups with normalizer index `1`/`2`
respectively. -/
def ClassEquation (g q k : ℕ) {s t : ℕ} (gs : Fin s → ℕ) (gt : Fin t → ℕ) : Prop :=
  (1 : ℚ) = 1 / g + ((q : ℚ) - 1) / (q * k)
    + (∑ i : Fin s, (((gs i : ℚ) - 1) / (gs i)))
    + (∑ i : Fin t, (((gt i : ℚ) - 1) / (2 * gt i)))

/-- **Main lemma (`case_enumeration`)**: the class equation forces `2s + t < 4`, i.e. `(s,t)`
is one of the 6 pairs Butler tabulates (tex lines ~1206-1270, "Case I" ... "Case VI"). -/
theorem case_enumeration (g q k : ℕ) (hg : 1 ≤ g) (hq : 1 ≤ q) (hk : 1 ≤ k)
    {s t : ℕ} (gs : Fin s → ℕ) (gt : Fin t → ℕ)
    (hgs : ∀ i, 2 ≤ gs i) (hgt : ∀ i, 2 ≤ gt i)
    (heq : ClassEquation g q k gs gt) :
    (s = 1 ∧ t = 0) ∨ (s = 1 ∧ t = 1) ∨ (s = 0 ∧ t = 0) ∨ (s = 0 ∧ t = 1)
      ∨ (s = 0 ∧ t = 2) ∨ (s = 0 ∧ t = 3) := by
  have hgpos : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hkpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hqk_nonneg : (0 : ℚ) ≤ ((q : ℚ) - 1) / (q * k) := by
    apply div_nonneg
    · have : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
      linarith
    · positivity
  have hs := sum_half_le gs hgs
  have ht := sum_quarter_le gt hgt
  have h1g : (0 : ℚ) < 1 / g := by positivity
  have hbound : (s : ℚ) / 2 + (t : ℚ) / 4 < 1 := by
    unfold ClassEquation at heq
    linarith
  have hnat : 2 * s + t < 4 := by
    have h4 : (2 * (s : ℚ) + (t : ℚ)) < 4 := by linarith
    have : ((2 * s + t : ℕ) : ℚ) < ((4 : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast this
  omega

/-! ### Per-case numeric consequences (Butler's "Case I" - "Case VI", tex ~1428-1881) -/

/-- **Case I** (`s = 1, t = 0`, tex ~1428-1450): rearranging the class equation gives
`1/(qk) + 1/g₁ = 1/g + 1/k`, and Butler splits into `q = 1` ("Case Ia") and `q > 1`
("Case Ib"). In the `q > 1` branch he needs `k > 1`, which he gets from the case
`k = 1` giving `1/q + 1/g₁ = 1/g + 1 > 1` while also `1/q, 1/g₁ ≤ 1/2` — a contradiction;
this part is pure arithmetic and is reproved below. From `k > 1`, i.e. `|K| > |Z|`, Butler
invokes Theorem 6.8(v): since `K` is a genuine (nontrivial) subgroup and the only cyclic
maximal abelian conjugacy class here is `A₁`, `K` must equal (a conjugate of) `A₁`, so
`k = g₁`; this group-theoretic fact is recorded as the hypothesis `hK`. -/
theorem case_1_0 (g q k g1 : ℕ) (hg : 1 ≤ g) (hq : 1 ≤ q) (hk : 1 ≤ k) (hg1 : 2 ≤ g1)
    (hK : 1 < k → k = g1)
    (heq : ClassEquation g q k (s := 1) (t := 0) (fun _ => g1) (fun i => i.elim0)) :
    (q = 1 ∧ g = g1) ∨ (1 < q ∧ k = g1 ∧ g = q * k) := by
  unfold ClassEquation at heq
  simp only [Fin.sum_univ_one, Finset.univ_eq_empty, Finset.sum_empty, add_zero] at heq
  have hgpos : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hkpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hg1pos : (0 : ℚ) < (g1 : ℚ) := by exact_mod_cast (by omega : 0 < g1)
  rcases eq_or_lt_of_le hq with hq1 | hq1
  · -- Case Ia: `q = 1`.
    left
    have hqn : q = 1 := hq1.symm
    have hq1' : (q : ℚ) = 1 := by exact_mod_cast hqn
    refine ⟨hqn, ?_⟩
    rw [hq1'] at heq
    simp only [sub_self, one_mul, zero_div, add_zero] at heq
    have hgg1 : (g : ℚ) = (g1 : ℚ) := by
      have h1 : ((g1:ℚ) - 1)/g1 = 1 - 1/g1 := one_sub_inv_self (ne_of_gt hg1pos)
      rw [h1] at heq
      have h2 : (1:ℚ)/g1 = 1/g := by linarith
      field_simp at h2
      linarith
    exact_mod_cast hgg1
  · -- Case Ib: `q > 1`.
    right
    have hq1' : 1 < q := hq1
    have hkne1 : k ≠ 1 := by
      intro hk1
      subst hk1
      simp only [Nat.cast_one, mul_one] at heq
      have hq2 : (2 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq1'
      have hg12 : (2 : ℚ) ≤ (g1 : ℚ) := by exact_mod_cast hg1
      have h1 : (1:ℚ) / q ≤ 1/2 := by
        rw [div_le_div_iff₀ hqpos (by norm_num)]
        linarith
      have h2 : (1:ℚ) / g1 ≤ 1/2 := by
        rw [div_le_div_iff₀ hg1pos (by norm_num)]
        linarith
      have hq' : ((q:ℚ) - 1)/q = 1 - 1/q := one_sub_inv_self (ne_of_gt hqpos)
      have hg1' : ((g1:ℚ) - 1)/g1 = 1 - 1/g1 := one_sub_inv_self (ne_of_gt hg1pos)
      have h3 : (0:ℚ) < 1/g := by positivity
      rw [hq', hg1'] at heq
      linarith
    have hk1lt : 1 < k := by omega
    have hkg1 : k = g1 := hK hk1lt
    subst hkg1
    refine ⟨hq1', rfl, ?_⟩
    have hkpos' : (0:ℚ) < (k:ℚ) := hkpos
    have e1 : ((k:ℚ) - 1)/k = 1 - 1/k := one_sub_inv_self (ne_of_gt hkpos')
    rw [e1] at heq
    have e2 : ((q:ℚ) - 1)/(q*k) = 1/k - 1/(q*k) := by
      field_simp
    rw [e2] at heq
    have key : (1:ℚ)/(q*k) = 1/g := by linarith
    have hqk : (g:ℚ) = q * k := by
      field_simp at key
      linarith
    exact_mod_cast hqk

/-- **Case III** (`s = 0, t = 0`, tex ~1661-1670): with no cyclic maximal abelian classes at
all, `K` cannot be a genuine (nontrivial) maximal abelian subgroup, so Theorem 6.8(v) forces
`|K| ≤ |Z|`, i.e. `k ≤ 1`; this group-theoretic fact is recorded as the hypothesis `hKle`
(without it the conclusion is false: e.g. `q = 1, k = 5, g = 1` solves the equation for any
`k`, since the `(q-1)` factor vanishes). Given `k = 1` the class equation reduces to
`1/q = 1/g`, i.e. `g = q`. -/
theorem case_0_0 (g q k : ℕ) (hg : 1 ≤ g) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hKle : k ≤ 1)
    (heq : ClassEquation g q k (s := 0) (t := 0) (fun i => i.elim0) (fun i => i.elim0)) :
    k = 1 ∧ g = q := by
  have hk1 : k = 1 := le_antisymm hKle hk
  refine ⟨hk1, ?_⟩
  unfold ClassEquation at heq
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero] at heq
  subst hk1
  simp only [Nat.cast_one, mul_one] at heq
  have hgpos : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hq' : ((q:ℚ) - 1)/q = 1 - 1/q := one_sub_inv_self (ne_of_gt hqpos)
  rw [hq'] at heq
  have hgq : (1:ℚ)/g = 1/q := by linarith
  have : (g:ℚ) = (q:ℚ) := by
    field_simp at hgq
    linarith
  exact_mod_cast this

/-- **Case IV** (`s = 0, t = 1`, tex ~1681-1745, "Case IVa/IVb"): since `[N_G(A_1) : A_1] = 2`
and `A_1 ≤ N_G(A_1) ≤ G`, we have `|G| ≥ 2|A_1|`, i.e. `g ≥ 2g₁`; this group-theoretic fact
(Lagrange applied to `N_G(A_1) ≤ G`) is recorded as the hypothesis `hg_ge`. From it, Butler
derives `k = 1`, `q ∈ {2,3}` and pins down `g` exactly in each subcase. -/
theorem case_0_1 (g q k g1 : ℕ) (hg : 1 ≤ g) (hq : 1 ≤ q) (hk : 1 ≤ k) (hg1 : 2 ≤ g1)
    (hg_ge : 2 * g1 ≤ g)
    (heq : ClassEquation g q k (s := 0) (t := 1) (fun i => i.elim0) (fun _ => g1)) :
    k = 1 ∧ ((q = 2 ∧ g = 2 * g1) ∨ (q = 3 ∧ g1 = 2 ∧ g = 12)) := by
  unfold ClassEquation at heq
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_one] at heq
  have hgpos : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hkpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hg1pos : (0 : ℚ) < (g1 : ℚ) := by exact_mod_cast (by omega : 0 < g1)
  have hg1' : ((g1:ℚ) - 1)/(2*g1) = 1/2 - 1/(2*g1) := one_sub_inv_two_self (ne_of_gt hg1pos)
  rw [hg1'] at heq
  have heq2 : (1:ℚ)/2 + 1/(2*g1) = 1/g + ((q:ℚ)-1)/(q*k) := by linarith
  have hg1_le : (1:ℚ)/g ≤ 1/(2*g1) := by
    rw [div_le_div_iff₀ hgpos (by positivity)]
    have : (2 * (g1:ℚ)) ≤ (g:ℚ) := by exact_mod_cast hg_ge
    linarith
  have hqk_ge : (1:ℚ)/2 ≤ ((q:ℚ)-1)/(q*k) := by linarith
  -- Step: `k = 1`.
  have hq1 : (1:ℚ) ≤ (q:ℚ) := by exact_mod_cast hq
  have hk1 : k = 1 := by
    by_contra hkne
    have hk2 : 2 ≤ k := by omega
    have hcontra : ((q:ℚ)-1)/(q*k) ≤ ((q:ℚ)-1)/(2*q) := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity)
      have : (2:ℚ) ≤ (k:ℚ) := by exact_mod_cast hk2
      nlinarith
    have hqhalf : ((q:ℚ)-1)/(2*q) < 1/2 := by
      rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  subst hk1
  refine ⟨rfl, ?_⟩
  simp only [Nat.cast_one, mul_one] at heq2 hqk_ge
  have hq' : ((q:ℚ) - 1)/q = 1 - 1/q := one_sub_inv_self (ne_of_gt hqpos)
  rw [hq'] at heq2
  have heq3 : (1:ℚ)/q + 1/(2*g1) = 1/g + 1/2 := by linarith
  -- `q ≥ 2` from `hqk_ge`.
  have hq2 : 2 ≤ q := by
    by_contra hqne
    have hq1 : q = 1 := by omega
    rw [hq1] at hqk_ge
    norm_num at hqk_ge
  -- `q < 4` from `heq3` and `g1 ≥ 2`.
  have hg1_quarter : (1:ℚ)/(2*g1) ≤ 1/4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2:ℚ) ≤ (g1:ℚ) := by exact_mod_cast hg1
    linarith
  have h1g : (0:ℚ) < 1/g := by positivity
  have hq4 : q < 4 := by
    have hqQ : (1:ℚ)/q > 1/4 := by linarith [heq3, hg1_quarter, h1g]
    by_contra hcon
    push_neg at hcon
    have hqge4 : (q:ℚ) ≥ 4 := by exact_mod_cast hcon
    have : (1:ℚ)/q ≤ 1/4 := by
      rw [div_le_div_iff₀ hqpos (by norm_num)]
      linarith
    linarith
  interval_cases q
  · -- `q = 2`.
    left
    refine ⟨rfl, ?_⟩
    norm_num at heq3
    have : (1:ℚ)/(2*g1) = 1/g := by linarith
    have hg2g1 : (g:ℚ) = 2*g1 := by
      field_simp at this
      linarith
    exact_mod_cast hg2g1
  · -- `q = 3`.
    right
    norm_num at heq3
    have hkey : (1:ℚ)/(2*g1) = 1/g + 1/6 := by linarith
    have hg1lt3 : (1:ℚ)/(2*g1) > 1/6 := by
      have : (0:ℚ) < 1/g := by positivity
      linarith
    have hg1lt : g1 < 3 := by
      by_contra hcon
      push_neg at hcon
      have h3g1 : (3:ℚ) ≤ (g1:ℚ) := by exact_mod_cast hcon
      have : (1:ℚ)/(2*g1) ≤ 1/6 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith
    have hg1eq : g1 = 2 := by omega
    refine ⟨rfl, hg1eq, ?_⟩
    rw [hg1eq] at hkey
    norm_num at hkey
    have hg12 : (g:ℚ) = 12 := by
      field_simp at hkey
      linarith
    exact_mod_cast hg12

/-- **Case II** (`s = 1, t = 1`, tex ~1453-1481, "Case II"/"Case IIa/IIb"): Butler first rules
out `q > 1` using the group-theoretic fact that if `K` is a genuine (nontrivial) maximal
abelian subgroup strictly bigger than the (unique) index-2 class `A_2`, then (Theorem 6.8(v),
there being only the two cyclic classes `A_1, A_2` here) `K` must be `A_1`, i.e. `k = g₁`; this
is recorded as the hypothesis `hK`. Having forced `q = 1`, the equation reduces to
`1/g₁ + 1/(2g₂) = 1/2 + 1/g`, from which `g₁ < 4`, i.e. `g₁ ∈ {2,3}` (the further pinning down
of `g₂` in each subcase needs more group theory and is not attempted here). -/
theorem case_1_1 (g q k g1 g2 : ℕ) (hg : 1 ≤ g) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hg1 : 2 ≤ g1) (hg2 : 2 ≤ g2)
    (hK : g2 < k → k = g1)
    (heq : ClassEquation g q k (s := 1) (t := 1) (fun _ => g1) (fun _ => g2)) :
    q = 1 ∧ (g1 = 2 ∨ g1 = 3) := by
  unfold ClassEquation at heq
  simp only [Fin.sum_univ_one] at heq
  have hgpos : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hkpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hg1pos : (0 : ℚ) < (g1 : ℚ) := by exact_mod_cast (by omega : 0 < g1)
  have hg2pos : (0 : ℚ) < (g2 : ℚ) := by exact_mod_cast (by omega : 0 < g2)
  have h1g : (0:ℚ) < 1/g := by positivity
  have e1 : ((g1:ℚ) - 1)/g1 = 1 - 1/g1 := one_sub_inv_self (ne_of_gt hg1pos)
  have e2 : ((g2:ℚ) - 1)/(2*g2) = 1/2 - 1/(2*g2) := one_sub_inv_two_self (ne_of_gt hg2pos)
  rw [e1, e2] at heq
  have heqA : (1:ℚ)/g1 + 1/(2*g2) = 1/2 + 1/g + ((q:ℚ)-1)/(q*k) := by linarith
  have hq1 : q = 1 := by
    by_contra hqne
    have hq2 : 2 ≤ q := by omega
    have hhalfq : (1:ℚ)/2 ≤ ((q:ℚ)-1)/q := half_le_term hq2
    have hqk_half : (1:ℚ)/(2*k) ≤ ((q:ℚ)-1)/(q*k) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hq2' : (2:ℚ) ≤ (q:ℚ) := by exact_mod_cast hq2
      nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ (q:ℚ) - 2) hkpos.le]
    have hg12_nonneg : (0:ℚ) ≤ 1/2 - 1/g1 := by
      rw [sub_nonneg, div_le_div_iff₀ hg1pos (by norm_num)]
      have : (2:ℚ) ≤ (g1:ℚ) := by exact_mod_cast hg1
      linarith
    have hkg2 : g2 < k := by
      have hstep : (1:ℚ)/(2*k) < 1/(2*g2) := by linarith
      have h4 : (0:ℚ) < 2*k := by positivity
      have h5 : (0:ℚ) < 2*g2 := by positivity
      rw [div_lt_div_iff₀ h4 h5, one_mul, one_mul] at hstep
      exact_mod_cast (by linarith : (g2:ℚ) < k)
    have hkeq : k = g1 := hK hkg2
    rw [hkeq] at heqA
    have hqk_half' : (1:ℚ)/(2*g1) ≤ ((q:ℚ)-1)/(q*g1) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hq2' : (2:ℚ) ≤ (q:ℚ) := by exact_mod_cast hq2
      nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ (q:ℚ) - 2) hg1pos.le]
    have hrel : (1:ℚ)/(2*g1) = 1/2 * (1/g1) := by field_simp
    have hcontra : (1:ℚ)/(2*g1) + 1/(2*g2) > 1/2 := by linarith [hrel]
    have hb1 : (1:ℚ)/(2*g1) ≤ 1/4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2:ℚ) ≤ (g1:ℚ) := by exact_mod_cast hg1
      linarith
    have hb2 : (1:ℚ)/(2*g2) ≤ 1/4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : (2:ℚ) ≤ (g2:ℚ) := by exact_mod_cast hg2
      linarith
    linarith
  refine ⟨hq1, ?_⟩
  subst hq1
  simp only [Nat.cast_one, sub_self, zero_div] at heqA
  have heqB : (1:ℚ)/g1 + 1/(2*g2) = 1/2 + 1/g := by linarith
  have hg1lt4 : g1 < 4 := by
    by_contra hcon
    push_neg at hcon
    have hg14 : (4:ℚ) ≤ (g1:ℚ) := by exact_mod_cast hcon
    have hg1_le : (1:ℚ)/g1 ≤ 1/4 := by
      rw [div_le_div_iff₀ hg1pos (by norm_num)]
      linarith
    have h2g2gt : (1:ℚ)/(2*g2) > 1/4 := by linarith
    have hg2lt2 : (g2:ℚ) < 2 := by
      by_contra hcon2
      push_neg at hcon2
      have : (1:ℚ)/(2*g2) ≤ 1/4 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        linarith
      linarith
    have : (2:ℚ) ≤ (g2:ℚ) := by exact_mod_cast hg2
    linarith
  omega

/-- **Case V** (`s = 0, t = 2`, tex ~1848-1911, "Case V"), *partial*: the opening arithmetic
steps of Butler's analysis, giving `q > 1` and `k > 1`. Beyond this point (tex ~1866 onward)
Butler needs the group-theoretic fact that `K ∈ 𝔐 ⟹ k ∈ {g₁, g₂}` (Theorem 6.8(v)) together
with a genuinely Diophantine argument involving auxiliary integers `d`, `i`, `m` coming from an
orbit-counting/Sylow argument (tex `\eqref{6.14}`-`\eqref{6.19}`) that is well outside the scope
of the pure class-equation arithmetic formalized in this file; it is not attempted here. -/
theorem case_0_2 (g q k g1 g2 : ℕ) (hg : 1 ≤ g) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hg1 : 2 ≤ g1) (hg2 : 2 ≤ g2)
    (hg_ge1 : 2 * g1 ≤ g) (hg_ge2 : 2 * g2 ≤ g)
    (heq : ClassEquation g q k (s := 0) (t := 2) (fun i => i.elim0) ![g1, g2]) :
    1 < q ∧ 1 < k := by
  unfold ClassEquation at heq
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one] at heq
  have hgpos : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hkpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hg1pos : (0 : ℚ) < (g1 : ℚ) := by exact_mod_cast (by omega : 0 < g1)
  have hg2pos : (0 : ℚ) < (g2 : ℚ) := by exact_mod_cast (by omega : 0 < g2)
  have h1g : (0:ℚ) < 1/g := by positivity
  have e1 : ((g1:ℚ) - 1)/(2*g1) = 1/2 - 1/(2*g1) := one_sub_inv_two_self (ne_of_gt hg1pos)
  have e2 : ((g2:ℚ) - 1)/(2*g2) = 1/2 - 1/(2*g2) := one_sub_inv_two_self (ne_of_gt hg2pos)
  rw [e1, e2] at heq
  have heqA : (1:ℚ)/(2*g1) + 1/(2*g2) = 1/g + ((q:ℚ)-1)/(q*k) := by linarith
  have hgg1 : (1:ℚ)/g ≤ 1/(2*g1) := by
    rw [div_le_div_iff₀ hgpos (by positivity)]
    have : (2 * (g1:ℚ)) ≤ (g:ℚ) := by exact_mod_cast hg_ge1
    linarith
  have hgg2 : (1:ℚ)/g ≤ 1/(2*g2) := by
    rw [div_le_div_iff₀ hgpos (by positivity)]
    have : (2 * (g2:ℚ)) ≤ (g:ℚ) := by exact_mod_cast hg_ge2
    linarith
  have hq1 : 1 < q := by
    by_contra hqne
    have hqeq : q = 1 := by omega
    rw [hqeq] at heqA
    simp only [Nat.cast_one, sub_self, zero_div, add_zero] at heqA
    linarith
  have hb1 : (1:ℚ)/(2*g1) ≤ 1/4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2:ℚ) ≤ (g1:ℚ) := by exact_mod_cast hg1
    linarith
  have hb2 : (1:ℚ)/(2*g2) ≤ 1/4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2:ℚ) ≤ (g2:ℚ) := by exact_mod_cast hg2
    linarith
  have hq2 : 2 ≤ q := hq1
  have hhalfq : (1:ℚ)/2 ≤ ((q:ℚ)-1)/q := half_le_term hq2
  have hqk_half : (1:ℚ)/(2*k) ≤ ((q:ℚ)-1)/(q*k) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have hq2' : (2:ℚ) ≤ (q:ℚ) := by exact_mod_cast hq2
    nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ (q:ℚ) - 2) hkpos.le]
  refine ⟨hq1, ?_⟩
  have hlt : (1:ℚ)/(2*k) < 1/2 := by linarith
  by_contra hkne
  have hkeq : k = 1 := by omega
  rw [hkeq] at hlt
  norm_num at hlt

/-- **Case VI** (`s = 0, t = 3`, tex ~2115-2160, "Case VI"), *partial*: the opening arithmetic
steps of Butler's analysis, giving `q = 1` (Butler's Equation `\eqref{case6b}`). Note that
once `q = 1` the `(q-1)/(qk)` term of the class equation vanishes identically, *regardless*
of `k`; so unlike Cases III/IV, `k` is genuinely left unconstrained by the arithmetic here
(Butler does not in fact claim a value for `k` in this case either). Beyond `q = 1`, Butler
further pins down `g₁ = 2` and `g₂ ∈ {2,3}` and then eliminates `g₂ = g₃ = 3` using a
Sylow-conjugacy argument (tex ~2160-2165) that is genuinely group-theoretic (not pure
arithmetic) and is not attempted here. The hypothesis `hK` records Theorem 6.8(v) applied to
this case: a nontrivial `K` must equal (a conjugate of) one of `A₁, A₂, A₃`. -/
theorem case_0_3 (g q k g1 g2 g3 : ℕ) (hg : 1 ≤ g) (hq : 1 ≤ q) (hk : 1 ≤ k)
    (hg1 : 2 ≤ g1) (hg2 : 2 ≤ g2) (hg3 : 2 ≤ g3)
    (hK : 1 < k → k = g1 ∨ k = g2 ∨ k = g3)
    (heq : ClassEquation g q k (s := 0) (t := 3) (fun i => i.elim0) ![g1, g2, g3]) :
    q = 1 := by
  unfold ClassEquation at heq
  simp only [Finset.univ_eq_empty, Finset.sum_empty, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at heq
  have hgpos : (0 : ℚ) < (g : ℚ) := by exact_mod_cast hg
  have hqpos : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
  have hkpos : (0 : ℚ) < (k : ℚ) := by exact_mod_cast hk
  have hg1pos : (0 : ℚ) < (g1 : ℚ) := by exact_mod_cast (by omega : 0 < g1)
  have hg2pos : (0 : ℚ) < (g2 : ℚ) := by exact_mod_cast (by omega : 0 < g2)
  have hg3pos : (0 : ℚ) < (g3 : ℚ) := by exact_mod_cast (by omega : 0 < g3)
  have h1g : (0:ℚ) < 1/g := by positivity
  have e1 : ((g1:ℚ) - 1)/(2*g1) = 1/2 - 1/(2*g1) := one_sub_inv_two_self (ne_of_gt hg1pos)
  have e2 : ((g2:ℚ) - 1)/(2*g2) = 1/2 - 1/(2*g2) := one_sub_inv_two_self (ne_of_gt hg2pos)
  have e3 : ((g3:ℚ) - 1)/(2*g3) = 1/2 - 1/(2*g3) := one_sub_inv_two_self (ne_of_gt hg3pos)
  rw [e1, e2, e3] at heq
  have heqA : (1:ℚ)/(2*g1) + 1/(2*g2) + 1/(2*g3) = 1/g + ((q:ℚ)-1)/(q*k) + 1/2 := by linarith
  have hb1 : (1:ℚ)/(2*g1) ≤ 1/4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2:ℚ) ≤ (g1:ℚ) := by exact_mod_cast hg1
    linarith
  have hb2 : (1:ℚ)/(2*g2) ≤ 1/4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2:ℚ) ≤ (g2:ℚ) := by exact_mod_cast hg2
    linarith
  have hb3 : (1:ℚ)/(2*g3) ≤ 1/4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (2:ℚ) ≤ (g3:ℚ) := by exact_mod_cast hg3
    linarith
  -- `q = 1`: otherwise `q > 1`, and both `k = 1` and `k > 1` lead to a contradiction.
  by_contra hqne
  have hq2 : 2 ≤ q := by omega
  have hhalfq : (1:ℚ)/2 ≤ ((q:ℚ)-1)/q := half_le_term hq2
  rcases eq_or_lt_of_le hk with hk1 | hk1
  · -- `k = 1`.
    have hkeq : k = 1 := hk1.symm
    rw [hkeq] at heqA
    simp only [Nat.cast_one, mul_one] at heqA
    have hq' : ((q:ℚ) - 1)/q = 1 - 1/q := one_sub_inv_self (ne_of_gt hqpos)
    rw [hq'] at heqA
    have hqhalf : (1:ℚ)/q ≤ 1/2 := by
      rw [div_le_div_iff₀ hqpos (by norm_num)]
      have hq2' : (2:ℚ) ≤ (q:ℚ) := by exact_mod_cast hq2
      linarith
    linarith
  · -- `k > 1`.
    have hkeq : k = g1 ∨ k = g2 ∨ k = g3 := hK hk1
    have hqk_half : (1:ℚ)/(2*k) ≤ ((q:ℚ)-1)/(q*k) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hq2' : (2:ℚ) ≤ (q:ℚ) := by exact_mod_cast hq2
      nlinarith [mul_nonneg (by linarith : (0:ℚ) ≤ (q:ℚ) - 2) hkpos.le]
    rcases hkeq with hkeq | hkeq | hkeq
    · rw [hkeq] at heqA hqk_half; linarith
    · rw [hkeq] at heqA hqk_half; linarith
    · rw [hkeq] at heqA hqk_half; linarith

end CaseArithmetic
