/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import TateCurvesTheta.Analysis.StrassmannSphere
import TateCurvesTheta.Arithmetic.DivisorConvolution
import TateCurvesTheta.TateCurve.DefectAnnulusLaurent
import TateCurvesTheta.TateCurve.DefectVanishing
import TateCurvesTheta.TateCurve.EisensteinSeries
import TateCurvesTheta.TateCurve.TatePointMem
import TateCurvesTheta.Theta.LaurentSphere

/-!
# The Tate point lies on the Tate curve: closing the Weierstrass identity

This file closes the Tate-parametrization Weierstrass identity unconditionally (away from
characteristics `2` and `3`): for a Tate parameter `q` over a complete nonarchimedean field
`K` with `(12 : K) ≠ 0` and every `u : Kˣ` off the `q`-orbit,
```
Y(u)² + X(u)·Y(u) = X(u)³ + a₄·X(u) + a₆,
```
i.e. the Tate point `(X(u), Y(u))` lies on `E_q` (Silverman, *Advanced Topics*, Ch. V,
Thm 3.1). This discharges the residual seam `DefectLaurentRepr` of
`TateCurve/TatePointMem.lean` (#116/#146/#170) and unblocks the Tate-parametrization
subtree.

## The assembly

`TateCurve/DefectVanishing.lean` reduced the vanishing of the Weierstrass defect at every
off-orbit point to two `u`-free **bracket identities** among the constant Eisenstein series.
Here these brackets are proved by combining:

* the `q`-expansions of `TateCurve/EisensteinSeries.lean`, which place every series on the
  common grid `∑'_N c_N·q^{N+1}` with per-`N` divisor-sum coefficients;
* the two classical convolution identities of `Arithmetic/DivisorConvolution.lean` — the
  **Besge identity** for `σ₁∗σ₁` and the weight-6 **`σ₁∗σ₃` evaluation** — applied
  coefficientwise. In series form these read
  `12·s₁² + 6·ρ = 5·s₃ + s₁` (`eisenstein_besge`) and
  `30·𝔪 + 240·s₁s₃ + s₁ = 10·s₃ + 21·s₅` (`eisenstein_sigma_one_three`), where
  `ρ = ∑ Nσ₁(N)qᴺ` and `𝔪 = ∑ Nσ₃(N)qᴺ` are the weighted Eisenstein series.

With the brackets in hand, `tateDefect_eq_zero` vanishes the defect **pointwise at every
off-orbit `u`** — uniformly, with no annulus restriction and no boundary-sphere case split —
so `DefectLaurentRepr` holds with the zero coefficient family (`defectLaurentRepr`), and the
Weierstrass identity `tatePoint_mem'` follows. As a corollary, Strassmann's theorem turns
the vanishing on a (nonempty) fundamental annulus into the coefficient-level Eisenstein
identity `defectAnnulusCoeff_eq_zero` (#169).

## The characteristic hypothesis

The hypothesis `(12 : K) ≠ 0` (characteristic not `2` or `3`) is genuine for this proof
route: the coefficient `a₆ = -(5s₃ + 7s₅)/12` involves division by `12`, and the
Eisenstein computation divides by `2` throughout.

## Main results

* `TateParameter.eisenstein_besge`, `TateParameter.eisenstein_sigma_one_three`: the two
  convolution identities in convergent-series form.
* `TateParameter.bracketA_eq_zero`, `TateParameter.bracketB_eq`: the two bracket
  identities consumed by the defect computation.
* `TateParameter.tateDefect_eq_zero`: the Weierstrass defect vanishes off the orbit.
* `TateParameter.defectLaurentRepr`: the residual seam `DefectLaurentRepr` holds.
* `TateParameter.tatePoint_mem'`: the unconditional Weierstrass identity.
* `TateParameter.defectAnnulusCoeff_eq_zero`: the coefficient-level identity, on a
  nonempty fundamental annulus.

## References

* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, Ch. V, Thm 3.1.
* J. Tate, *A review of non-Archimedean elliptic functions*.
* M. Besge, *Extrait d'une lettre de M. Besge à M. Liouville*, J. Math. Pures Appl. 7 (1862).
-/

open Filter Topology

noncomputable section

namespace TateCurvesTheta

namespace TateParameter

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-! ### Norm bounds for divisor-sum coefficients -/

section CoeffBounds

omit [CompleteSpace K] in
private lemma norm_add_le_one' {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a + b‖ ≤ 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)

omit [CompleteSpace K] [IsUltrametricDist K] in
private lemma norm_mul_le_one' {a b : K} (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) : ‖a * b‖ ≤ 1 := by
  rw [norm_mul]
  exact mul_le_one₀ ha (norm_nonneg _) hb

omit [CompleteSpace K] in
private lemma norm_finset_sum_le_one {α : Type*} {s : Finset α} {f : α → K}
    (hf : ∀ a ∈ s, ‖f a‖ ≤ 1) : ‖∑ a ∈ s, f a‖ ≤ 1 := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    rw [Finset.sum_cons]
    exact norm_add_le_one' (hf a (Finset.mem_cons_self a s))
      (ih fun b hb => hf b (Finset.mem_cons_of_mem hb))

omit [CompleteSpace K] in
private lemma norm_divisor_pow_sum_le_one (k M : ℕ) :
    ‖∑ d ∈ M.divisors, (d : K) ^ k‖ ≤ 1 := by
  refine norm_finset_sum_le_one fun d _ => ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one K d)

omit [CompleteSpace K] in
private lemma norm_divisor_sum_le_one (M : ℕ) : ‖∑ d ∈ M.divisors, (d : K)‖ ≤ 1 :=
  norm_finset_sum_le_one fun d _ => IsUltrametricDist.norm_natCast_le_one K d

omit [IsUltrametricDist K] in
/-- Summability of a coefficient family dominated by `1` against the geometric grid. -/
private lemma summable_qexp {c : ℕ → K} (hc : ∀ N, ‖c N‖ ≤ 1) :
    Summable fun N : ℕ => c N * (t.q : K) ^ (N + 1) := by
  have hgeom : Summable fun N : ℕ => ‖(t.q : K)‖ ^ (N + 1) := by
    simpa only [pow_succ] using
      (summable_geometric_of_lt_one (norm_nonneg _) t.norm_lt_one).mul_right ‖(t.q : K)‖
  refine hgeom.of_norm_bounded fun N => ?_
  rw [norm_mul, norm_pow]
  calc ‖c N‖ * ‖(t.q : K)‖ ^ (N + 1) ≤ 1 * ‖(t.q : K)‖ ^ (N + 1) := by gcongr; exact hc N
    _ = ‖(t.q : K)‖ ^ (N + 1) := one_mul _

end CoeffBounds

/-! ### The two convolution identities in series form -/

section SeriesIdentities

/-- **Besge's identity in convergent-series form**: `12·s₁² + 6·ρ = 5·s₃ + s₁`, where
`ρ = t.rSum = ∑_N Nσ₁(N)qᴺ` is the weight-2 weighted Eisenstein series. Each `qᴺ`-slot is
the classical Besge evaluation of the `σ₁∗σ₁` convolution. -/
theorem eisenstein_besge :
    12 * t.eisenstein 1 ^ 2 + 6 * t.rSum = 5 * t.eisenstein 3 + t.eisenstein 1 := by
  rw [t.eisenstein_one_sq_eq_qexp, t.rSum_eq_qexp, t.eisenstein_eq_qexp 3, t.eisenstein_eq_qexp 1]
  have hA := t.summable_qexp (c := fun N => ∑ s ∈ Finset.Ico 1 (N + 1),
      (∑ d ∈ s.divisors, (d : K)) * ∑ d ∈ (N + 1 - s).divisors, (d : K))
    fun N => norm_finset_sum_le_one fun s _ =>
      norm_mul_le_one' (norm_divisor_sum_le_one s) (norm_divisor_sum_le_one (N + 1 - s))
  have hB := t.summable_qexp (c := fun N => ((N + 1 : ℕ) : K) * ∑ d ∈ (N + 1).divisors, (d : K))
    fun N => norm_mul_le_one' (IsUltrametricDist.norm_natCast_le_one K (N + 1))
      (norm_divisor_sum_le_one (N + 1))
  have hC := t.summable_qexp (c := fun N => ∑ d ∈ (N + 1).divisors, (d : K) ^ 3)
    fun N => norm_divisor_pow_sum_le_one 3 (N + 1)
  have hD := t.summable_qexp (c := fun N => ∑ d ∈ (N + 1).divisors, (d : K) ^ 1)
    fun N => norm_divisor_pow_sum_le_one 1 (N + 1)
  rw [← tsum_mul_left (a := (12 : K)), ← tsum_mul_left (a := (6 : K)),
    ← tsum_mul_left (a := (5 : K)),
    ← Summable.tsum_add (hA.mul_left 12) (hB.mul_left 6),
    ← Summable.tsum_add (hC.mul_left 5) hD]
  refine tsum_congr fun N => ?_
  have hZ := besge_identity (N + 1) (Nat.succ_pos N)
  simp only [sigmaZ, pow_one] at hZ
  simp only [pow_one]
  have hzid : 12 * ∑ s ∈ Finset.Ico 1 (N + 1),
        (∑ d ∈ s.divisors, (d : ℤ)) * ∑ d ∈ (N + 1 - s).divisors, (d : ℤ)
      + 6 * (((N + 1 : ℕ) : ℤ) * ∑ d ∈ (N + 1).divisors, (d : ℤ))
      = 5 * (∑ d ∈ (N + 1).divisors, (d : ℤ) ^ 3) + ∑ d ∈ (N + 1).divisors, (d : ℤ) := by
    linear_combination hZ
  have hcast : 12 * (∑ s ∈ Finset.Ico 1 (N + 1),
        (∑ d ∈ s.divisors, (d : K)) * ∑ d ∈ (N + 1 - s).divisors, (d : K))
      + 6 * (((N + 1 : ℕ) : K) * ∑ d ∈ (N + 1).divisors, (d : K))
      = 5 * (∑ d ∈ (N + 1).divisors, (d : K) ^ 3) + ∑ d ∈ (N + 1).divisors, (d : K) := by
    have h := congrArg (fun z : ℤ => (z : K)) hzid
    push_cast at h ⊢
    linear_combination h
  linear_combination (t.q : K) ^ (N + 1) * hcast

/-- **The `σ₁∗σ₃` evaluation in convergent-series form**:
`30·𝔪 + 240·s₁s₃ + s₁ = 10·s₃ + 21·s₅`, where `𝔪 = t.psiSum = ∑_N Nσ₃(N)qᴺ`. -/
theorem eisenstein_sigma_one_three :
    30 * t.psiSum + 240 * (t.eisenstein 1 * t.eisenstein 3) + t.eisenstein 1
      = 10 * t.eisenstein 3 + 21 * t.eisenstein 5 := by
  rw [t.eisenstein_one_mul_three_eq_qexp, t.psiSum_eq_qexp, t.eisenstein_eq_qexp 3,
    t.eisenstein_eq_qexp 5, t.eisenstein_eq_qexp 1]
  have hA := t.summable_qexp (c := fun N => ((N + 1 : ℕ) : K)
      * ∑ d ∈ (N + 1).divisors, (d : K) ^ 3)
    fun N => norm_mul_le_one' (IsUltrametricDist.norm_natCast_le_one K (N + 1))
      (norm_divisor_pow_sum_le_one 3 (N + 1))
  have hB := t.summable_qexp (c := fun N => ∑ s ∈ Finset.Ico 1 (N + 1),
      (∑ d ∈ s.divisors, (d : K)) * ∑ d ∈ (N + 1 - s).divisors, (d : K) ^ 3)
    fun N => norm_finset_sum_le_one fun s _ =>
      norm_mul_le_one' (norm_divisor_sum_le_one s) (norm_divisor_pow_sum_le_one 3 (N + 1 - s))
  have hC := t.summable_qexp (c := fun N => ∑ d ∈ (N + 1).divisors, (d : K) ^ 1)
    fun N => norm_divisor_pow_sum_le_one 1 (N + 1)
  have hD := t.summable_qexp (c := fun N => ∑ d ∈ (N + 1).divisors, (d : K) ^ 3)
    fun N => norm_divisor_pow_sum_le_one 3 (N + 1)
  have hE := t.summable_qexp (c := fun N => ∑ d ∈ (N + 1).divisors, (d : K) ^ 5)
    fun N => norm_divisor_pow_sum_le_one 5 (N + 1)
  rw [← tsum_mul_left (a := (30 : K)), ← tsum_mul_left (a := (240 : K)),
    ← tsum_mul_left (a := (10 : K)), ← tsum_mul_left (a := (21 : K)),
    ← Summable.tsum_add (hA.mul_left 30) (hB.mul_left 240),
    ← Summable.tsum_add ((hA.mul_left 30).add (hB.mul_left 240)) hC,
    ← Summable.tsum_add (hD.mul_left 10) (hE.mul_left 21)]
  refine tsum_congr fun N => ?_
  have hZ := sigma_one_three_conv (N + 1) (Nat.succ_pos N)
  simp only [sigmaZ, pow_one] at hZ
  simp only [pow_one]
  have hzid : 30 * (((N + 1 : ℕ) : ℤ) * ∑ d ∈ (N + 1).divisors, (d : ℤ) ^ 3)
      + 240 * (∑ s ∈ Finset.Ico 1 (N + 1),
          (∑ d ∈ s.divisors, (d : ℤ)) * ∑ d ∈ (N + 1 - s).divisors, (d : ℤ) ^ 3)
      + ∑ d ∈ (N + 1).divisors, (d : ℤ)
      = 10 * (∑ d ∈ (N + 1).divisors, (d : ℤ) ^ 3)
        + 21 * ∑ d ∈ (N + 1).divisors, (d : ℤ) ^ 5 := by
    linear_combination hZ
  have hcast : 30 * (((N + 1 : ℕ) : K) * ∑ d ∈ (N + 1).divisors, (d : K) ^ 3)
      + 240 * (∑ s ∈ Finset.Ico 1 (N + 1),
          (∑ d ∈ s.divisors, (d : K)) * ∑ d ∈ (N + 1 - s).divisors, (d : K) ^ 3)
      + ∑ d ∈ (N + 1).divisors, (d : K)
      = 10 * (∑ d ∈ (N + 1).divisors, (d : K) ^ 3)
        + 21 * ∑ d ∈ (N + 1).divisors, (d : K) ^ 5 := by
    have h := congrArg (fun z : ℤ => (z : K)) hzid
    push_cast at h ⊢
    linear_combination h
  linear_combination (t.q : K) ^ (N + 1) * hcast

end SeriesIdentities

/-! ### Identification of the folded constant series and the brackets -/

section Brackets

/-- The unweighted `p`-series is `s₁`: the divisor-swap symmetry of the double series. -/
lemma pSum_eq_eisenstein_one : t.pSum = t.eisenstein 1 := by
  rw [t.pSum_eq_qexp, t.eisenstein_eq_qexp 1]
  exact tsum_congr fun N => by simp only [pow_one]

/-- The unweighted `φ`-series is `s₃`. -/
lemma phiSum_eq_eisenstein_three : t.phiSum = t.eisenstein 3 := by
  rw [t.phiSum_eq_qexp, t.eisenstein_eq_qexp 3]

/-- The squared-`p` series evaluates to `(s₃ - s₁)/6`, in division-free form. -/
lemma pSqSum_six_eq : 6 * t.pSqSum = t.eisenstein 3 - t.eisenstein 1 := by
  rw [t.pSqSum_mul_six_eq_qexp, t.eisenstein_eq_qexp 3, t.eisenstein_eq_qexp 1]
  have hC := t.summable_qexp (c := fun N => ∑ d ∈ (N + 1).divisors, (d : K) ^ 3)
    fun N => norm_divisor_pow_sum_le_one 3 (N + 1)
  have hD := t.summable_qexp (c := fun N => ∑ d ∈ (N + 1).divisors, (d : K) ^ 1)
    fun N => norm_divisor_pow_sum_le_one 1 (N + 1)
  rw [← Summable.tsum_sub hC hD]
  refine tsum_congr fun N => ?_
  simp only [pow_one, Finset.sum_sub_distrib]
  ring

/-- The weighted `p·r`-series evaluates to `(𝔪 - ρ)/12`, in division-free form. -/
lemma prSum_twelve_eq : 12 * t.prSum = t.psiSum - t.rSum := by
  rw [t.prSum_mul_twelve_eq_qexp, t.psiSum_eq_qexp, t.rSum_eq_qexp]
  have hA := t.summable_qexp (c := fun N => ((N + 1 : ℕ) : K)
      * ∑ d ∈ (N + 1).divisors, (d : K) ^ 3)
    fun N => norm_mul_le_one' (IsUltrametricDist.norm_natCast_le_one K (N + 1))
      (norm_divisor_pow_sum_le_one 3 (N + 1))
  have hB := t.summable_qexp (c := fun N => ((N + 1 : ℕ) : K)
      * ∑ d ∈ (N + 1).divisors, (d : K))
    fun N => norm_mul_le_one' (IsUltrametricDist.norm_natCast_le_one K (N + 1))
      (norm_divisor_sum_le_one (N + 1))
  rw [← Summable.tsum_sub hA hB]
  refine tsum_congr fun N => ?_
  simp only [Finset.sum_sub_distrib]
  ring

/-- **The weight-4 bracket identity**: the coefficient of `S` in the Eisenstein assembly of
the Weierstrass defect vanishes. Equivalent to Besge's identity together with
`a₄ = -5s₃`. -/
theorem bracketA_eq_zero (h3 : (3 : K) ≠ 0) :
    12 * t.phiSum + 8 * t.pSqSum + 8 * t.rSum + 16 * t.eisenstein 1 ^ 2 + 4 * t.a₄ = 0 := by
  apply mul_left_cancel₀ h3
  rw [mul_zero]
  linear_combination 36 * t.phiSum_eq_eisenstein_three + 4 * t.pSqSum_six_eq
    + 4 * t.eisenstein_besge + 12 * t.a₄_def

/-- **The weight-6 bracket identity**: the constant term of the Eisenstein assembly of the
Weierstrass defect vanishes. Equivalent to the `σ₁∗σ₃` convolution evaluation together with
Besge's identity and `a₆ = -(5s₃ + 7s₅)/12`. -/
theorem bracketB_eq (h3 : (3 : K) ≠ 0) (h12 : (12 : K) ≠ 0) :
    2 * t.psiSum + 16 * t.prSum + 2 * t.rSum + 4 * t.eisenstein 1 ^ 2 + 4 * t.a₆
      = 16 * t.eisenstein 1 * t.rSum + 32 * t.eisenstein 1 ^ 3
        + 8 * t.a₄ * t.eisenstein 1 := by
  have h9 : (9 : K) ≠ 0 := by
    have h := mul_ne_zero h3 h3
    rwa [show (3 : K) * 3 = 9 by norm_num] at h
  have ha6 : 12 * t.a₆ = -(5 * t.eisenstein 3 + 7 * t.eisenstein 5) := by
    rw [t.a₆_def]
    field_simp
  apply mul_left_cancel₀ h9
  linear_combination 12 * t.prSum_twelve_eq + 3 * ha6
    + (-72 * t.eisenstein 1) * t.a₄_def
    + (1 - 24 * t.eisenstein 1) * t.eisenstein_besge + t.eisenstein_sigma_one_three

end Brackets

/-! ### The Weierstrass identity, unconditionally -/

section Closure

variable {u : Kˣ}

/-- **Vanishing of the Weierstrass defect** at every point off the `q`-orbit, over any
complete nonarchimedean field of characteristic prime to `12`. This is the analytic heart
of Silverman, *Advanced Topics*, Thm V.3.1, proved by the elementary Eisenstein
computation — uniformly in `u`, with no annulus or value-group restriction. -/
theorem tateDefect_eq_zero (h12 : (12 : K) ≠ 0)
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) : t.tateDefect u = 0 := by
  have h2 : (2 : K) ≠ 0 := fun h => h12 (by rw [show (12 : K) = 2 * 6 by norm_num, h, zero_mul])
  have h3 : (3 : K) ≠ 0 := fun h => h12 (by rw [show (12 : K) = 3 * 4 by norm_num, h, zero_mul])
  have h4 : (4 : K) ≠ 0 := by
    have h := mul_ne_zero h2 h2
    rwa [show (2 : K) * 2 = 4 by norm_num] at h
  exact t.tateDefect_eq_zero_of_brackets h2 h4 hu t.pSum_eq_eisenstein_one
    (t.bracketA_eq_zero h3) (t.bracketB_eq h3 h12)

/-- **The residual analytic seam `DefectLaurentRepr` holds** (with the zero coefficient
family): the defect is represented off the orbit by the identically-zero `q`-invariant
Laurent series. This discharges the seam of `TateCurve/TatePointMem.lean` (#146/#170). -/
theorem defectLaurentRepr (h12 : (12 : K) ≠ 0) : t.DefectLaurentRepr := by
  refine ⟨fun _ => 0, fun u => ?_, fun u hu => ?_, fun u => ?_⟩
  · exact summable_zero.congr fun n => (zero_mul _).symm
  · rw [t.tateDefect_eq_zero h12 hu]
    simp
  · simp

/-- **The Tate parametrization Weierstrass identity, unconditionally**: for every `u` off
the `q`-orbit the Tate point `(X(u), Y(u))` lies on the Tate curve `E_q`,
`Y(u)² + X(u)·Y(u) = X(u)³ + a₄·X(u) + a₆` (Silverman, *Advanced Topics*, Thm V.3.1).
This supersedes the conditional `tatePoint_mem`, whose `LaurentCoeffUnique` and
`DefectLaurentRepr` inputs are now both theorems. -/
theorem tatePoint_mem' (h12 : (12 : K) ≠ 0)
    (hu : ∀ n : ℤ, (t.q : K) ^ n * (u : K) ≠ 1) :
    t.tateCurve.toAffine.Equation (t.X u) (t.Y u) :=
  (t.tatePoint_equation_iff u).mpr (t.tateDefect_eq_zero h12 hu)

/-- **The Eisenstein pole-cancellation identity at the coefficient level** (#169): on a
field whose fundamental annulus `1 < ‖u‖ < ‖q‖⁻¹` is nonempty, every coefficient of the
annulus Laurent development of the Weierstrass defect vanishes. The defect vanishes
identically on the annulus (`tateDefect_eq_zero`), so by Strassmann's theorem — applied on
the sphere `‖·‖ = ‖u‖` through the rescaled family `ℓ ↦ defectAnnulusCoeff ℓ · uˡ`, which
kills the infinitely many norm-one witnesses `1 + qᵏ⁺¹` — the coefficients themselves are
zero. (For discretely-valued `K` with `‖Kˣ‖ = ‖q‖ᶻ` the annulus is empty and this
statement requires a base-change argument instead; the parametrization itself needs only
`tateDefect_eq_zero`, which is unconditional.) -/
theorem defectAnnulusCoeff_eq_zero (h12 : (12 : K) ≠ 0) {u : Kˣ}
    (h1 : 1 < ‖(u : K)‖) (h2 : ‖(t.q : K)‖ * ‖(u : K)‖ < 1) (ℓ : ℤ) :
    t.defectAnnulusCoeff ℓ = 0 := by
  classical
  -- every point of the annulus sphere `‖u·x‖ = ‖u‖`, `‖x‖ = 1`, is off the orbit
  have hoff : ∀ x : Kˣ, ‖(x : K)‖ = 1 →
      ∀ n : ℤ, (t.q : K) ^ n * ((u * x : Kˣ) : K) ≠ 1 := by
    intro x hx n hcontra
    have hnorm : ‖(t.q : K)‖ ^ n * ‖(u : K)‖ = 1 := by
      have h := congrArg norm hcontra
      rwa [norm_mul, norm_zpow, Units.val_mul, norm_mul, hx, mul_one, norm_one] at h
    have hsplit : n ≤ 0 ∨ 0 < n := by omega
    rcases hsplit with hn | hn
    · -- `‖q‖ⁿ ≥ 1` for `n ≤ 0`, so `‖q‖ⁿ‖u‖ > 1`
      have hq1 : (1 : ℝ) ≤ ‖(t.q : K)‖ ^ n := by
        have hpow : ‖(t.q : K)‖ ^ (-n).toNat ≤ 1 :=
          pow_le_one₀ (norm_nonneg _) t.norm_lt_one.le
        have hzpow : ‖(t.q : K)‖ ^ n = (‖(t.q : K)‖ ^ (-n).toNat)⁻¹ := by
          rw [← zpow_natCast, ← zpow_neg, Int.toNat_of_nonneg (by omega), neg_neg]
        rw [hzpow]
        exact one_le_inv₀ (pow_pos t.norm_q_pos _) |>.mpr hpow
      have : (1 : ℝ) < ‖(t.q : K)‖ ^ n * ‖(u : K)‖ :=
        lt_of_lt_of_le (by simpa using h1)
          (by nlinarith [norm_nonneg (u : K)])
      rw [hnorm] at this
      exact lt_irrefl 1 this
    · -- `‖q‖ⁿ ≤ ‖q‖` for `n ≥ 1`, so `‖q‖ⁿ‖u‖ < 1`
      have hqn : ‖(t.q : K)‖ ^ n ≤ ‖(t.q : K)‖ := by
        have hzpow : ‖(t.q : K)‖ ^ n = ‖(t.q : K)‖ ^ n.toNat := by
          rw [← zpow_natCast, Int.toNat_of_nonneg (by omega)]
        rw [hzpow]
        calc ‖(t.q : K)‖ ^ n.toNat ≤ ‖(t.q : K)‖ ^ 1 :=
              pow_le_pow_of_le_one (norm_nonneg _) t.norm_lt_one.le
                (show 1 ≤ n.toNat by omega)
          _ = ‖(t.q : K)‖ := pow_one _
      have hlt : ‖(t.q : K)‖ ^ n * ‖(u : K)‖ < 1 :=
        lt_of_le_of_lt (by nlinarith [norm_nonneg (u : K), t.norm_q_pos]) h2
      rw [hnorm] at hlt
      exact lt_irrefl 1 hlt
  -- the rescaled coefficient family vanishes on the whole unit sphere
  have hzero : ∀ x : Kˣ, ‖(x : K)‖ = 1 →
      HasSum (fun n : ℤ => (t.defectAnnulusCoeff n * (u : K) ^ n) * (x : K) ^ n) 0 := by
    intro x hx
    have hnorm1 : 1 < ‖((u * x : Kˣ) : K)‖ := by
      rwa [Units.val_mul, norm_mul, hx, mul_one]
    have hnorm2 : ‖(t.q : K)‖ * ‖((u * x : Kˣ) : K)‖ < 1 := by
      rwa [Units.val_mul, norm_mul, hx, mul_one]
    have hsum := t.tateDefect_hasSum_laurent (u * x) hnorm1 hnorm2
    rw [t.tateDefect_eq_zero h12 (hoff x hx)] at hsum
    have hfe : (fun n : ℤ => t.defectAnnulusCoeff n * ((u * x : Kˣ) : K) ^ n)
        = fun n : ℤ => (t.defectAnnulusCoeff n * (u : K) ^ n) * (x : K) ^ n := by
      funext n
      rw [Units.val_mul, mul_zpow]
      ring
    exact hfe ▸ hsum
  -- Strassmann on the unit sphere: infinitely many zeros force zero coefficients
  set c' : ℤ → K := fun n => t.defectAnnulusCoeff n * (u : K) ^ n with hc'
  have hc'sum : Summable c' := by
    have h := (hzero 1 (by simp)).summable
    refine h.congr fun n => ?_
    simp [hc']
  by_cases hne : c' = 0
  · have h := congrFun hne ℓ
    simp only [hc', Pi.zero_apply] at h
    exact (mul_eq_zero.mp h).resolve_right (zpow_ne_zero ℓ u.ne_zero)
  · exfalso
    have hfin := StrassmannSphere.finite_zeros hc'sum hne
    have hmem : ∀ k : ℕ, ((t.sphereWitness k : Kˣ) : K) ∈
        {v : K | ‖v‖ = 1 ∧ (∑' n : ℤ, c' n * v ^ n) = 0} := by
      intro k
      have hwnorm : ‖((t.sphereWitness k : Kˣ) : K)‖ = 1 := by
        rw [t.sphereWitness_val k]
        exact t.norm_one_add_qpow k
      exact ⟨hwnorm, (hzero (t.sphereWitness k) hwnorm).tsum_eq⟩
    have hinj : Function.Injective (fun k : ℕ => ((t.sphereWitness k : Kˣ) : K)) :=
      fun a b hab => t.sphereWitness_injective (Units.ext hab)
    exact Set.infinite_of_injective_forall_mem hinj hmem hfin

end Closure

end TateParameter

end TateCurvesTheta
