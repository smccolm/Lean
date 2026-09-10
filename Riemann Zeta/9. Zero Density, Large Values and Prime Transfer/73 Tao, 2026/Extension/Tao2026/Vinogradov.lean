import Tao2026.CriticalIntervals
import Tao2026.TypeIIArithmetic
import Mathlib.Analysis.Calculus.Taylor

/-!
# Vinogradov exponential-sum interface

This module assembles the exact derivative hypotheses for the high-scale
branch of the integer exponential-sum estimate.  The substantive Vinogradov
inequality is not yet asserted here: the results below remove its source
cutoff, logarithmic-parameter, and critical-deletion bookkeeping.
-/

namespace Tao2026

open scoped ContDiff

/-- The exact Vinogradov exponential-sum estimate with its absolute constant
made explicit.  This form lets all later asymptotic thresholds depend on that
single constant without re-selecting it for each phase or interval. -/
def VinogradovExponentialSumEstimateAt (C : ℝ) : Prop :=
  0 < C ∧ ∀ (X F α : ℝ) (a b : ℕ) (f : ℝ → ℝ),
      2 ≤ X → X ^ 4 ≤ F → 1 ≤ α →
      Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3 < (1 / 1000 : ℝ) →
      Set.Icc (a : ℝ) (b : ℝ) ⊆ Set.Icc X (2 * X) →
      (∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t) →
      (∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
        r ≤ vinogradovDerivativeCutoff X F →
        F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F) →
      ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
        C * α * X * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)

/-- Exact integer-interval form of the Vinogradov exponential-sum estimate
used by the source.  Proving this proposition is the remaining substantive
analytic input: the constant is absolute and all parameter restrictions are
quantified explicitly. -/
def VinogradovExponentialSumEstimate : Prop :=
  ∃ C : ℝ, VinogradovExponentialSumEstimateAt C

/-- The degree `R = 10⌈log F / log X⌉` of the Taylor polynomial in the
source proof of the Vinogradov estimate.  The derivative cutoff is `R + 1`.-/
noncomputable def vinogradovTaylorDegree (X F : ℝ) : ℕ :=
  10 * ⌈Real.log F / Real.log X⌉₊

@[simp]
theorem vinogradovTaylorDegree_add_one (X F : ℝ) :
    vinogradovTaylorDegree X F + 1 = vinogradovDerivativeCutoff X F := by
  rfl

/-- Tao's polynomial `F_n(q)`, with coefficient
`α_r(n) = f^(r)(n) / r!`. -/
noncomputable def vinogradovTaylorPolynomial
    (f : ℝ → ℝ) (R : ℕ) (x q : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (R + 1),
    iteratedDeriv r f x / (r.factorial : ℝ) * q ^ r

/-- On a genuinely smooth forward interval, Mathlib's within-Taylor
polynomial is exactly Tao's polynomial with ordinary iterated derivatives. -/
theorem taylorWithinEval_eq_vinogradovTaylorPolynomial
    {f : ℝ → ℝ} {R : ℕ} {x q : ℝ} (hq : 0 < q)
    (hsmooth : ContDiffAt ℝ ∞ f x) :
    taylorWithinEval f R (Set.Icc x (x + q)) x (x + q) =
      vinogradovTaylorPolynomial f R x q := by
  rw [taylor_within_apply]
  unfold vinogradovTaylorPolynomial
  apply Finset.sum_congr rfl
  intro r hr
  rw [iteratedDerivWithin_eq_iteratedDeriv
    (uniqueDiffOn_Icc (by linarith : x < x + q))
    ((contDiffAt_infty.mp hsmooth) r) ⟨le_rfl, by linarith⟩]
  simp only [add_sub_cancel_left, smul_eq_mul]
  ring

/-- The exact Lagrange remainder identity for a forward Taylor step.  This is
the calculus input used before the polynomial exponential-sum argument in the
pinned proof of the Vinogradov estimate. -/
theorem exists_vinogradovTaylor_remainder_lagrange
    {f : ℝ → ℝ} {R : ℕ} {x q : ℝ} (hq : 0 < q)
    (hf : ContDiffOn ℝ (R + 1) f (Set.Icc x (x + q))) :
    ∃ ξ ∈ Set.Ioo x (x + q),
      f (x + q) -
          taylorWithinEval f R (Set.Icc x (x + q)) x (x + q) =
        iteratedDeriv (R + 1) f ξ * q ^ (R + 1) / (R + 1).factorial := by
  have hx : x < x + q := by linarith
  have hf' : ContDiffOn ℝ (R + 1) f (Set.uIcc x (x + q)) := by
    rwa [Set.uIcc_of_le hx.le]
  have hTaylor := taylor_mean_remainder_lagrange_iteratedDeriv
    (f := f) (x₀ := x) (x := x + q) (n := R) hx.ne hf'
  rw [Set.uIcc_of_le hx.le, Set.uIoo_of_le hx.le] at hTaylor
  simpa only [add_sub_cancel_left] using hTaylor

/-- Source notation form of the same identity, now literally involving
`F_x(q) = ∑_{r≤R} f^(r)(x) q^r / r!`. -/
theorem exists_vinogradovTaylorPolynomial_remainder_lagrange
    {f : ℝ → ℝ} {R : ℕ} {x q : ℝ} (hq : 0 < q)
    (hsmooth : ∀ t ∈ Set.Icc x (x + q), ContDiffAt ℝ ∞ f t) :
    ∃ ξ ∈ Set.Ioo x (x + q),
      f (x + q) - vinogradovTaylorPolynomial f R x q =
        iteratedDeriv (R + 1) f ξ * q ^ (R + 1) / (R + 1).factorial := by
  have hf : ContDiffOn ℝ (R + 1) f (Set.Icc x (x + q)) := by
    intro t ht
    exact ((contDiffAt_infty.mp (hsmooth t ht)) (R + 1)).contDiffWithinAt
  obtain ⟨ξ, hξ, hrem⟩ :=
    exists_vinogradovTaylor_remainder_lagrange hq hf
  refine ⟨ξ, hξ, ?_⟩
  rw [← taylorWithinEval_eq_vinogradovTaylorPolynomial hq
    (hsmooth x ⟨le_rfl, by linarith⟩)]
  exact hrem

/-- Uniform derivative control turns the exact Lagrange identity into the
pointwise Taylor-error bound used in the source averaging argument. -/
theorem abs_vinogradovTaylor_remainder_le
    {f : ℝ → ℝ} {R : ℕ} {x q D : ℝ} (hq : 0 < q)
    (hf : ContDiffOn ℝ (R + 1) f (Set.Icc x (x + q)))
    (hD : ∀ ξ ∈ Set.Icc x (x + q),
      |iteratedDeriv (R + 1) f ξ| ≤ D) :
    |f (x + q) -
          taylorWithinEval f R (Set.Icc x (x + q)) x (x + q)| ≤
      D * q ^ (R + 1) / (R + 1).factorial := by
  obtain ⟨ξ, hξ, hrem⟩ :=
    exists_vinogradovTaylor_remainder_lagrange hq hf
  have hqabs : |q ^ (R + 1)| = q ^ (R + 1) :=
    abs_of_nonneg (pow_nonneg hq.le _)
  have hfactabs : |((R + 1).factorial : ℝ)| = (R + 1).factorial :=
    abs_of_nonneg (Nat.cast_nonneg _)
  rw [hrem, abs_div, abs_mul, hqabs, hfactabs]
  gcongr
  exact hD ξ ⟨hξ.1.le, hξ.2.le⟩

/-- Source-normalized derivative control gives the scale-free Taylor error
`B (q/x)^(R+1)`: the factorial in Taylor's formula cancels the factorial in
the derivative hypothesis. -/
theorem abs_vinogradovTaylor_remainder_le_normalized
    {f : ℝ → ℝ} {R : ℕ} {x q B : ℝ} (hx : 0 < x) (hq : 0 < q)
    (hf : ContDiffOn ℝ (R + 1) f (Set.Icc x (x + q)))
    (hupper : ∀ ξ ∈ Set.Icc x (x + q),
      ξ ^ (R + 1) / (R + 1).factorial *
          |iteratedDeriv (R + 1) f ξ| ≤ B) :
    |f (x + q) -
          taylorWithinEval f R (Set.Icc x (x + q)) x (x + q)| ≤
      B * (q / x) ^ (R + 1) := by
  have hfac : 0 < (((R + 1).factorial : ℕ) : ℝ) := by positivity
  have hxpow : 0 < x ^ (R + 1) := pow_pos hx _
  have hD : ∀ ξ ∈ Set.Icc x (x + q),
      |iteratedDeriv (R + 1) f ξ| ≤
        (((R + 1).factorial : ℕ) : ℝ) * B / x ^ (R + 1) := by
    intro ξ hξ
    have hpow : x ^ (R + 1) ≤ ξ ^ (R + 1) :=
      pow_le_pow_left₀ hx.le hξ.1 _
    have hcoef : x ^ (R + 1) / (((R + 1).factorial : ℕ) : ℝ) ≤
        ξ ^ (R + 1) / (((R + 1).factorial : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hpow hfac.le
    have hscaled : x ^ (R + 1) / (((R + 1).factorial : ℕ) : ℝ) *
          |iteratedDeriv (R + 1) f ξ| ≤ B :=
      (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)).trans (hupper ξ hξ)
    have hscaled' : x ^ (R + 1) * |iteratedDeriv (R + 1) f ξ| /
          (((R + 1).factorial : ℕ) : ℝ) ≤ B := by
      simpa [div_mul_eq_mul_div] using hscaled
    apply (le_div_iff₀ hxpow).2
    have hmul := (div_le_iff₀ hfac).1 hscaled'
    simpa [mul_comm] using hmul
  calc
    |f (x + q) -
        taylorWithinEval f R (Set.Icc x (x + q)) x (x + q)| ≤
        ((((R + 1).factorial : ℕ) : ℝ) * B / x ^ (R + 1)) *
          q ^ (R + 1) / (R + 1).factorial :=
      abs_vinogradovTaylor_remainder_le hq hf hD
    _ = B * (q / x) ^ (R + 1) := by
      rw [div_pow]
      field_simp [hx.ne', hfac.ne']

/-- Source-polynomial form of the normalized Taylor error. -/
theorem abs_vinogradovTaylorPolynomial_remainder_le_normalized
    {f : ℝ → ℝ} {R : ℕ} {x q B : ℝ} (hx : 0 < x) (hq : 0 < q)
    (hsmooth : ∀ t ∈ Set.Icc x (x + q), ContDiffAt ℝ ∞ f t)
    (hupper : ∀ ξ ∈ Set.Icc x (x + q),
      ξ ^ (R + 1) / (R + 1).factorial *
          |iteratedDeriv (R + 1) f ξ| ≤ B) :
    |f (x + q) - vinogradovTaylorPolynomial f R x q| ≤
      B * (q / x) ^ (R + 1) := by
  have hf : ContDiffOn ℝ (R + 1) f (Set.Icc x (x + q)) := by
    intro t ht
    exact ((contDiffAt_infty.mp (hsmooth t ht)) (R + 1)).contDiffWithinAt
  rw [← taylorWithinEval_eq_vinogradovTaylorPolynomial hq
    (hsmooth x ⟨le_rfl, by linarith⟩)]
  exact abs_vinogradovTaylor_remainder_le_normalized hx hq hf hupper

/-- Replacing a real phase by an approximation costs at most `2π` times
the total phase error. -/
theorem norm_sum_standardAdditiveCharacter_sub_le_sum_abs
    {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    ‖(∑ i ∈ s, standardAdditiveCharacter (f i)) -
        ∑ i ∈ s, standardAdditiveCharacter (g i)‖ ≤
      2 * Real.pi * ∑ i ∈ s, |f i - g i| := by
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i ∈ s,
        (standardAdditiveCharacter (f i) - standardAdditiveCharacter (g i))‖ ≤
        ∑ i ∈ s,
          ‖standardAdditiveCharacter (f i) - standardAdditiveCharacter (g i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, 2 * Real.pi * |f i - g i| := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_standardAdditiveCharacter_sub_le (f i) (g i)
    _ = 2 * Real.pi * ∑ i ∈ s, |f i - g i| := by
      rw [Finset.mul_sum]

/-- Finite-sum form of the Taylor replacement error.  It is the precise
calculus estimate needed when the source proof averages the Taylor shift over
its product multiset of shifts. -/
theorem norm_sum_standardAdditiveCharacter_taylorWithinEval_sub_le
    (s : Finset ℕ) {f : ℝ → ℝ} {R : ℕ} {q D : ℝ} (hq : 0 < q)
    (hf : ∀ n ∈ s,
      ContDiffOn ℝ (R + 1) f (Set.Icc (n : ℝ) (n + q)))
    (hD : ∀ n ∈ s, ∀ ξ ∈ Set.Icc (n : ℝ) (n + q),
      |iteratedDeriv (R + 1) f ξ| ≤ D) :
    ‖(∑ n ∈ s, standardAdditiveCharacter (f (n + q))) -
        ∑ n ∈ s, standardAdditiveCharacter
          (taylorWithinEval f R (Set.Icc (n : ℝ) (n + q)) n (n + q))‖ ≤
      2 * Real.pi * (s.card : ℝ) *
        (D * q ^ (R + 1) / (R + 1).factorial) := by
  have hpoint : ∀ n ∈ s,
      |f (n + q) -
          taylorWithinEval f R (Set.Icc (n : ℝ) (n + q)) n (n + q)| ≤
        D * q ^ (R + 1) / (R + 1).factorial := by
    intro n hn
    exact abs_vinogradovTaylor_remainder_le hq (hf n hn) (hD n hn)
  calc
    ‖(∑ n ∈ s, standardAdditiveCharacter (f (n + q))) -
        ∑ n ∈ s, standardAdditiveCharacter
          (taylorWithinEval f R (Set.Icc (n : ℝ) (n + q)) n (n + q))‖ ≤
      2 * Real.pi * ∑ n ∈ s,
        |f (n + q) -
          taylorWithinEval f R (Set.Icc (n : ℝ) (n + q)) n (n + q)| :=
      norm_sum_standardAdditiveCharacter_sub_le_sum_abs s _ _
    _ ≤ 2 * Real.pi * ∑ _n ∈ s,
        (D * q ^ (R + 1) / (R + 1).factorial) := by
      gcongr with n hn
      exact hpoint n hn
    _ = 2 * Real.pi * (s.card : ℝ) *
        (D * q ^ (R + 1) / (R + 1).factorial) := by
      simp [mul_assoc]

/-- Source-normalized finite-sum Taylor replacement on a range whose base
points are all at least `X`.  This packages the exact error term that must be
made negligible before invoking the polynomial Vinogradov estimate. -/
theorem norm_sum_standardAdditiveCharacter_taylorWithinEval_sub_le_normalized
    (s : Finset ℕ) {f : ℝ → ℝ} {R : ℕ} {X q B : ℝ}
    (hX : 0 < X) (hq : 0 < q) (hB : 0 ≤ B)
    (hXn : ∀ n ∈ s, X ≤ (n : ℝ))
    (hf : ∀ n ∈ s,
      ContDiffOn ℝ (R + 1) f (Set.Icc (n : ℝ) (n + q)))
    (hupper : ∀ n ∈ s, ∀ ξ ∈ Set.Icc (n : ℝ) (n + q),
      ξ ^ (R + 1) / (R + 1).factorial *
          |iteratedDeriv (R + 1) f ξ| ≤ B) :
    ‖(∑ n ∈ s, standardAdditiveCharacter (f (n + q))) -
        ∑ n ∈ s, standardAdditiveCharacter
          (taylorWithinEval f R (Set.Icc (n : ℝ) (n + q)) n (n + q))‖ ≤
      2 * Real.pi * (s.card : ℝ) * (B * (q / X) ^ (R + 1)) := by
  have hpoint : ∀ n ∈ s,
      |f (n + q) -
          taylorWithinEval f R (Set.Icc (n : ℝ) (n + q)) n (n + q)| ≤
        B * (q / X) ^ (R + 1) := by
    intro n hn
    have hnpos : 0 < (n : ℝ) := hX.trans_le (hXn n hn)
    calc
      |f (n + q) -
          taylorWithinEval f R (Set.Icc (n : ℝ) (n + q)) n (n + q)| ≤
          B * (q / (n : ℝ)) ^ (R + 1) :=
        abs_vinogradovTaylor_remainder_le_normalized hnpos hq
          (hf n hn) (hupper n hn)
      _ ≤ B * (q / X) ^ (R + 1) := by
        gcongr
        exact hXn n hn
  calc
    ‖(∑ n ∈ s, standardAdditiveCharacter (f (n + q))) -
        ∑ n ∈ s, standardAdditiveCharacter
          (taylorWithinEval f R (Set.Icc (n : ℝ) (n + q)) n (n + q))‖ ≤
      2 * Real.pi * ∑ n ∈ s,
        |f (n + q) -
          taylorWithinEval f R (Set.Icc (n : ℝ) (n + q)) n (n + q)| :=
      norm_sum_standardAdditiveCharacter_sub_le_sum_abs s _ _
    _ ≤ 2 * Real.pi * ∑ _n ∈ s, B * (q / X) ^ (R + 1) := by
      gcongr with n hn
      exact hpoint n hn
    _ = 2 * Real.pi * (s.card : ℝ) * (B * (q / X) ^ (R + 1)) := by
      simp [mul_assoc]

/-- Literal source-cutoff specialization of the Taylor replacement bound.
The hypotheses are stated on one ambient interval, exactly as in
`VinogradovExponentialSumEstimateAt`; each shifted Taylor segment is obtained
by restriction. -/
theorem norm_sum_standardAdditiveCharacter_taylorWithinEval_sub_le_sourceCutoff
    (s : Finset ℕ) {f : ℝ → ℝ} {X F α q u v : ℝ}
    (hX : 0 < X) (hq : 0 < q) (hα : 0 ≤ α) (hF : 0 ≤ F)
    (hXn : ∀ n ∈ s, X ≤ (n : ℝ))
    (hwindow : ∀ n ∈ s,
      Set.Icc (n : ℝ) (n + q) ⊆ Set.Icc u v)
    (hsmooth : ∀ t ∈ Set.Icc u v, ContDiffAt ℝ ∞ f t)
    (hupper : ∀ ξ ∈ Set.Icc u v,
      ξ ^ (vinogradovDerivativeCutoff X F) /
          (vinogradovDerivativeCutoff X F).factorial *
          |iteratedDeriv (vinogradovDerivativeCutoff X F) f ξ| ≤
        α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) :
    ‖(∑ n ∈ s, standardAdditiveCharacter (f (n + q))) -
        ∑ n ∈ s, standardAdditiveCharacter
          (taylorWithinEval f (vinogradovTaylorDegree X F)
            (Set.Icc (n : ℝ) (n + q)) n (n + q))‖ ≤
      2 * Real.pi * (s.card : ℝ) *
        ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
          (q / X) ^ (vinogradovDerivativeCutoff X F)) := by
  apply norm_sum_standardAdditiveCharacter_taylorWithinEval_sub_le_normalized
    s hX hq (mul_nonneg (pow_nonneg hα _) hF) hXn
  · intro n hn t ht
    exact ((contDiffAt_infty.mp (hsmooth t (hwindow n hn ht)))
      (vinogradovTaylorDegree X F + 1)).contDiffWithinAt
  · intro n hn ξ hξ
    simpa only [vinogradovTaylorDegree_add_one] using
      hupper ξ (hwindow n hn hξ)

/-- The Taylor front end extracted directly from the hypotheses of the source
Vinogradov lemma.  In particular, no separate bound for the top derivative is
left as a callback. -/
theorem norm_sum_standardAdditiveCharacter_taylorWithinEval_sub_le_of_sourceHypotheses
    (s : Finset ℕ) {f : ℝ → ℝ} {X F α q u v : ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α) (hq : 0 < q)
    (hXn : ∀ n ∈ s, X ≤ (n : ℝ))
    (hwindow : ∀ n ∈ s,
      Set.Icc (n : ℝ) (n + q) ⊆ Set.Icc u v)
    (hsmooth : ∀ t ∈ Set.Icc u v, ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc u v, ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F) :
    ‖(∑ n ∈ s, standardAdditiveCharacter (f (n + q))) -
        ∑ n ∈ s, standardAdditiveCharacter
          (taylorWithinEval f (vinogradovTaylorDegree X F)
            (Set.Icc (n : ℝ) (n + q)) n (n + q))‖ ≤
      2 * Real.pi * (s.card : ℝ) *
        ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
          (q / X) ^ (vinogradovDerivativeCutoff X F)) := by
  have hR : 1 ≤ vinogradovDerivativeCutoff X F := by
    simp [vinogradovDerivativeCutoff]
  have hF : 0 ≤ F := by
    calc
      0 ≤ X ^ 4 := by positivity
      _ ≤ F := hFhigh
  apply norm_sum_standardAdditiveCharacter_taylorWithinEval_sub_le_sourceCutoff
    s (by linarith) hq (by linarith) hF hXn hwindow hsmooth
  intro ξ hξ
  exact (hderiv ξ hξ (vinogradovDerivativeCutoff X F) hR le_rfl).2

/-- The preceding source-hypothesis estimate expressed with Tao's literal
polynomials `F_n(q)`.  This closes the Taylor-replacement portion of the
pinned Vinogradov proof; the subsequent polynomial mean-value estimate is a
separate analytic stage. -/
theorem norm_sum_standardAdditiveCharacter_vinogradovTaylorPolynomial_sub_le_of_sourceHypotheses
    (s : Finset ℕ) {f : ℝ → ℝ} {X F α q u v : ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α) (hq : 0 < q)
    (hXn : ∀ n ∈ s, X ≤ (n : ℝ))
    (hwindow : ∀ n ∈ s,
      Set.Icc (n : ℝ) (n + q) ⊆ Set.Icc u v)
    (hsmooth : ∀ t ∈ Set.Icc u v, ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc u v, ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F) :
    ‖(∑ n ∈ s, standardAdditiveCharacter (f (n + q))) -
        ∑ n ∈ s, standardAdditiveCharacter
          (vinogradovTaylorPolynomial f (vinogradovTaylorDegree X F) n q)‖ ≤
      2 * Real.pi * (s.card : ℝ) *
        ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
          (q / X) ^ (vinogradovDerivativeCutoff X F)) := by
  have h :=
    norm_sum_standardAdditiveCharacter_taylorWithinEval_sub_le_of_sourceHypotheses
      s hX hFhigh hα hq hXn hwindow hsmooth hderiv
  have hsum :
      (∑ n ∈ s, standardAdditiveCharacter
        (taylorWithinEval f (vinogradovTaylorDegree X F)
          (Set.Icc (n : ℝ) (n + q)) n (n + q))) =
        ∑ n ∈ s, standardAdditiveCharacter
          (vinogradovTaylorPolynomial f (vinogradovTaylorDegree X F) n q) := by
    apply Finset.sum_congr rfl
    intro n hn
    congr 1
    apply taylorWithinEval_eq_vinogradovTaylorPolynomial hq
    exact hsmooth n (hwindow n hn ⟨le_rfl, by linarith⟩)
  rw [hsum] at h
  exact h

/-- Shifting an integer interval forward by `q` and trimming its right edge
costs only the `q` points at the left boundary for a unit-norm phase. -/
theorem norm_sum_Ico_standardAdditiveCharacter_sub_forwardShift_le
    (f : ℝ → ℝ) (a b q : ℕ) :
    ‖(∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)) -
        ∑ n ∈ Finset.Ico a (b - q),
          standardAdditiveCharacter (f ((n + q : ℕ) : ℝ))‖ ≤ (q : ℝ) := by
  by_cases haqb : a + q ≤ b
  · have hqb : q ≤ b := q.le_add_left a |>.trans haqb
    have hshift :
        (∑ n ∈ Finset.Ico a (b - q),
            standardAdditiveCharacter (f ((n + q : ℕ) : ℝ))) =
          ∑ n ∈ Finset.Ico (a + q) b,
            standardAdditiveCharacter (f n) := by
      simpa only [Nat.cast_add, Nat.sub_add_cancel hqb] using
        (Finset.sum_Ico_add'
          (fun n : ℕ => standardAdditiveCharacter (f n)) a (b - q) q)
    have hsplit := Finset.sum_Ico_consecutive
      (fun n : ℕ => standardAdditiveCharacter (f n))
      (Nat.le_add_right a q) haqb
    rw [hshift, ← hsplit, add_sub_cancel_right]
    calc
      ‖∑ n ∈ Finset.Ico a (a + q), standardAdditiveCharacter (f n)‖ ≤
          ∑ n ∈ Finset.Ico a (a + q),
            ‖standardAdditiveCharacter (f n)‖ := norm_sum_le _ _
      _ = (q : ℝ) := by simp
  · have hempty : Finset.Ico a (b - q) = ∅ := by
      apply Finset.Ico_eq_empty
      omega
    rw [hempty, Finset.sum_empty, sub_zero]
    calc
      ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
          ∑ n ∈ Finset.Ico a b,
            ‖standardAdditiveCharacter (f n)‖ := norm_sum_le _ _
      _ = ((b - a : ℕ) : ℝ) := by simp
      _ ≤ (q : ℝ) := by exact_mod_cast (show b - a ≤ q by omega)

/-- Complete source Taylor-expansion estimate on an integer interval: after a
positive integral shift, the original phase sum differs from the sum of Tao's
literal polynomials by one boundary term plus the normalized Taylor error. -/
theorem norm_sum_Ico_standardAdditiveCharacter_sub_vinogradovTaylorPolynomial_le
    {f : ℝ → ℝ} {X F α : ℝ} {a b q : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hq : 0 < q) (hXa : X ≤ (a : ℝ))
    (hsmooth : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F) :
    ‖(∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)) -
        ∑ n ∈ Finset.Ico a (b - q), standardAdditiveCharacter
          (vinogradovTaylorPolynomial f (vinogradovTaylorDegree X F) n q)‖ ≤
      (q : ℝ) + 2 * Real.pi * ((Finset.Ico a (b - q)).card : ℝ) *
        ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
          ((q : ℝ) / X) ^ (vinogradovDerivativeCutoff X F)) := by
  let S : Finset ℕ := Finset.Ico a (b - q)
  have hXn : ∀ n ∈ S, X ≤ (n : ℝ) := by
    intro n hn
    exact hXa.trans (by exact_mod_cast (Finset.mem_Ico.mp hn).1)
  have hwindow : ∀ n ∈ S,
      Set.Icc (n : ℝ) (n + (q : ℝ)) ⊆ Set.Icc (a : ℝ) (b : ℝ) := by
    intro n hn t ht
    have hn := Finset.mem_Ico.mp hn
    constructor
    · have han : (a : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
      exact han.trans ht.1
    · have hnq : n + q ≤ b := by
        omega
      exact ht.2.trans (by exact_mod_cast hnq)
  have hTaylor :=
    norm_sum_standardAdditiveCharacter_vinogradovTaylorPolynomial_sub_le_of_sourceHypotheses
      S hX hFhigh hα (by exact_mod_cast hq) hXn hwindow hsmooth hderiv
  have hshift :=
    norm_sum_Ico_standardAdditiveCharacter_sub_forwardShift_le f a b q
  calc
    ‖(∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)) -
        ∑ n ∈ S, standardAdditiveCharacter
          (vinogradovTaylorPolynomial f (vinogradovTaylorDegree X F) n q)‖ =
      ‖((∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)) -
          ∑ n ∈ S, standardAdditiveCharacter (f (n + (q : ℝ)))) +
        ((∑ n ∈ S, standardAdditiveCharacter (f (n + (q : ℝ)))) -
          ∑ n ∈ S, standardAdditiveCharacter
            (vinogradovTaylorPolynomial f (vinogradovTaylorDegree X F) n q))‖ := by
        congr 1
        ring
    _ ≤ ‖(∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)) -
          ∑ n ∈ S, standardAdditiveCharacter (f (n + (q : ℝ)))‖ +
        ‖(∑ n ∈ S, standardAdditiveCharacter (f (n + (q : ℝ)))) -
          ∑ n ∈ S, standardAdditiveCharacter
            (vinogradovTaylorPolynomial f (vinogradovTaylorDegree X F) n q)‖ :=
      norm_add_le _ _
    _ ≤ (q : ℝ) + 2 * Real.pi * (S.card : ℝ) *
        ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
          ((q : ℝ) / X) ^ (vinogradovDerivativeCutoff X F)) := by
      apply add_le_add
      · simpa only [S, Nat.cast_add] using hshift
      · exact hTaylor

/-- Triangle inequality for an unnormalized finite average. -/
theorem norm_card_nsmul_sub_sum_le_sum_norm_sub
    {ι : Type*} (s : Finset ι) (z : ℂ) (g : ι → ℂ) :
    ‖s.card • z - ∑ i ∈ s, g i‖ ≤ ∑ i ∈ s, ‖z - g i‖ := by
  rw [← Finset.sum_const, ← Finset.sum_sub_distrib]
  exact norm_sum_le _ _

/-- The product multiset `{xy : 1 ≤ x,y ≤ V}` is represented by its pairs,
so equal products retain their source multiplicities. -/
def vinogradovShiftPairs (V : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 V).product (Finset.Icc 1 V)

@[simp]
theorem card_vinogradovShiftPairs (V : ℕ) :
    (vinogradovShiftPairs V).card = V ^ 2 := by
  simp [vinogradovShiftPairs, pow_two]

/-- The unnormalized polynomial sum over Tao's product multiset of shifts. -/
noncomputable def vinogradovTaylorPolynomialPairSum
    (f : ℝ → ℝ) (R a b V : ℕ) : ℂ :=
  ∑ p ∈ vinogradovShiftPairs V,
    ∑ n ∈ Finset.Ico a (b - p.1 * p.2),
      standardAdditiveCharacter
        (vinogradovTaylorPolynomial f R n ((p.1 * p.2 : ℕ) : ℝ))

/-- The complete product-multiset polynomial sum at one base point `n`.  This
is the bilinear sum estimated pointwise in the Iwaniec--Kowalski stage. -/
noncomputable def vinogradovTaylorPolynomialLocalProductSum
    (f : ℝ → ℝ) (R n V : ℕ) : ℂ :=
  ∑ p ∈ vinogradovShiftPairs V,
    standardAdditiveCharacter
      (vinogradovTaylorPolynomial f R n ((p.1 * p.2 : ℕ) : ℝ))

/-- Positive-degree part of Tao's Taylor polynomial. -/
noncomputable def vinogradovTaylorPositivePolynomial
    (f : ℝ → ℝ) (R : ℕ) (n q : ℝ) : ℝ :=
  ∑ r ∈ Finset.range R,
    iteratedDeriv (r + 1) f n / ((r + 1).factorial : ℝ) * q ^ (r + 1)

theorem vinogradovTaylorPolynomial_eq_constant_add_positive
    (f : ℝ → ℝ) (R : ℕ) (n q : ℝ) :
    vinogradovTaylorPolynomial f R n q =
      f n + vinogradovTaylorPositivePolynomial f R n q := by
  unfold vinogradovTaylorPolynomial vinogradovTaylorPositivePolynomial
  rw [Finset.sum_range_succ']
  simp [add_comm]

/-- Bilinear polynomial phase after writing `q = xy`. -/
noncomputable def vinogradovTaylorBilinearPhase
    (f : ℝ → ℝ) (R : ℕ) (n x y : ℝ) : ℝ :=
  ∑ r ∈ Finset.range R,
    iteratedDeriv (r + 1) f n / ((r + 1).factorial : ℝ) *
      x ^ (r + 1) * y ^ (r + 1)

theorem vinogradovTaylorPositivePolynomial_mul
    (f : ℝ → ℝ) (R : ℕ) (n x y : ℝ) :
    vinogradovTaylorPositivePolynomial f R n (x * y) =
      vinogradovTaylorBilinearPhase f R n x y := by
  unfold vinogradovTaylorPositivePolynomial vinogradovTaylorBilinearPhase
  apply Finset.sum_congr rfl
  intro r hr
  rw [mul_pow]
  ring

/-- Iterated-sum form of the pointwise bilinear polynomial sum. -/
noncomputable def vinogradovTaylorBilinearSum
    (f : ℝ → ℝ) (R n V : ℕ) : ℂ :=
  ∑ x ∈ Finset.Icc 1 V, ∑ y ∈ Finset.Icc 1 V,
    standardAdditiveCharacter
      (vinogradovTaylorBilinearPhase f R n x y)

/-- Coefficient sequence of Tao's Taylor polynomial. -/
noncomputable def vinogradovTaylorCoefficient
    (f : ℝ → ℝ) (n : ℝ) (r : ℕ) : ℝ :=
  iteratedDeriv r f n / (r.factorial : ℝ)

/-- Generic diagonal bilinear polynomial sum
`∑_{x,y} e(∑_{1≤r≤R} c_r x^r y^r)`. -/
noncomputable def vinogradovBilinearPolynomialSum
    (c : ℕ → ℝ) (R V : ℕ) : ℂ :=
  ∑ x ∈ Finset.Icc 1 V, ∑ y ∈ Finset.Icc 1 V,
    standardAdditiveCharacter
      (∑ r ∈ Finset.range R, c (r + 1) * x ^ (r + 1) * y ^ (r + 1))

theorem vinogradovTaylorBilinearSum_eq_bilinearPolynomialSum
    (f : ℝ → ℝ) (R n V : ℕ) :
    vinogradovTaylorBilinearSum f R n V =
      vinogradovBilinearPolynomialSum
        (vinogradovTaylorCoefficient f n) R V := by
  unfold vinogradovTaylorBilinearSum vinogradovBilinearPolynomialSum
    vinogradovTaylorBilinearPhase vinogradovTaylorCoefficient
  rfl

theorem pow_mul_abs_vinogradovTaylorCoefficient
    (f : ℝ → ℝ) (n : ℝ) (r : ℕ) :
    n ^ r * |vinogradovTaylorCoefficient f n r| =
      n ^ r / (r.factorial : ℝ) * |iteratedDeriv r f n| := by
  unfold vinogradovTaylorCoefficient
  rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ r.factorial)]
  ring

/-- Cardinality bound for the complete bilinear polynomial sum. -/
theorem norm_vinogradovBilinearPolynomialSum_le
    (c : ℕ → ℝ) (R V : ℕ) :
    ‖vinogradovBilinearPolynomialSum c R V‖ ≤ (((V ^ 2 : ℕ) : ℝ)) := by
  unfold vinogradovBilinearPolynomialSum
  calc
    ‖∑ x ∈ Finset.Icc 1 V, ∑ y ∈ Finset.Icc 1 V,
        standardAdditiveCharacter
          (∑ r ∈ Finset.range R, c (r + 1) * x ^ (r + 1) * y ^ (r + 1))‖ ≤
      ∑ x ∈ Finset.Icc 1 V,
        ‖∑ y ∈ Finset.Icc 1 V, standardAdditiveCharacter
          (∑ r ∈ Finset.range R,
            c (r + 1) * x ^ (r + 1) * y ^ (r + 1))‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ Finset.Icc 1 V, ∑ y ∈ Finset.Icc 1 V,
        ‖standardAdditiveCharacter
          (∑ r ∈ Finset.range R,
            c (r + 1) * x ^ (r + 1) * y ^ (r + 1))‖ := by
      apply Finset.sum_le_sum
      intro x hx
      exact norm_sum_le _ _
    _ = (((V ^ 2 : ℕ) : ℝ)) := by simp [pow_two]

/-- Removing the Taylor polynomial's constant term changes the complete local
product sum only by a unit complex factor. -/
theorem norm_vinogradovTaylorPolynomialLocalProductSum_eq_bilinearSum
    (f : ℝ → ℝ) (R n V : ℕ) :
    ‖vinogradovTaylorPolynomialLocalProductSum f R n V‖ =
      ‖vinogradovTaylorBilinearSum f R n V‖ := by
  have hterm : ∀ p ∈ vinogradovShiftPairs V,
      standardAdditiveCharacter
          (vinogradovTaylorPolynomial f R n ((p.1 * p.2 : ℕ) : ℝ)) =
        standardAdditiveCharacter (f n) * standardAdditiveCharacter
          (vinogradovTaylorBilinearPhase f R n p.1 p.2) := by
    intro p hp
    rw [vinogradovTaylorPolynomial_eq_constant_add_positive,
      standardAdditiveCharacter_add]
    congr 1
    rw [← vinogradovTaylorPositivePolynomial_mul]
    norm_num only [Nat.cast_mul]
  unfold vinogradovTaylorPolynomialLocalProductSum vinogradovTaylorBilinearSum
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  rw [norm_mul, norm_standardAdditiveCharacter, one_mul]
  exact congrArg norm (Finset.sum_product (Finset.Icc 1 V) (Finset.Icc 1 V)
    (fun p => standardAdditiveCharacter
      (vinogradovTaylorBilinearPhase f R n p.1 p.2)))

/-- Interior sum on which every product shift `xy ≤ V²` is available. -/
noncomputable def vinogradovTaylorPolynomialInteriorSum
    (f : ℝ → ℝ) (R a b V : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ico a (b - V ^ 2),
    vinogradovTaylorPolynomialLocalProductSum f R n V

/-- Dropping the varying constraints `n + xy < b` costs at most the product
multiset cardinality times the width `V²` of the right boundary strip. -/
theorem norm_vinogradovTaylorPolynomialPairSum_sub_interiorSum_le_of_span
    (f : ℝ → ℝ) (R a b V : ℕ) (hspan : a + V ^ 2 ≤ b) :
    ‖vinogradovTaylorPolynomialPairSum f R a b V -
        vinogradovTaylorPolynomialInteriorSum f R a b V‖ ≤
      (((V ^ 2 : ℕ) : ℝ)) * (((V ^ 2 : ℕ) : ℝ)) := by
  let g : (ℕ × ℕ) → ℕ → ℂ := fun p n =>
    standardAdditiveCharacter
      (vinogradovTaylorPolynomial f R n ((p.1 * p.2 : ℕ) : ℝ))
  have ha : a ≤ b - V ^ 2 := by omega
  have hsplit : ∀ p ∈ vinogradovShiftPairs V,
      ∑ n ∈ Finset.Ico a (b - p.1 * p.2), g p n =
        (∑ n ∈ Finset.Ico a (b - V ^ 2), g p n) +
          ∑ n ∈ Finset.Ico (b - V ^ 2) (b - p.1 * p.2), g p n := by
    intro p hp
    obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
    have hx := (Finset.mem_Icc.mp hp₁).2
    have hy := (Finset.mem_Icc.mp hp₂).2
    have hqV : p.1 * p.2 ≤ V ^ 2 := by
      rw [pow_two]
      exact Nat.mul_le_mul hx hy
    have hend : b - V ^ 2 ≤ b - p.1 * p.2 := Nat.sub_le_sub_left hqV b
    exact (Finset.sum_Ico_consecutive (g p) ha hend).symm
  have hrearrange :
      vinogradovTaylorPolynomialPairSum f R a b V =
        vinogradovTaylorPolynomialInteriorSum f R a b V +
          ∑ p ∈ vinogradovShiftPairs V,
            ∑ n ∈ Finset.Ico (b - V ^ 2) (b - p.1 * p.2), g p n := by
    unfold vinogradovTaylorPolynomialPairSum
    change (∑ p ∈ vinogradovShiftPairs V,
      ∑ n ∈ Finset.Ico a (b - p.1 * p.2), g p n) = _
    rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
    unfold vinogradovTaylorPolynomialInteriorSum
      vinogradovTaylorPolynomialLocalProductSum
    change (∑ p ∈ vinogradovShiftPairs V,
        ∑ n ∈ Finset.Ico a (b - V ^ 2), g p n) + _ = _
    rw [Finset.sum_comm]
  rw [hrearrange, add_sub_cancel_left]
  calc
    ‖∑ p ∈ vinogradovShiftPairs V,
        ∑ n ∈ Finset.Ico (b - V ^ 2) (b - p.1 * p.2), g p n‖ ≤
      ∑ p ∈ vinogradovShiftPairs V,
        ‖∑ n ∈ Finset.Ico (b - V ^ 2) (b - p.1 * p.2), g p n‖ :=
      norm_sum_le _ _
    _ ≤
      ∑ p ∈ vinogradovShiftPairs V,
        ∑ n ∈ Finset.Ico (b - V ^ 2) (b - p.1 * p.2), ‖g p n‖ := by
      apply Finset.sum_le_sum
      intro p hp
      exact norm_sum_le _ _
    _ = ∑ p ∈ vinogradovShiftPairs V,
        ((Finset.Ico (b - V ^ 2) (b - p.1 * p.2)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro p hp
      simp only [g, norm_standardAdditiveCharacter, Finset.sum_const,
        nsmul_eq_mul, mul_one]
    _ ≤ ∑ _p ∈ vinogradovShiftPairs V, (((V ^ 2 : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p hp
      simp only [Nat.card_Ico]
      exact_mod_cast (show (b - p.1 * p.2) - (b - V ^ 2) ≤ V ^ 2 by omega)
    _ = (((V ^ 2 : ℕ) : ℝ)) * (((V ^ 2 : ℕ) : ℝ)) := by
      rw [Finset.sum_const, nsmul_eq_mul, card_vinogradovShiftPairs]

/-- Endpoint removal for every interval.  If the interval is shorter than
`V²`, both the interior and the entire varying-support pair sum are covered by
the same `V⁴` trivial bound. -/
theorem norm_vinogradovTaylorPolynomialPairSum_sub_interiorSum_le
    (f : ℝ → ℝ) (R a b V : ℕ) :
    ‖vinogradovTaylorPolynomialPairSum f R a b V -
        vinogradovTaylorPolynomialInteriorSum f R a b V‖ ≤
      (((V ^ 2 : ℕ) : ℝ)) * (((V ^ 2 : ℕ) : ℝ)) := by
  by_cases hspan : a + V ^ 2 ≤ b
  · exact norm_vinogradovTaylorPolynomialPairSum_sub_interiorSum_le_of_span
      f R a b V hspan
  · have hempty : Finset.Ico a (b - V ^ 2) = ∅ := by
      apply Finset.Ico_eq_empty
      omega
    have hinterior : vinogradovTaylorPolynomialInteriorSum f R a b V = 0 := by
      unfold vinogradovTaylorPolynomialInteriorSum
      rw [hempty, Finset.sum_empty]
    rw [hinterior, sub_zero]
    unfold vinogradovTaylorPolynomialPairSum
    calc
      ‖∑ p ∈ vinogradovShiftPairs V,
          ∑ n ∈ Finset.Ico a (b - p.1 * p.2),
            standardAdditiveCharacter
              (vinogradovTaylorPolynomial f R n ((p.1 * p.2 : ℕ) : ℝ))‖ ≤
        ∑ p ∈ vinogradovShiftPairs V,
          ‖∑ n ∈ Finset.Ico a (b - p.1 * p.2),
            standardAdditiveCharacter
              (vinogradovTaylorPolynomial f R n ((p.1 * p.2 : ℕ) : ℝ))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ p ∈ vinogradovShiftPairs V,
          ∑ n ∈ Finset.Ico a (b - p.1 * p.2),
            ‖standardAdditiveCharacter
              (vinogradovTaylorPolynomial f R n ((p.1 * p.2 : ℕ) : ℝ))‖ := by
        apply Finset.sum_le_sum
        intro p hp
        exact norm_sum_le _ _
      _ = ∑ p ∈ vinogradovShiftPairs V,
          ((Finset.Ico a (b - p.1 * p.2)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp
      _ ≤ ∑ _p ∈ vinogradovShiftPairs V, (((V ^ 2 : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        simp only [Nat.card_Ico]
        exact_mod_cast (show (b - p.1 * p.2) - a ≤ V ^ 2 by omega)
      _ = (((V ^ 2 : ℕ) : ℝ)) * (((V ^ 2 : ℕ) : ℝ)) := by
        rw [Finset.sum_const, nsmul_eq_mul, card_vinogradovShiftPairs]

/-- Pointwise control of the complete local product sum controls its interior
aggregate with the exact number of base points. -/
theorem norm_vinogradovTaylorPolynomialInteriorSum_le_of_local
    (f : ℝ → ℝ) (R a b V : ℕ) {A : ℝ}
    (hlocal : ∀ n ∈ Finset.Ico a (b - V ^ 2),
      ‖vinogradovTaylorPolynomialLocalProductSum f R n V‖ ≤ A) :
    ‖vinogradovTaylorPolynomialInteriorSum f R a b V‖ ≤
      ((Finset.Ico a (b - V ^ 2)).card : ℝ) * A := by
  unfold vinogradovTaylorPolynomialInteriorSum
  calc
    ‖∑ n ∈ Finset.Ico a (b - V ^ 2),
        vinogradovTaylorPolynomialLocalProductSum f R n V‖ ≤
      ∑ n ∈ Finset.Ico a (b - V ^ 2),
        ‖vinogradovTaylorPolynomialLocalProductSum f R n V‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Ico a (b - V ^ 2), A := by
      apply Finset.sum_le_sum
      intro n hn
      exact hlocal n hn
    _ = ((Finset.Ico a (b - V ^ 2)).card : ℝ) * A := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Exact global consequence of a pointwise local-product estimate, including
the `V⁴` right-boundary contribution. -/
theorem norm_vinogradovTaylorPolynomialPairSum_le_of_local
    (f : ℝ → ℝ) (R a b V : ℕ) {A : ℝ}
    (hlocal : ∀ n ∈ Finset.Ico a (b - V ^ 2),
      ‖vinogradovTaylorPolynomialLocalProductSum f R n V‖ ≤ A) :
    ‖vinogradovTaylorPolynomialPairSum f R a b V‖ ≤
      (((V ^ 2 : ℕ) : ℝ)) * (((V ^ 2 : ℕ) : ℝ)) +
        ((Finset.Ico a (b - V ^ 2)).card : ℝ) * A := by
  have hboundary :=
    norm_vinogradovTaylorPolynomialPairSum_sub_interiorSum_le f R a b V
  have hinterior :=
    norm_vinogradovTaylorPolynomialInteriorSum_le_of_local f R a b V hlocal
  calc
    ‖vinogradovTaylorPolynomialPairSum f R a b V‖ =
        ‖(vinogradovTaylorPolynomialPairSum f R a b V -
            vinogradovTaylorPolynomialInteriorSum f R a b V) +
          vinogradovTaylorPolynomialInteriorSum f R a b V‖ := by
      congr 1
      abel
    _ ≤ ‖vinogradovTaylorPolynomialPairSum f R a b V -
          vinogradovTaylorPolynomialInteriorSum f R a b V‖ +
        ‖vinogradovTaylorPolynomialInteriorSum f R a b V‖ := norm_add_le _ _
    _ ≤ (((V ^ 2 : ℕ) : ℝ)) * (((V ^ 2 : ℕ) : ℝ)) +
        ((Finset.Ico a (b - V ^ 2)).card : ℝ) * A :=
      add_le_add hboundary hinterior

/-- Boundary plus Taylor error contributed by one product shift. -/
noncomputable def vinogradovTaylorShiftError
    (X F α : ℝ) (a b : ℕ) (p : ℕ × ℕ) : ℝ :=
  ((p.1 * p.2 : ℕ) : ℝ) +
    2 * Real.pi * ((Finset.Ico a (b - p.1 * p.2)).card : ℝ) *
      ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
        (((p.1 * p.2 : ℕ) : ℝ) / X) ^ (vinogradovDerivativeCutoff X F))

/-- Uniform version of the boundary-plus-Taylor error over all product shifts
`xy` with `1 ≤ x,y ≤ V`. -/
noncomputable def vinogradovTaylorShiftErrorEnvelope
    (X F α : ℝ) (a b V : ℕ) : ℝ :=
  ((V ^ 2 : ℕ) : ℝ) +
    2 * Real.pi * ((b - a : ℕ) : ℝ) *
      ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
        (((V ^ 2 : ℕ) : ℝ) / X) ^ (vinogradovDerivativeCutoff X F))

/-- The source choice `V = X^(1/4)`, rounded down to a natural number. -/
noncomputable def vinogradovAveragingRange (X : ℝ) : ℕ :=
  ⌊Real.sqrt (Real.sqrt X)⌋₊

theorem vinogradovAveragingRange_pos {X : ℝ} (hX : 1 ≤ X) :
    0 < vinogradovAveragingRange X := by
  rw [vinogradovAveragingRange, Nat.floor_pos]
  apply Real.one_le_sqrt.mpr
  apply Real.one_le_sqrt.mpr
  exact hX

theorem vinogradovAveragingRange_sq_le_sqrt (X : ℝ) :
    (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) ≤ Real.sqrt X := by
  have hfloor : ((vinogradovAveragingRange X : ℕ) : ℝ) ≤
      Real.sqrt (Real.sqrt X) := by
    exact Nat.floor_le (Real.sqrt_nonneg _)
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ _) hfloor 2
  rw [Real.sq_sqrt (Real.sqrt_nonneg X)] at hp
  norm_num only [Nat.cast_pow]
  exact hp

/-- Once `X ≥ 16`, floor rounding loses less than a factor two from the source
choice `X^(1/4)`. -/
theorem half_sqrt_sqrt_lt_vinogradovAveragingRange
    {X : ℝ} (hX : 16 ≤ X) :
    Real.sqrt (Real.sqrt X) / 2 < (vinogradovAveragingRange X : ℝ) := by
  let y := Real.sqrt (Real.sqrt X)
  let V := vinogradovAveragingRange X
  have hsqrt : 4 ≤ Real.sqrt X := by
    have := Real.sqrt_le_sqrt hX
    norm_num at this ⊢
    exact this
  have hy : 2 ≤ y := by
    have := Real.sqrt_le_sqrt hsqrt
    norm_num at this
    exact this
  have hV : 1 ≤ V := by
    have hfloorpos : 0 < Nat.floor y := Nat.floor_pos.mpr (by linarith : 1 ≤ y)
    change 1 ≤ Nat.floor y
    omega
  have hfloor := Nat.lt_floor_add_one y
  have hfloor' : y < (V : ℝ) + 1 := by
    simpa only [V, vinogradovAveragingRange, Nat.cast_add, Nat.cast_one] using hfloor
  have hVreal : 1 ≤ (V : ℝ) := by exact_mod_cast hV
  dsimp only [y] at hfloor' ⊢
  dsimp only [V] at hVreal hfloor'
  linarith

/-- Logarithmic comparison between the floor-rounded averaging range and the
ideal value `X^(1/4)`. -/
theorem log_vinogradovAveragingRange_bounds
    {X : ℝ} (hX : 16 ≤ X) :
    Real.log X / 4 - Real.log 2 <
        Real.log (vinogradovAveragingRange X : ℝ) ∧
      Real.log (vinogradovAveragingRange X : ℝ) ≤ Real.log X / 4 := by
  let y := Real.sqrt (Real.sqrt X)
  let V := vinogradovAveragingRange X
  have hXpos : 0 < X := by linarith
  have hypos : 0 < y := by dsimp only [y]; positivity
  have hhalf : y / 2 < (V : ℝ) := by
    simpa only [y, V] using half_sqrt_sqrt_lt_vinogradovAveragingRange hX
  have hVpos : 0 < (V : ℝ) := (div_pos hypos (by norm_num)).trans hhalf
  have hVle : (V : ℝ) ≤ y := by
    dsimp only [V, vinogradovAveragingRange, y]
    exact Nat.floor_le (Real.sqrt_nonneg _)
  have hlogY : Real.log y = Real.log X / 4 := by
    dsimp only [y]
    rw [Real.log_sqrt (Real.sqrt_nonneg X), Real.log_sqrt hXpos.le]
    ring
  constructor
  · have hlog := Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (div_pos hypos (by norm_num)))
      (Set.mem_Ioi.mpr hVpos) hhalf
    rw [Real.log_div (ne_of_gt hypos) (by norm_num), hlogY] at hlog
    exact hlog
  · have hlog := Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hVpos) (Set.mem_Ioi.mpr hypos) hVle
    simpa only [hlogY] using hlog

/-- Before the numerical smallness condition is used, the canonical
fourth-root averaging range reduces the Taylor envelope to the two terms in
the source display: `√X` and the normalized top-derivative remainder. -/
theorem vinogradovTaylorShiftErrorEnvelope_averagingRange_le
    {X F α : ℝ} {a b : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hlength : ((b - a : ℕ) : ℝ) ≤ X) :
    vinogradovTaylorShiftErrorEnvelope X F α a b
        (vinogradovAveragingRange X) ≤
      Real.sqrt X + 2 * Real.pi * X *
        ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
          (Real.sqrt X / X) ^ (vinogradovDerivativeCutoff X F)) := by
  have hXpos : 0 < X := by linarith
  have hF : 0 ≤ F := (by positivity : 0 ≤ X ^ 4).trans hFhigh
  have hB : 0 ≤ α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F :=
    mul_nonneg (pow_nonneg (by linarith) _) hF
  have hV := vinogradovAveragingRange_sq_le_sqrt X
  have hratio :
      (((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) / X ≤
        Real.sqrt X / X := by
    exact (div_le_div_iff_of_pos_right hXpos).2 hV
  unfold vinogradovTaylorShiftErrorEnvelope
  apply add_le_add hV
  gcongr

/-- Algebraic factorization used in the source's estimate of the Taylor
remainder after choosing `V = X^(1/4)`. -/
theorem vinogradovTaylorRemainder_factorization
    {X α F : ℝ} {R : ℕ} (hX : 0 < X) :
    X * (α ^ (R ^ 3) * F) * (Real.sqrt X / X) ^ R =
      (X ^ (-(R : ℝ) / 4) * α ^ (R ^ 3)) *
        (F * X ^ (1 - (R : ℝ) / 4)) := by
  have hbase : Real.sqrt X / X = X ^ (-1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    calc
      X ^ (1 / (2 : ℝ)) / X = X ^ (1 / (2 : ℝ)) / X ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = X ^ (1 / (2 : ℝ) - 1) := Real.rpow_sub hX _ _ |>.symm
      _ = X ^ (-1 / 2 : ℝ) := by
        congr 1
        ring
  have hpow : (X ^ (-1 / 2 : ℝ)) ^ R =
      X ^ ((-1 / 2 : ℝ) * (R : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX.le]
  have hxid : X * X ^ ((-1 / 2 : ℝ) * (R : ℝ)) =
      X ^ (-(R : ℝ) / 4) * X ^ (1 - (R : ℝ) / 4) := by
    calc
      X * X ^ ((-1 / 2 : ℝ) * (R : ℝ)) =
          X ^ (1 : ℝ) * X ^ ((-1 / 2 : ℝ) * (R : ℝ)) := by
        rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + (-1 / 2 : ℝ) * (R : ℝ)) :=
        (Real.rpow_add hX _ _).symm
      _ = X ^ (-(R : ℝ) / 4 + (1 - (R : ℝ) / 4)) := by
        congr 1
        ring
      _ = X ^ (-(R : ℝ) / 4) * X ^ (1 - (R : ℝ) / 4) :=
        Real.rpow_add hX _ _
  rw [hbase, hpow]
  calc
    X * (α ^ (R ^ 3) * F) * X ^ ((-1 / 2 : ℝ) * (R : ℝ)) =
        (X * X ^ ((-1 / 2 : ℝ) * (R : ℝ))) *
          (α ^ (R ^ 3) * F) := by ring
    _ = (X ^ (-(R : ℝ) / 4) * X ^ (1 - (R : ℝ) / 4)) *
        (α ^ (R ^ 3) * F) := by rw [hxid]
    _ = (X ^ (-(R : ℝ) / 4) * α ^ (R ^ 3)) *
        (F * X ^ (1 - (R : ℝ) / 4)) := by ring

/-- The factor in parentheses in the pinned source is at most one.  This uses
only `F ≥ X⁴` and the literal cutoff `10⌈log F / log X⌉ + 1`. -/
theorem vinogradovSecondSourceFactor_le_one
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    F * X ^ (1 - (vinogradovDerivativeCutoff X F : ℝ) / 4) ≤ 1 := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hlogF : 0 ≤ Real.log F := Real.log_nonneg (by
    calc
      1 = (1 : ℝ) ^ 4 := by norm_num
      _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
      _ ≤ F := hFhigh)
  have hlogHigh : 4 * Real.log X ≤ Real.log F := by
    calc
      4 * Real.log X = Real.log (X ^ 4) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  let u := Real.log F / Real.log X
  have hu : 4 ≤ u := by
    dsimp only [u]
    rw [le_div_iff₀ hlogX]
    exact hlogHigh
  have hceil : u ≤ (⌈u⌉₊ : ℝ) := Nat.le_ceil u
  have hcutoff : 10 * u + 1 ≤ (vinogradovDerivativeCutoff X F : ℝ) := by
    unfold vinogradovDerivativeCutoff
    push_cast
    dsimp only [u] at hceil ⊢
    linarith
  have hratio : u ≤ (vinogradovDerivativeCutoff X F : ℝ) / 4 - 1 := by
    linarith
  have hlogIdentity : Real.log F = u * Real.log X := by
    dsimp only [u]
    field_simp
  have hlogBound : Real.log F ≤
      ((vinogradovDerivativeCutoff X F : ℝ) / 4 - 1) * Real.log X := by
    rw [hlogIdentity]
    exact mul_le_mul_of_nonneg_right hratio hlogX.le
  have hFpow : F ≤
      X ^ ((vinogradovDerivativeCutoff X F : ℝ) / 4 - 1) :=
    Real.le_rpow_of_log_le hXpos hlogBound
  calc
    F * X ^ (1 - (vinogradovDerivativeCutoff X F : ℝ) / 4) ≤
        X ^ ((vinogradovDerivativeCutoff X F : ℝ) / 4 - 1) *
          X ^ (1 - (vinogradovDerivativeCutoff X F : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hFpow (Real.rpow_nonneg hXpos.le _)
    _ = X ^ (((vinogradovDerivativeCutoff X F : ℝ) / 4 - 1) +
          (1 - (vinogradovDerivativeCutoff X F : ℝ) / 4)) :=
      (Real.rpow_add hXpos _ _).symm
    _ = 1 := by norm_num

/-- Vinogradov's numerical `10⁻³` condition controls the first factor in the
source Taylor-error display.  The constants use the literal cutoff and the
consequence `log F / log X ≥ 4` of `F ≥ X⁴`. -/
theorem vinogradovFirstSourceFactor_le_one
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3 < 1 / 1000) :
    X ^ (-(vinogradovDerivativeCutoff X F : ℝ) / 4) *
        α ^ ((vinogradovDerivativeCutoff X F) ^ 3) ≤ 1 := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hFone : 1 ≤ F := by
    calc
      1 = (1 : ℝ) ^ 4 := by norm_num
      _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) (by linarith) 4
      _ ≤ F := hFhigh
  have hXfour : (1 : ℝ) < X ^ 4 := by
    calc
      1 < (2 : ℝ) ^ 4 := by norm_num
      _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX 4
  have hlogF : 0 < Real.log F := Real.log_pos (hXfour.trans_le hFhigh)
  have hlogAlpha : 0 ≤ Real.log α := Real.log_nonneg hα
  let s := Real.log F / Real.log X
  let R : ℝ := vinogradovDerivativeCutoff X F
  have hs : 4 ≤ s := by
    dsimp only [s]
    rw [le_div_iff₀ hlogX]
    calc
      4 * Real.log X = Real.log (X ^ 4) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  have hRlower : 10 * s + 1 ≤ R := by
    have hceil : s ≤ (⌈s⌉₊ : ℝ) := Nat.le_ceil s
    dsimp only [R]
    unfold vinogradovDerivativeCutoff
    push_cast
    linarith
  have hRupper : R < 13 * s := by
    have hcut := vinogradovDerivativeCutoff_cast_lt (by linarith : 1 < X) hFone
    dsimp only [R, s]
    dsimp only [s] at hs
    linarith
  have hRnonneg : 0 ≤ R := by positivity
  have hsnonneg : 0 ≤ s := by linarith
  have hcube : R ^ 3 ≤ (13 * s) ^ 3 :=
    pow_le_pow_left₀ hRnonneg hRupper.le 3
  have hlogBound : R ^ 3 * Real.log α ≤ R / 4 * Real.log X := by
    have hmul : R ^ 3 * Real.log α ≤ (13 * s) ^ 3 * Real.log α :=
      mul_le_mul_of_nonneg_right hcube hlogAlpha
    have hidentity : (13 * s) ^ 3 * Real.log α =
        2197 * (Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3) *
          Real.log F := by
      dsimp only [s]
      field_simp
      ring
    have hsmallMul :
        2197 * (Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3) *
            Real.log F <
          2197 * (1 / 1000 : ℝ) * Real.log F := by
      gcongr
    have htwoHalf :
        2197 * (1 / 1000 : ℝ) * Real.log F <
          (5 / 2 : ℝ) * Real.log F := by
      nlinarith
    have htarget : (5 / 2 : ℝ) * Real.log F < R / 4 * Real.log X := by
      have hsIdentity : s * Real.log X = Real.log F := by
        dsimp only [s]
        field_simp
      nlinarith
    exact (hmul.trans_lt (by rw [hidentity]; exact hsmallMul.trans htwoHalf)).trans
      htarget |>.le
  have hpow : α ^ ((vinogradovDerivativeCutoff X F) ^ 3) ≤
      X ^ (R / 4) := by
    apply Real.le_rpow_of_log_le hXpos
    rw [Real.log_pow]
    norm_num only [Nat.cast_pow]
    simpa only [R] using hlogBound
  calc
    X ^ (-(vinogradovDerivativeCutoff X F : ℝ) / 4) *
        α ^ ((vinogradovDerivativeCutoff X F) ^ 3) ≤
      X ^ (-R / 4) * X ^ (R / 4) :=
        mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hXpos.le _)
    _ = X ^ (-R / 4 + R / 4) := (Real.rpow_add hXpos _ _).symm
    _ = 1 := by
      rw [show -R / 4 + R / 4 = 0 by ring, Real.rpow_zero]

/-- The two factors displayed in the pinned source each being at most one
implies that the normalized Taylor remainder is at most one. -/
theorem vinogradovTaylorRemainder_le_one_of_sourceFactors
    {X α F : ℝ} {R : ℕ} (hX : 0 < X) (hF : 0 ≤ F)
    (hfirst : X ^ (-(R : ℝ) / 4) * α ^ (R ^ 3) ≤ 1)
    (hsecond : F * X ^ (1 - (R : ℝ) / 4) ≤ 1) :
    X * (α ^ (R ^ 3) * F) * (Real.sqrt X / X) ^ R ≤ 1 := by
  rw [vinogradovTaylorRemainder_factorization hX]
  have hmul := mul_le_mul hfirst hsecond
    (mul_nonneg hF (Real.rpow_nonneg hX.le _)) (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [mul_one] using hmul

/-- With the two source factors discharged, the complete canonical Taylor
envelope is at most `√X + 2π`. -/
theorem vinogradovTaylorShiftErrorEnvelope_averagingRange_le_sqrt_add_two_pi
    {X F α : ℝ} {a b : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hlength : ((b - a : ℕ) : ℝ) ≤ X)
    (hfirst : X ^ (-(vinogradovDerivativeCutoff X F : ℝ) / 4) *
        α ^ ((vinogradovDerivativeCutoff X F) ^ 3) ≤ 1)
    (hsecond : F * X ^
        (1 - (vinogradovDerivativeCutoff X F : ℝ) / 4) ≤ 1) :
    vinogradovTaylorShiftErrorEnvelope X F α a b
        (vinogradovAveragingRange X) ≤ Real.sqrt X + 2 * Real.pi := by
  have hXpos : 0 < X := by linarith
  have hF : 0 ≤ F := (by positivity : 0 ≤ X ^ 4).trans hFhigh
  have htail := vinogradovTaylorRemainder_le_one_of_sourceFactors
    hXpos hF hfirst hsecond
  have htwoPi : 0 ≤ 2 * Real.pi := by positivity
  calc
    vinogradovTaylorShiftErrorEnvelope X F α a b
        (vinogradovAveragingRange X) ≤
      Real.sqrt X + 2 * Real.pi * X *
        ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
          (Real.sqrt X / X) ^ (vinogradovDerivativeCutoff X F)) :=
      vinogradovTaylorShiftErrorEnvelope_averagingRange_le
        hX hFhigh hα hlength
    _ = Real.sqrt X + (2 * Real.pi) *
        (X * (α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
          (Real.sqrt X / X) ^ (vinogradovDerivativeCutoff X F)) := by ring
    _ ≤ Real.sqrt X + (2 * Real.pi) * 1 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left htail htwoPi)
    _ = Real.sqrt X + 2 * Real.pi := by ring

/-- Complete discharge of the source Taylor error from the hypotheses of
Vinogradov's proposition. -/
theorem vinogradovTaylorShiftErrorEnvelope_averagingRange_le_source
    {X F α : ℝ} {a b : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hlength : ((b - a : ℕ) : ℝ) ≤ X)
    (hsmall : Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3 < 1 / 1000) :
    vinogradovTaylorShiftErrorEnvelope X F α a b
        (vinogradovAveragingRange X) ≤ Real.sqrt X + 2 * Real.pi := by
  exact vinogradovTaylorShiftErrorEnvelope_averagingRange_le_sqrt_add_two_pi
    hX hFhigh hα hlength
      (vinogradovFirstSourceFactor_le_one hX hFhigh hα hsmall)
      (vinogradovSecondSourceFactor_le_one hX hFhigh)

/-- The source's `O(√X)` Taylor loss is absorbed by nine copies of the stated
Vinogradov main scale.  This uses only `F ≥ X⁴`; the main exponential can lose
far less than a square root at the smallest permitted `F`. -/
theorem sqrt_add_two_pi_le_nine_mul_vinogradovScale
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α) :
    Real.sqrt X + 2 * Real.pi ≤
      9 * (α * X * Real.exp
        (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
          (Real.log F) ^ 2)) := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hlogF : 0 < Real.log F := by
    apply Real.log_pos
    calc
      1 < (2 : ℝ) ^ 4 := by norm_num
      _ ≤ X ^ 4 := pow_le_pow_left₀ (by norm_num) hX 4
      _ ≤ F := hFhigh
  have hlogHigh : 4 * Real.log X ≤ Real.log F := by
    calc
      4 * Real.log X = Real.log (X ^ 4) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  have hlogSquare : 16 * (Real.log X) ^ 2 ≤ (Real.log F) ^ 2 := by
    have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ 4 * Real.log X)
      hlogHigh 2
    nlinarith
  have hratio : (Real.log X) ^ 3 / (Real.log F) ^ 2 ≤
      Real.log X / 16 := by
    rw [div_le_iff₀ (sq_pos_of_pos hlogF)]
    nlinarith [mul_le_mul_of_nonneg_left hlogSquare hlogX.le]
  have hc : 0 ≤ (2 : ℝ) ^ (-18 : ℝ) := Real.rpow_nonneg (by norm_num) _
  have hcOne : (2 : ℝ) ^ (-18 : ℝ) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by norm_num)
  have hdecay : (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
      (Real.log F) ^ 2 ≤ Real.log X / 2 := by
    calc
      (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
          (Real.log F) ^ 2 =
        (2 : ℝ) ^ (-18 : ℝ) *
          ((Real.log X) ^ 3 / (Real.log F) ^ 2) := by ring
      _ ≤ (2 : ℝ) ^ (-18 : ℝ) * (Real.log X / 16) :=
        mul_le_mul_of_nonneg_left hratio hc
      _ ≤ 1 * (Real.log X / 16) :=
        mul_le_mul_of_nonneg_right hcOne (by positivity)
      _ ≤ Real.log X / 2 := by linarith
  have hexp : X ^ (-1 / 2 : ℝ) ≤ Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) := by
    rw [Real.rpow_def_of_pos hXpos, Real.exp_le_exp]
    calc
      Real.log X * (-1 / 2 : ℝ) = -(Real.log X / 2) := by ring
      _ ≤ -((2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
          (Real.log F) ^ 2) := neg_le_neg hdecay
      _ = -((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
          (Real.log F) ^ 2 := by ring
  have hsqrtIdentity : X * X ^ (-1 / 2 : ℝ) = Real.sqrt X := by
    rw [Real.sqrt_eq_rpow]
    calc
      X * X ^ (-1 / 2 : ℝ) = X ^ (1 : ℝ) * X ^ (-1 / 2 : ℝ) := by
        rw [Real.rpow_one]
      _ = X ^ ((1 : ℝ) + (-1 / 2 : ℝ)) := (Real.rpow_add hXpos _ _).symm
      _ = X ^ (1 / 2 : ℝ) := by congr 1; ring
  have hsqrtMain : Real.sqrt X ≤ α * X * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) := by
    rw [← hsqrtIdentity]
    have hXexp := mul_le_mul_of_nonneg_left hexp hXpos.le
    calc
      X * X ^ (-1 / 2 : ℝ) ≤ X * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2) := hXexp
      _ ≤ α * X * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2) := by
        have hexp0 : 0 ≤ Real.exp
            (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
              (Real.log F) ^ 2) := Real.exp_pos _ |>.le
        calc
          X * Real.exp
              (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
                (Real.log F) ^ 2) =
            1 * (X * Real.exp
              (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
                (Real.log F) ^ 2)) := by ring
          _ ≤ α * (X * Real.exp
              (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
                (Real.log F) ^ 2)) :=
            mul_le_mul_of_nonneg_right hα (mul_nonneg hXpos.le hexp0)
          _ = α * X * Real.exp
              (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
                (Real.log F) ^ 2) := by ring
  have hsqrtOne : 1 ≤ Real.sqrt X := Real.one_le_sqrt.mpr (by linarith)
  have hpi : 2 * Real.pi ≤ 8 * Real.sqrt X := by
    have := Real.pi_lt_four
    nlinarith
  nlinarith

/-- The total Taylor error over the product multiset is its cardinality
`V²` times the uniform shift envelope. -/
theorem sum_vinogradovTaylorShiftError_le_envelope
    {X F α : ℝ} {a b V : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α) :
    ∑ p ∈ vinogradovShiftPairs V, vinogradovTaylorShiftError X F α a b p ≤
      ((V ^ 2 : ℕ) : ℝ) *
        vinogradovTaylorShiftErrorEnvelope X F α a b V := by
  have hF : 0 ≤ F := (by positivity : 0 ≤ X ^ 4).trans hFhigh
  have hB : 0 ≤ α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F :=
    mul_nonneg (pow_nonneg (by linarith) _) hF
  calc
    ∑ p ∈ vinogradovShiftPairs V, vinogradovTaylorShiftError X F α a b p ≤
        ∑ _p ∈ vinogradovShiftPairs V,
          vinogradovTaylorShiftErrorEnvelope X F α a b V := by
      apply Finset.sum_le_sum
      intro p hp
      obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
      have hx := Finset.mem_Icc.mp hp₁
      have hy := Finset.mem_Icc.mp hp₂
      have hqV : p.1 * p.2 ≤ V ^ 2 := by
        rw [pow_two]
        exact Nat.mul_le_mul hx.2 hy.2
      have hcard : (Finset.Ico a (b - p.1 * p.2)).card ≤ b - a := by
        simp only [Nat.card_Ico]
        omega
      unfold vinogradovTaylorShiftError vinogradovTaylorShiftErrorEnvelope
      apply add_le_add
      · exact_mod_cast hqV
      · gcongr
    _ = ((V ^ 2 : ℕ) : ℝ) *
        vinogradovTaylorShiftErrorEnvelope X F α a b V := by
      rw [Finset.sum_const, nsmul_eq_mul, card_vinogradovShiftPairs]

/-- Exact product-multiset averaging form of the source Taylor reduction.
Every occurrence of a product `xy` is retained separately. -/
theorem norm_vinogradovShiftPairs_nsmul_sum_sub_taylorPolynomialPairSum_le
    {f : ℝ → ℝ} {X F α : ℝ} {a b V : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hXa : X ≤ (a : ℝ))
    (hsmooth : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F) :
    ‖(V ^ 2) • (∑ n ∈ Finset.Ico a b,
          standardAdditiveCharacter (f n)) -
        vinogradovTaylorPolynomialPairSum f
          (vinogradovTaylorDegree X F) a b V‖ ≤
      ∑ p ∈ vinogradovShiftPairs V,
        vinogradovTaylorShiftError X F α a b p := by
  rw [← card_vinogradovShiftPairs V]
  unfold vinogradovTaylorPolynomialPairSum
  refine (norm_card_nsmul_sub_sum_le_sum_norm_sub
    (vinogradovShiftPairs V)
    (∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n))
    (fun p => ∑ n ∈ Finset.Ico a (b - p.1 * p.2),
      standardAdditiveCharacter
        (vinogradovTaylorPolynomial f (vinogradovTaylorDegree X F) n
          ((p.1 * p.2 : ℕ) : ℝ)))).trans ?_
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨hp₁, hp₂⟩ := Finset.mem_product.mp hp
  have hx := Finset.mem_Icc.mp hp₁
  have hy := Finset.mem_Icc.mp hp₂
  have hq : 0 < p.1 * p.2 := Nat.mul_pos hx.1 hy.1
  simpa only [vinogradovTaylorShiftError] using
    (norm_sum_Ico_standardAdditiveCharacter_sub_vinogradovTaylorPolynomial_le
      hX hFhigh hα hq hXa hsmooth hderiv)

/-- Divide an unnormalized `V²`-term average after bounding both its
approximation error and its main term. -/
theorem norm_le_of_square_nsmul_sub_le_and_norm_le
    {V : ℕ} (hV : 1 ≤ V) {z w : ℂ} {E A : ℝ}
    (herror : ‖(V ^ 2) • z - w‖ ≤ ((V ^ 2 : ℕ) : ℝ) * E)
    (hmain : ‖w‖ ≤ ((V ^ 2 : ℕ) : ℝ) * A) :
    ‖z‖ ≤ E + A := by
  have hVpos : 0 < ((V ^ 2 : ℕ) : ℝ) := by
    positivity
  have havg : ‖(V ^ 2) • z‖ ≤ ((V ^ 2 : ℕ) : ℝ) * (E + A) := by
    calc
      ‖(V ^ 2) • z‖ = ‖((V ^ 2) • z - w) + w‖ := by
        congr 1
        abel
      _ ≤ ‖(V ^ 2) • z - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ ((V ^ 2 : ℕ) : ℝ) * E + ((V ^ 2 : ℕ) : ℝ) * A :=
        add_le_add herror hmain
      _ = ((V ^ 2 : ℕ) : ℝ) * (E + A) := by ring
  rw [RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul] at havg
  exact (mul_le_mul_iff_of_pos_left hVpos).mp havg

/-- The exact Taylor/product-shift reduction: any estimate for the resulting
polynomial pair sum transfers to the original exponential sum, with the
explicit boundary-and-Taylor envelope added.  The subsequent polynomial
mean-value estimate is the remaining Iwaniec--Kowalski stage. -/
theorem norm_sum_Ico_standardAdditiveCharacter_le_of_taylorPolynomialPairSum
    {f : ℝ → ℝ} {X F α : ℝ} {a b V : ℕ} {A : ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hV : 1 ≤ V) (hXa : X ≤ (a : ℝ))
    (hsmooth : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F)
    (hpoly : ‖vinogradovTaylorPolynomialPairSum f
        (vinogradovTaylorDegree X F) a b V‖ ≤ ((V ^ 2 : ℕ) : ℝ) * A) :
    ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
      vinogradovTaylorShiftErrorEnvelope X F α a b V + A := by
  apply norm_le_of_square_nsmul_sub_le_and_norm_le hV
  · exact
      (norm_vinogradovShiftPairs_nsmul_sum_sub_taylorPolynomialPairSum_le
        hX hFhigh hα hXa hsmooth hderiv).trans
        (sum_vinogradovTaylorShiftError_le_envelope hX hFhigh hα)
  · exact hpoly

/-- Source-specialized form at `V = ⌊X^(1/4)⌋`: after the exact averaging
reduction, only the Taylor-polynomial pair-sum estimate and the displayed
top-derivative remainder remain. -/
theorem norm_sum_Ico_standardAdditiveCharacter_le_of_averagingRange_pairSum
    {f : ℝ → ℝ} {X F α : ℝ} {a b : ℕ} {A : ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hXa : X ≤ (a : ℝ)) (hlength : ((b - a : ℕ) : ℝ) ≤ X)
    (hsmooth : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F)
    (hpoly : ‖vinogradovTaylorPolynomialPairSum f
        (vinogradovTaylorDegree X F) a b (vinogradovAveragingRange X)‖ ≤
      ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) * A)) :
    ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
      Real.sqrt X + 2 * Real.pi * X *
        ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
          (Real.sqrt X / X) ^ (vinogradovDerivativeCutoff X F)) + A := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have htransfer :=
    norm_sum_Ico_standardAdditiveCharacter_le_of_taylorPolynomialPairSum
      hX hFhigh hα hV hXa hsmooth hderiv hpoly
  have henvelope := vinogradovTaylorShiftErrorEnvelope_averagingRange_le
    hX hFhigh hα hlength
  calc
    ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
        vinogradovTaylorShiftErrorEnvelope X F α a b
          (vinogradovAveragingRange X) + A := htransfer
    _ ≤ (Real.sqrt X + 2 * Real.pi * X *
          ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
            (Real.sqrt X / X) ^ (vinogradovDerivativeCutoff X F))) + A :=
      add_le_add henvelope le_rfl
    _ = Real.sqrt X + 2 * Real.pi * X *
          ((α ^ ((vinogradovDerivativeCutoff X F) ^ 3) * F) *
            (Real.sqrt X / X) ^ (vinogradovDerivativeCutoff X F)) + A := rfl

/-- Under Vinogradov's numerical condition, a normalized estimate for the
polynomial pair sum transfers to the original sum with only `√X + 2π` Taylor
loss.  This is the complete formal version of the Taylor-error paragraph in
the pinned proof. -/
theorem norm_sum_Ico_standardAdditiveCharacter_le_of_source_pairSum
    {f : ℝ → ℝ} {X F α : ℝ} {a b : ℕ} {A : ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3 < 1 / 1000)
    (hXa : X ≤ (a : ℝ)) (hlength : ((b - a : ℕ) : ℝ) ≤ X)
    (hsmooth : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F)
    (hpoly : ‖vinogradovTaylorPolynomialPairSum f
        (vinogradovTaylorDegree X F) a b (vinogradovAveragingRange X)‖ ≤
      ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) * A)) :
    ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
      Real.sqrt X + 2 * Real.pi + A := by
  have hV : 1 ≤ vinogradovAveragingRange X :=
    vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have htransfer :=
    norm_sum_Ico_standardAdditiveCharacter_le_of_taylorPolynomialPairSum
      hX hFhigh hα hV hXa hsmooth hderiv hpoly
  have henvelope := vinogradovTaylorShiftErrorEnvelope_averagingRange_le_source
    hX hFhigh hα hlength hsmall
  exact htransfer.trans (add_le_add henvelope le_rfl)

/-- Contract-shaped Taylor reduction for an arbitrary integer interval inside
`[X,2X]`.  The endpoint and length hypotheses required by the preceding
theorem are derived internally; empty intervals are handled directly. -/
theorem norm_sum_Ico_standardAdditiveCharacter_le_of_source_pairSum_of_subset
    {f : ℝ → ℝ} {X F α : ℝ} {a b : ℕ} {A : ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : Real.log α * (Real.log F) ^ 2 / (Real.log X) ^ 3 < 1 / 1000)
    (hI : Set.Icc (a : ℝ) (b : ℝ) ⊆ Set.Icc X (2 * X))
    (hsmooth : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ContDiffAt ℝ ∞ f t)
    (hderiv : ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F)
    (hpoly : ‖vinogradovTaylorPolynomialPairSum f
        (vinogradovTaylorDegree X F) a b (vinogradovAveragingRange X)‖ ≤
      ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) * A)) :
    ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
      Real.sqrt X + 2 * Real.pi + A := by
  by_cases hab : a < b
  · have habReal : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab.le
    have hXa : X ≤ (a : ℝ) :=
      (hI ⟨le_rfl, habReal⟩).1
    have hbX : (b : ℝ) ≤ 2 * X :=
      (hI ⟨habReal, le_rfl⟩).2
    have hlength : ((b - a : ℕ) : ℝ) ≤ X := by
      rw [Nat.cast_sub hab.le]
      linarith
    exact norm_sum_Ico_standardAdditiveCharacter_le_of_source_pairSum
      hX hFhigh hα hsmall hXa hlength hsmooth hderiv hpoly
  · rw [Finset.Ico_eq_empty hab, Finset.sum_empty, norm_zero]
    have hsqrt : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
    have hpi : 0 < Real.pi := Real.pi_pos
    have hAnorm : 0 ≤ A := by
      have := norm_nonneg (vinogradovTaylorPolynomialPairSum f
        (vinogradovTaylorDegree X F) a b (vinogradovAveragingRange X))
      have hVpos : 0 < ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ)) := by
        have := vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
        positivity
      nlinarith
    positivity

/-- Coefficient-only bilinear estimate after Taylor expansion. This is the
pure polynomial statement to which the Iwaniec--Kowalski mean-value argument
applies. -/
def VinogradovBilinearPolynomialEstimateAt (C : ℝ) : Prop :=
  0 < C ∧ ∀ (X F α : ℝ) (n : ℕ) (c : ℕ → ℝ),
    2 ≤ X → X ^ 4 ≤ F → 1 ≤ α →
    (n : ℝ) ∈ Set.Icc X (2 * X) →
    (∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F) →
    ‖vinogradovBilinearPolynomialSum c (vinogradovTaylorDegree X F)
        (vinogradovAveragingRange X)‖ ≤
      ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        (C * α * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)))

/-- Nontrivial branch of the coefficient-only bilinear estimate. When the
requested normalized majorant is at least one, the cardinality bound already
proves the result. -/
def VinogradovBilinearPolynomialNontrivialEstimateAt (C : ℝ) : Prop :=
  1 ≤ C ∧ ∀ (X F α : ℝ) (n : ℕ) (c : ℕ → ℝ),
    2 ≤ X → X ^ 4 ≤ F → 1 ≤ α →
    (n : ℝ) ∈ Set.Icc X (2 * X) →
    (∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F) →
    C * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1 →
    ‖vinogradovBilinearPolynomialSum c (vinogradovTaylorDegree X F)
        (vinogradovAveragingRange X)‖ ≤
      ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        (C * α * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)))

/-- In the genuinely nontrivial branch, `α` is automatically smaller than
the exponential decay it accompanies. -/
theorem log_lt_of_nontrivial_exponential_scale
    {C α d : ℝ} (hC : 1 ≤ C) (hα : 1 ≤ α)
    (hsmall : C * α * Real.exp (-d) < 1) :
    Real.log α < d := by
  have hαpos : 0 < α := zero_lt_one.trans_le hα
  have hfactor : 0 ≤ α * Real.exp (-d) := by positivity
  have hαsmall : α * Real.exp (-d) < 1 := by
    calc
      α * Real.exp (-d) = 1 * (α * Real.exp (-d)) := by ring
      _ ≤ C * (α * Real.exp (-d)) :=
        mul_le_mul_of_nonneg_right hC hfactor
      _ = C * α * Real.exp (-d) := by ring
      _ < 1 := hsmall
  apply (Real.log_lt_iff_lt_exp hαpos).2
  calc
    α = (α * Real.exp (-d)) * Real.exp d := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    _ < 1 * Real.exp d := mul_lt_mul_of_pos_right hαsmall (Real.exp_pos d)
    _ = Real.exp d := one_mul _

theorem log_alpha_lt_vinogradovDecay_of_nontrivialScale
    {C X F α : ℝ} (hC : 1 ≤ C) (hα : 1 ≤ α)
    (hsmall : C * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    Real.log α < (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
      (Real.log F) ^ 2 := by
  apply log_lt_of_nontrivial_exponential_scale hC hα
  rw [show -((2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
      (Real.log F) ^ 2) =
      -((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2 by ring]
  exact hsmall

/-- The source decay exponent is at most `2⁻²² log X`; this is the direct
consequence of the lower scale condition `F ≥ X⁴`. -/
theorem vinogradovDecay_le_two_neg22_mul_log
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 / (Real.log F) ^ 2 ≤
      (2 : ℝ) ^ (-22 : ℝ) * Real.log X := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hlogF : 0 < Real.log F := by
    apply Real.log_pos
    exact (show 1 < X ^ 4 by nlinarith [sq_nonneg (X ^ 2 - 4)]).trans_le hFhigh
  have hlogHigh : 4 * Real.log X ≤ Real.log F := by
    calc
      4 * Real.log X = Real.log (X ^ 4) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  have hsq : 16 * (Real.log X) ^ 2 ≤ (Real.log F) ^ 2 := by
    nlinarith
  rw [div_le_iff₀ (sq_pos_of_pos hlogF)]
  have hpow : (2 : ℝ) ^ (-18 : ℝ) =
      16 * (2 : ℝ) ^ (-22 : ℝ) := by norm_num
  rw [hpow]
  have hnonneg : 0 ≤ (2 : ℝ) ^ (-22 : ℝ) * Real.log X := by positivity
  nlinarith

/-- With leading constant two, a genuinely nontrivial target forces `X` far
past the bounded range: quantitatively, `2²² log 2 < log X`. -/
theorem two_pow_22_mul_log_two_lt_log_of_nontrivialScale
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (2 : ℝ) ^ (22 : ℝ) * Real.log 2 < Real.log X := by
  let d := (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 / (Real.log F) ^ 2
  have hlogTwo : Real.log 2 < d := by
    apply log_lt_of_nontrivial_exponential_scale hα (by norm_num)
    rw [show -d =
      -((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2 by simp only [d]; ring]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hsmall
  have hdecay : d ≤ (2 : ℝ) ^ (-22 : ℝ) * Real.log X := by
    exact vinogradovDecay_le_two_neg22_mul_log hX hFhigh
  have hprod : (2 : ℝ) ^ (22 : ℝ) * (2 : ℝ) ^ (-22 : ℝ) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    norm_num
  calc
    (2 : ℝ) ^ (22 : ℝ) * Real.log 2 <
        (2 : ℝ) ^ (22 : ℝ) * d :=
      mul_lt_mul_of_pos_left hlogTwo (Real.rpow_pos_of_pos (by norm_num) _)
    _ ≤ (2 : ℝ) ^ (22 : ℝ) *
        ((2 : ℝ) ^ (-22 : ℝ) * Real.log X) :=
      mul_le_mul_of_nonneg_left hdecay (Real.rpow_nonneg (by norm_num) _)
    _ = Real.log X := by rw [← mul_assoc, hprod, one_mul]

/-- In particular, the nontrivial branch with leading constant two guarantees
the elementary threshold needed for the floor-rounded averaging range. -/
theorem sixteen_lt_of_nontrivialScale
    {X F α : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    16 < X := by
  have hlarge := two_pow_22_mul_log_two_lt_log_of_nontrivialScale
    hX hFhigh hα hsmall
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hfour : 4 * Real.log 2 < (2 : ℝ) ^ (22 : ℝ) * Real.log 2 := by
    apply mul_lt_mul_of_pos_right _ hlogTwo
    norm_num
  have hlogSixteen : Real.log 16 = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
    norm_num
  have hlog : Real.log 16 < Real.log X := by linarith
  have hexp := Real.exp_lt_exp.mpr hlog
  rw [Real.exp_log (by norm_num), Real.exp_log (by linarith)] at hexp
  exact hexp

/-- Dividing a multiplicative coefficient window by its positive reference
scale preserves its two normalized endpoints. -/
theorem normalized_vinogradovCoefficient_bounds
    {F α q : ℝ} {k : ℕ}
    (hF : 0 < F)
    (hlow : F / α ^ k ≤ q) (hupp : q ≤ α ^ k * F) :
    1 / α ^ k ≤ q / F ∧ q / F ≤ α ^ k := by
  constructor
  · rw [le_div_iff₀ hF]
    simpa [div_eq_mul_inv, mul_comm] using hlow
  · rw [div_le_iff₀ hF]
    simpa [mul_comm] using hupp

/-- Logarithmic form of a normalized symmetric multiplicative window. -/
theorem abs_log_normalized_vinogradovCoefficient_le
    {F α q : ℝ} {k : ℕ}
    (hF : 0 < F) (hα : 1 ≤ α)
    (hlow : F / α ^ k ≤ q) (hupp : q ≤ α ^ k * F) :
    |Real.log (q / F)| ≤ (k : ℝ) * Real.log α := by
  have hαpos : 0 < α := zero_lt_one.trans_le hα
  have hpowpos : 0 < α ^ k := pow_pos hαpos k
  obtain ⟨hlow', hupp'⟩ :=
    normalized_vinogradovCoefficient_bounds hF hlow hupp
  have hqpos : 0 < q / F := (one_div_pos.mpr hpowpos).trans_le hlow'
  rw [abs_le]
  constructor
  · have hlog := Real.log_le_log (one_div_pos.mpr hpowpos) hlow'
    rw [Real.log_div (by positivity) (ne_of_gt hpowpos), Real.log_one,
      zero_sub, Real.log_pow] at hlog
    exact hlog
  · have hlog := Real.log_le_log hqpos hupp'
    rw [Real.log_pow] at hlog
    exact hlog

/-- A positive lower coefficient window forces the relevant absolute
coefficient to be strictly positive. -/
theorem abs_vinogradovCoefficient_pos
    {F α : ℝ} {n r : ℕ} {c : ℕ → ℝ}
    (hF : 0 < F) (hα : 0 < α) (hn : 0 < n)
    (hlow : F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r|) :
    0 < |c r| := by
  have hlowerpos : 0 < F / α ^ (r ^ 3) := div_pos hF (pow_pos hα _)
  have hqpos : 0 < (n : ℝ) ^ r * |c r| := hlowerpos.trans_le hlow
  have hnpowpos : 0 < (n : ℝ) ^ r := pow_pos (by exact_mod_cast hn) _
  apply pos_of_mul_pos_left (b := (n : ℝ) ^ r) _ hnpowpos.le
  simpa [mul_comm] using hqpos

/-- The derivative-window coefficients lie within `r³ log α` of their central
logarithmic size `log F - r log n`. -/
theorem abs_log_vinogradovCoefficient_sub_le
    {X F α : ℝ} {n r : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : X ≤ (n : ℝ))
    (hcoeff : F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
      (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F) :
    |Real.log |c r| - (Real.log F - (r : ℝ) * Real.log n)| ≤
      ((r ^ 3 : ℕ) : ℝ) * Real.log α := by
  have hFpos : 0 < F := lt_of_lt_of_le (by positivity : 0 < X ^ 4) hFhigh
  have hnpos : 0 < (n : ℝ) := lt_of_lt_of_le (by linarith) hn
  have hαpos : 0 < α := zero_lt_one.trans_le hα
  have hlowerpos : 0 < F / α ^ (r ^ 3) := div_pos hFpos (pow_pos hαpos _)
  have hqpos : 0 < (n : ℝ) ^ r * |c r| := hlowerpos.trans_le hcoeff.1
  have hcpos : 0 < |c r| := by
    by_contra hc
    have hczero : |c r| = 0 := le_antisymm (le_of_not_gt hc) (abs_nonneg _)
    rw [hczero, mul_zero] at hqpos
    exact (lt_irrefl 0) hqpos
  have hlog := abs_log_normalized_vinogradovCoefficient_le
    hFpos hα hcoeff.1 hcoeff.2
  rw [Real.log_div (mul_ne_zero (pow_ne_zero _ (ne_of_gt hnpos)) (ne_of_gt hcpos))
      (ne_of_gt hFpos),
    Real.log_mul (pow_ne_zero _ (ne_of_gt hnpos)) (ne_of_gt hcpos),
    Real.log_pow] at hlog
  rw [show Real.log |c r| - (Real.log F - (r : ℝ) * Real.log n) =
    (r : ℝ) * Real.log n + Real.log |c r| - Real.log F by ring]
  exact hlog

/-- Direct absolute-value form of the same coefficient window. -/
theorem abs_vinogradovCoefficient_bounds
    {F α : ℝ} {n r : ℕ} {c : ℕ → ℝ}
    (hn : 0 < n)
    (hcoeff : F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
      (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F) :
    F / α ^ (r ^ 3) / (n : ℝ) ^ r ≤ |c r| ∧
      |c r| ≤ α ^ (r ^ 3) * F / (n : ℝ) ^ r := by
  have hnpow : 0 < (n : ℝ) ^ r := pow_pos (by exact_mod_cast hn) _
  constructor
  · apply (div_le_iff₀ hnpow).2
    simpa [mul_comm] using hcoeff.1
  · apply (le_div_iff₀ hnpow).2
    simpa [mul_comm] using hcoeff.2

/-- Tao's medium-coefficient window for a polynomial bilinear sum. The
parameter `c₀` measures the fixed separation from both endpoint exponents
zero and two. -/
def IsVinogradovMediumCoefficient
    (M c₀ : ℝ) (c : ℕ → ℝ) (r : ℕ) : Prop :=
  M ^ (-(2 - c₀) * (r : ℝ)) ≤ |c r| ∧
    |c r| ≤ M ^ (-c₀ * (r : ℝ))

/-- Degrees between one and `R` whose coefficients satisfy the medium window. -/
noncomputable def vinogradovMediumCoefficientIndices
    (M c₀ : ℝ) (c : ℕ → ℝ) (R : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 R).filter (IsVinogradovMediumCoefficient M c₀ c)

@[simp]
theorem mem_vinogradovMediumCoefficientIndices
    {M c₀ : ℝ} {c : ℕ → ℝ} {R r : ℕ} :
    r ∈ vinogradovMediumCoefficientIndices M c₀ c R ↔
      1 ≤ r ∧ r ≤ R ∧ IsVinogradovMediumCoefficient M c₀ c r := by
  classical
  simp [vinogradovMediumCoefficientIndices, and_assoc]

/-- Explicit fixed-width block used to supply many medium coefficients. -/
noncomputable def vinogradovMediumDegreeBlock (X F : ℝ) : Finset ℕ :=
  Finset.Icc
    ⌈(4 / 3 : ℝ) * (Real.log F / Real.log X)⌉₊
    ⌊(7 / 4 : ℝ) * (Real.log F / Real.log X)⌋₊

/-- Real bounds attached to membership in the explicit degree block. -/
theorem mem_vinogradovMediumDegreeBlock_bounds
    {X F : ℝ} {r : ℕ} (hratio : 0 ≤ Real.log F / Real.log X)
    (hr : r ∈ vinogradovMediumDegreeBlock X F) :
    (4 / 3 : ℝ) * (Real.log F / Real.log X) ≤ (r : ℝ) ∧
      (r : ℝ) ≤ (7 / 4 : ℝ) * (Real.log F / Real.log X) := by
  rw [vinogradovMediumDegreeBlock, Finset.mem_Icc] at hr
  constructor
  · exact (Nat.le_ceil _).trans (by exact_mod_cast hr.1)
  · exact (by exact_mod_cast hr.2 : (r : ℝ) ≤
      (⌊(7 / 4 : ℝ) * (Real.log F / Real.log X)⌋₊ : ℝ)) |>.trans
        (Nat.floor_le (mul_nonneg (by norm_num) hratio))

/-- The explicit source block consists only of positive Taylor degrees not
exceeding `R = 10⌈log F/log X⌉`. -/
theorem mem_vinogradovMediumDegreeBlock_degree
    {X F : ℝ} {r : ℕ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F)
    (hr : r ∈ vinogradovMediumDegreeBlock X F) :
    1 ≤ r ∧ r ≤ vinogradovTaylorDegree X F := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hs : 4 ≤ Real.log F / Real.log X := by
    rw [le_div_iff₀ hlogX]
    calc
      4 * Real.log X = Real.log (X ^ 4) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  obtain ⟨hrlow, hrupp⟩ :=
    mem_vinogradovMediumDegreeBlock_bounds (by linarith) hr
  constructor
  · exact_mod_cast (show (1 : ℝ) ≤ r by nlinarith)
  · have hceil : Real.log F / Real.log X ≤
        (⌈Real.log F / Real.log X⌉₊ : ℝ) := Nat.le_ceil _
    have hrR : (r : ℝ) ≤
        (10 * ⌈Real.log F / Real.log X⌉₊ : ℕ) := by
      push_cast
      nlinarith
    exact_mod_cast hrR

/-- The explicit block contains at least `R/128` degrees. This is the precise
positive-density count required by the later mean-value theorem. -/
theorem vinogradovTaylorDegree_div_128_le_card_mediumDegreeBlock
    {X F : ℝ} (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) :
    (vinogradovTaylorDegree X F : ℝ) / 128 ≤
      (vinogradovMediumDegreeBlock X F).card := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  let s := Real.log F / Real.log X
  let a := ⌈(4 / 3 : ℝ) * s⌉₊
  let b := ⌊(7 / 4 : ℝ) * s⌋₊
  have hs : 4 ≤ s := by
    dsimp only [s]
    rw [le_div_iff₀ hlogX]
    calc
      4 * Real.log X = Real.log (X ^ 4) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log F := Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr (pow_pos hXpos 4)) (Set.mem_Ioi.mpr hFpos) hFhigh
  have ha : (a : ℝ) < (4 / 3 : ℝ) * s + 1 := by
    dsimp only [a]
    exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num) (by linarith))
  have hb : (7 / 4 : ℝ) * s < (b : ℝ) + 1 := by
    dsimp only [b]
    exact Nat.lt_floor_add_one _
  have hab : a ≤ b := by
    have haU : (a : ℝ) ≤ (7 / 4 : ℝ) * s := by nlinarith
    exact Nat.le_floor haU
  have hcard : ((vinogradovMediumDegreeBlock X F).card : ℝ) =
      (b : ℝ) + 1 - (a : ℝ) := by
    change ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ)
    rw [Nat.card_Icc, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one]
  have hcardLower : (5 / 12 : ℝ) * s - 1 <
      (vinogradovMediumDegreeBlock X F).card := by
    rw [hcard]
    nlinarith
  have hceil : (⌈s⌉₊ : ℝ) < s + 1 :=
    Nat.ceil_lt_add_one (by linarith)
  have hRupper : (vinogradovTaylorDegree X F : ℝ) < 10 * (s + 1) := by
    rw [vinogradovTaylorDegree]
    push_cast
    dsimp only [s] at hceil ⊢
    linarith
  nlinarith

/-- A medium-coefficient window remains valid when its separation parameter
is weakened. -/
theorem IsVinogradovMediumCoefficient.mono
    {M c₀ c₁ : ℝ} {c : ℕ → ℝ} {r : ℕ}
    (hM : 1 ≤ M) (hc : c₁ ≤ c₀)
    (h : IsVinogradovMediumCoefficient M c₀ c r) :
    IsVinogradovMediumCoefficient M c₁ c r := by
  have hr : 0 ≤ (r : ℝ) := by positivity
  have hleftExp : -(2 - c₁) * (r : ℝ) ≤ -(2 - c₀) * (r : ℝ) := by
    have := mul_le_mul_of_nonneg_right (show 2 - c₀ ≤ 2 - c₁ by linarith) hr
    linarith
  have hrightExp : -c₀ * (r : ℝ) ≤ -c₁ * (r : ℝ) := by
    have := mul_le_mul_of_nonneg_right hc hr
    linarith
  exact ⟨(Real.rpow_le_rpow_of_exponent_le hM hleftExp).trans h.1,
    h.2.trans (Real.rpow_le_rpow_of_exponent_le hM hrightExp)⟩

/-- Exponentiating a pair of logarithmic bounds produces Tao's
medium-coefficient window. -/
theorem isVinogradovMediumCoefficient_of_log_bounds
    {M c₀ : ℝ} {c : ℕ → ℝ} {r : ℕ}
    (hM : 0 < M) (hc : 0 < |c r|)
    (hlow : Real.log M * (-(2 - c₀) * (r : ℝ)) ≤ Real.log |c r|)
    (hupp : Real.log |c r| ≤ Real.log M * (-c₀ * (r : ℝ))) :
    IsVinogradovMediumCoefficient M c₀ c r := by
  constructor
  · rw [Real.rpow_def_of_pos hM, ← Real.exp_log hc]
    exact Real.exp_le_exp.mpr hlow
  · rw [Real.rpow_def_of_pos hM, ← Real.exp_log hc]
    exact Real.exp_le_exp.mpr hupp

/-- The derivative coefficient window implies medium size once the remaining
two real logarithmic comparisons have been discharged. This cleanly isolates
the numerical block-selection step from the analytic mean-value theorem. -/
theorem isVinogradovMediumCoefficient_of_coefficientWindow
    {X F α M c₀ : ℝ} {n r : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : X ≤ (n : ℝ))
    (hM : 0 < M)
    (hcoeff : F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
      (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hlow : Real.log M * (-(2 - c₀) * (r : ℝ)) ≤
      Real.log F - (r : ℝ) * Real.log n -
        ((r ^ 3 : ℕ) : ℝ) * Real.log α)
    (hupp : Real.log F - (r : ℝ) * Real.log n +
        ((r ^ 3 : ℕ) : ℝ) * Real.log α ≤
      Real.log M * (-c₀ * (r : ℝ))) :
    IsVinogradovMediumCoefficient M c₀ c r := by
  have hnrealpos : 0 < (n : ℝ) := lt_of_lt_of_le (by linarith) hn
  have hnpos : 0 < n := by exact_mod_cast hnrealpos
  have hFpos : 0 < F := lt_of_lt_of_le (by positivity : 0 < X ^ 4) hFhigh
  have hcpos := abs_vinogradovCoefficient_pos hFpos
    (zero_lt_one.trans_le hα) hnpos hcoeff.1
  have hlog := abs_log_vinogradovCoefficient_sub_le hX hFhigh hα hn hcoeff
  rw [abs_le] at hlog
  apply isVinogradovMediumCoefficient_of_log_bounds hM hcpos
  · linarith [hlog.1]
  · linarith [hlog.2]

/-- Elementary distortion calculation behind the medium-coefficient block:
if `r ≤ (7/4)s` and `A < 2⁻¹⁸L/s²`, then the cubic loss is bounded by the
linear budget `rL/65536`. -/
theorem cube_mul_lt_linear_of_ratio
    {r s L A : ℝ} (hr : 0 < r) (hs : 0 < s) (hL : 0 < L) (hA0 : 0 ≤ A)
    (hrs : r ≤ (7 / 4 : ℝ) * s)
    (hA : A < (2 : ℝ) ^ (-18 : ℝ) * L / s ^ 2) :
    r ^ 3 * A < r * L / 65536 := by
  have hsq : r ^ 2 ≤ (49 / 16 : ℝ) * s ^ 2 := by nlinarith
  have hAs : A * s ^ 2 < (2 : ℝ) ^ (-18 : ℝ) * L := by
    rw [lt_div_iff₀ (sq_pos_of_pos hs)] at hA
    nlinarith
  have hquad : r ^ 2 * A < L / 65536 := by
    calc
      r ^ 2 * A ≤ ((49 / 16 : ℝ) * s ^ 2) * A :=
        mul_le_mul_of_nonneg_right hsq hA0
      _ = (49 / 16 : ℝ) * (A * s ^ 2) := by ring
      _ < (49 / 16 : ℝ) * ((2 : ℝ) ^ (-18 : ℝ) * L) := by gcongr
      _ < L / 65536 := by
        have hconst : (49 / 16 : ℝ) * (2 : ℝ) ^ (-18 : ℝ) < 1 / 65536 := by
          norm_num
        nlinarith
  calc
    r ^ 3 * A = r * (r ^ 2 * A) := by ring
    _ < r * (L / 65536) := mul_lt_mul_of_pos_left hquad hr
    _ = r * L / 65536 := by ring

/-- Vinogradov's nontrivial-scale condition makes the coefficient distortion
negligible throughout the upper end `r ≤ (7/4)(log F/log X)` of the selected
degree block. -/
theorem cube_log_alpha_lt_linear_of_mediumIndex
    {X F α : ℝ} {r : ℕ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α) (hr : 1 ≤ r)
    (hrupp : (r : ℝ) ≤ (7 / 4 : ℝ) * (Real.log F / Real.log X))
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    ((r ^ 3 : ℕ) : ℝ) * Real.log α <
      (r : ℝ) * Real.log X / 65536 := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hlogF : 0 < Real.log F := Real.log_pos
    ((show 1 < X ^ 4 by nlinarith [sq_nonneg (X ^ 2 - 4)]).trans_le hFhigh)
  let s := Real.log F / Real.log X
  have hs : 0 < s := div_pos hlogF hlogX
  have hlogα := log_alpha_lt_vinogradovDecay_of_nontrivialScale
    (by norm_num : (1 : ℝ) ≤ 2) hα hsmall
  have hdecay : (2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
      (Real.log F) ^ 2 = (2 : ℝ) ^ (-18 : ℝ) * Real.log X / s ^ 2 := by
    dsimp only [s]
    field_simp
  rw [hdecay] at hlogα
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  have hmain := cube_mul_lt_linear_of_ratio hrpos hs hlogX
    (Real.log_nonneg hα) (by simpa only [s] using hrupp) hlogα
  norm_num only [Nat.cast_pow] at hmain ⊢
  exact hmain

/-- Every degree in the fixed source block
`(4/3)(log F/log X) ≤ r ≤ (7/4)(log F/log X)` is medium-sized with
`c₀ = 1/8`, for the actual floor-rounded averaging range. This is the
coefficient-selection input to the polynomial mean-value theorem. -/
theorem isVinogradovMediumCoefficient_eighth_of_sourceBlock
    {X F α : ℝ} {n r : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hr : 1 ≤ r)
    (hrlow : (4 / 3 : ℝ) * (Real.log F / Real.log X) ≤ (r : ℝ))
    (hrupp : (r : ℝ) ≤ (7 / 4 : ℝ) * (Real.log F / Real.log X))
    (hcoeff : F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
      (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    IsVinogradovMediumCoefficient (vinogradovAveragingRange X : ℝ)
      (1 / 8) c r := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hlogF : 0 < Real.log F := Real.log_pos
    ((show 1 < X ^ 4 by nlinarith [sq_nonneg (X ^ 2 - 4)]).trans_le hFhigh)
  have hnpos : 0 < (n : ℝ) := hXpos.trans_le hn.1
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr
  let s := Real.log F / Real.log X
  have hspos : 0 < s := div_pos hlogF hlogX
  have hsIdentity : Real.log F = s * Real.log X := by
    dsimp only [s]
    field_simp
  have hsLower : (4 / 7 : ℝ) * (r : ℝ) ≤ s := by
    dsimp only [s] at hrupp ⊢
    linarith
  have hsUpper : s ≤ (3 / 4 : ℝ) * (r : ℝ) := by
    dsimp only [s] at hrlow ⊢
    linarith
  have hsLowerMul : (4 / 7 : ℝ) * (r : ℝ) * Real.log X ≤
      s * Real.log X := mul_le_mul_of_nonneg_right hsLower hlogX.le
  have hsUpperMul : s * Real.log X ≤
      (3 / 4 : ℝ) * (r : ℝ) * Real.log X :=
    mul_le_mul_of_nonneg_right hsUpper hlogX.le
  have hlognLow : Real.log X ≤ Real.log n :=
    Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hXpos)
      (Set.mem_Ioi.mpr hnpos) hn.1
  have hlognUpp : Real.log n ≤ Real.log X + Real.log 2 := by
    have h2Xpos : 0 < 2 * X := mul_pos (by norm_num) hXpos
    have h := Real.strictMonoOn_log.monotoneOn (Set.mem_Ioi.mpr hnpos)
      (Set.mem_Ioi.mpr h2Xpos) hn.2
    rw [Real.log_mul (by norm_num) (ne_of_gt hXpos)] at h
    linarith
  have hlognLowMul : (r : ℝ) * Real.log X ≤ (r : ℝ) * Real.log n :=
    mul_le_mul_of_nonneg_left hlognLow hrpos.le
  have hlognUppMul : (r : ℝ) * Real.log n ≤
      (r : ℝ) * (Real.log X + Real.log 2) :=
    mul_le_mul_of_nonneg_left hlognUpp hrpos.le
  have herror := cube_log_alpha_lt_linear_of_mediumIndex
    hX hFhigh hα hr hrupp hsmall
  have hXsixteen : 16 ≤ X :=
    (sixteen_lt_of_nontrivialScale hX hFhigh hα hsmall).le
  obtain ⟨hlogVLow, hlogVUpp⟩ := log_vinogradovAveragingRange_bounds hXsixteen
  have hVpos : 0 < (vinogradovAveragingRange X : ℝ) := by
    exact_mod_cast vinogradovAveragingRange_pos (show 1 ≤ X by linarith)
  have hlarge := two_pow_22_mul_log_two_lt_log_of_nontrivialScale
    hX hFhigh hα hsmall
  have hbig : (2 : ℝ) ^ (22 : ℝ) * (r : ℝ) * Real.log 2 <
      (r : ℝ) * Real.log X := by
    nlinarith
  norm_num at hbig
  apply isVinogradovMediumCoefficient_of_coefficientWindow
    hX hFhigh hα hn.1 hVpos hcoeff
  · rw [hsIdentity]
    have hnegative : -(2 - (1 / 8 : ℝ)) * (r : ℝ) < 0 := by
      norm_num
      omega
    have hleft := mul_lt_mul_of_neg_right hlogVLow hnegative
    nlinarith
  · rw [hsIdentity]
    have hnegative : -(1 / 8 : ℝ) * (r : ℝ) < 0 := by
      norm_num
      omega
    have hright := mul_le_mul_of_nonpos_right hlogVUpp hnegative.le
    nlinarith

/-- The same source block meets the smaller separation constant `1/128`,
which is compatible with its positive density among the `R` Taylor degrees. -/
theorem isVinogradovMediumCoefficient_one_div_128_of_sourceBlock
    {X F α : ℝ} {n r : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X)) (hr : 1 ≤ r)
    (hrlow : (4 / 3 : ℝ) * (Real.log F / Real.log X) ≤ (r : ℝ))
    (hrupp : (r : ℝ) ≤ (7 / 4 : ℝ) * (Real.log F / Real.log X))
    (hcoeff : F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
      (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    IsVinogradovMediumCoefficient (vinogradovAveragingRange X : ℝ)
      (1 / 128) c r := by
  have hV : 1 ≤ (vinogradovAveragingRange X : ℝ) := by
    exact_mod_cast (vinogradovAveragingRange_pos (show 1 ≤ X by linarith))
  apply IsVinogradovMediumCoefficient.mono (c₀ := 1 / 8) hV (by norm_num)
  exact isVinogradovMediumCoefficient_eighth_of_sourceBlock
    hX hFhigh hα hn hr hrlow hrupp hcoeff hsmall

/-- The source derivative window supplies at least `R/128` medium coefficients
for the actual floor-rounded bilinear sum. This completes the coefficient
selection and counting stage preceding the Vinogradov mean-value argument. -/
theorem vinogradovTaylorDegree_div_128_le_card_mediumCoefficientIndices
    {X F α : ℝ} {n : ℕ} {c : ℕ → ℝ}
    (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : (n : ℝ) ∈ Set.Icc X (2 * X))
    (hcoeff : ∀ r : ℕ, 1 ≤ r → r ≤ vinogradovTaylorDegree X F →
      F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
        (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : 2 * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    (vinogradovTaylorDegree X F : ℝ) / 128 ≤
      (vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 128) c
        (vinogradovTaylorDegree X F)).card := by
  have hXpos : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hFpos : 0 < F := (pow_pos hXpos 4).trans_le hFhigh
  have hratio : 0 ≤ Real.log F / Real.log X :=
    (div_pos (Real.log_pos
      ((show 1 < X ^ 4 by nlinarith [sq_nonneg (X ^ 2 - 4)]).trans_le hFhigh))
      hlogX).le
  have hsubset : vinogradovMediumDegreeBlock X F ⊆
      vinogradovMediumCoefficientIndices
        (vinogradovAveragingRange X : ℝ) (1 / 128) c
        (vinogradovTaylorDegree X F) := by
    intro r hr
    obtain ⟨hrlow, hrupp⟩ :=
      mem_vinogradovMediumDegreeBlock_bounds hratio hr
    obtain ⟨hrone, hrR⟩ := mem_vinogradovMediumDegreeBlock_degree hX hFhigh hr
    rw [mem_vinogradovMediumCoefficientIndices]
    exact ⟨hrone, hrR,
      isVinogradovMediumCoefficient_one_div_128_of_sourceBlock
        hX hFhigh hα hn hrone hrlow hrupp (hcoeff r hrone hrR) hsmall⟩
  exact (vinogradovTaylorDegree_div_128_le_card_mediumDegreeBlock hX hFhigh).trans
    (by exact_mod_cast Finset.card_le_card hsubset)

/-- In the nontrivial branch, the logarithmic displacement of every positive
degree coefficient has the strict source decay budget. -/
theorem abs_log_vinogradovCoefficient_sub_lt_of_nontrivialScale
    {C X F α : ℝ} {n r : ℕ} {c : ℕ → ℝ}
    (hC : 1 ≤ C) (hX : 2 ≤ X) (hFhigh : X ^ 4 ≤ F) (hα : 1 ≤ α)
    (hn : X ≤ (n : ℝ)) (hr : 1 ≤ r)
    (hcoeff : F / α ^ (r ^ 3) ≤ (n : ℝ) ^ r * |c r| ∧
      (n : ℝ) ^ r * |c r| ≤ α ^ (r ^ 3) * F)
    (hsmall : C * α * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log F) ^ 2) < 1) :
    |Real.log |c r| - (Real.log F - (r : ℝ) * Real.log n)| <
      ((r ^ 3 : ℕ) : ℝ) *
        ((2 : ℝ) ^ (-18 : ℝ) * (Real.log X) ^ 3 /
          (Real.log F) ^ 2) := by
  refine (abs_log_vinogradovCoefficient_sub_le hX hFhigh hα hn hcoeff).trans_lt ?_
  apply mul_lt_mul_of_pos_left
    (log_alpha_lt_vinogradovDecay_of_nontrivialScale hC hα hsmall)
  exact_mod_cast (pow_pos hr 3)

theorem vinogradovBilinearPolynomialEstimateAt_of_nontrivialEstimateAt
    {C : ℝ} (hnontrivial : VinogradovBilinearPolynomialNontrivialEstimateAt C) :
    VinogradovBilinearPolynomialEstimateAt C := by
  refine ⟨zero_lt_one.trans_le hnontrivial.1, ?_⟩
  intro X F α n c hX hFhigh hα hn hcoeff
  let D := C * α * Real.exp
    (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
      (Real.log F) ^ 2)
  by_cases hD : D < 1
  · simpa only [D] using hnontrivial.2 X F α n c hX hFhigh hα hn hcoeff
      (by simpa only [D] using hD)
  · have hOne : 1 ≤ D := le_of_not_gt hD
    calc
      ‖vinogradovBilinearPolynomialSum c (vinogradovTaylorDegree X F)
          (vinogradovAveragingRange X)‖ ≤
        ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ)) :=
        norm_vinogradovBilinearPolynomialSum_le _ _ _
      _ = ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ)) * 1 := by ring
      _ ≤ ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ)) * D :=
        mul_le_mul_of_nonneg_left hOne (by positivity)
      _ = ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ)) *
          (C * α * Real.exp
            (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
              (Real.log F) ^ 2)) := by rfl

/-- Pointwise bilinear estimate for the complete product sum at a single base
point. This is the direct formal counterpart of the sum over `1 ≤ x,y ≤ V`
estimated on pp. 217--225 of Iwaniec--Kowalski. -/
def VinogradovTaylorPolynomialLocalProductSumEstimateAt (C : ℝ) : Prop :=
  0 < C ∧ ∀ (X F α : ℝ) (n : ℕ) (f : ℝ → ℝ),
    2 ≤ X → X ^ 4 ≤ F → 1 ≤ α →
    (n : ℝ) ∈ Set.Icc X (2 * X) →
    (∀ r : ℕ, 1 ≤ r → r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          (n : ℝ) ^ r / (r.factorial : ℝ) * |iteratedDeriv r f n| ∧
        (n : ℝ) ^ r / (r.factorial : ℝ) * |iteratedDeriv r f n| ≤
          α ^ (r ^ 3) * F) →
    ‖vinogradovTaylorPolynomialLocalProductSum f
        (vinogradovTaylorDegree X F) n (vinogradovAveragingRange X)‖ ≤
      ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        (C * α * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)))

/-- Substitution of the actual Taylor coefficients into the generic bilinear
polynomial estimate. -/
theorem vinogradovTaylorPolynomialLocalProductSumEstimateAt_of_bilinearPolynomialEstimateAt
    {C : ℝ} (hbilinear : VinogradovBilinearPolynomialEstimateAt C) :
    VinogradovTaylorPolynomialLocalProductSumEstimateAt C := by
  refine ⟨hbilinear.1, ?_⟩
  intro X F α n f hX hFhigh hα hn hderiv
  rw [norm_vinogradovTaylorPolynomialLocalProductSum_eq_bilinearSum,
    vinogradovTaylorBilinearSum_eq_bilinearPolynomialSum]
  apply hbilinear.2 X F α n (vinogradovTaylorCoefficient f n)
    hX hFhigh hα hn
  intro r hr hdegree
  rw [pow_mul_abs_vinogradovTaylorCoefficient]
  apply hderiv r hr
  rw [← vinogradovTaylorDegree_add_one]
  omega

/-- Exact residual polynomial estimate after the Taylor and averaging stages.
As stated in the pinned proof, this stage assumes only the normalized
derivative window (besides `F ≥ X⁴` and interval geometry), not the Taylor
smoothness or numerical-smallness hypotheses. -/
def VinogradovTaylorPolynomialPairSumEstimateAt (C : ℝ) : Prop :=
  0 < C ∧ ∀ (X F α : ℝ) (a b : ℕ) (f : ℝ → ℝ),
    2 ≤ X → X ^ 4 ≤ F → 1 ≤ α →
    Set.Icc (a : ℝ) (b : ℝ) ⊆ Set.Icc X (2 * X) →
    (∀ t ∈ Set.Icc (a : ℝ) (b : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X F →
      F / α ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ∧
        t ^ r / (r.factorial : ℝ) * |iteratedDeriv r f t| ≤
          α ^ (r ^ 3) * F) →
    ‖vinogradovTaylorPolynomialPairSum f
        (vinogradovTaylorDegree X F) a b (vinogradovAveragingRange X)‖ ≤
      ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) *
        (C * α * X * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)))

/-- The pointwise bilinear estimate implies the interval-level pair-sum
estimate. The right-boundary strip is absorbed using nine copies of the same
Vinogradov scale. -/
theorem vinogradovTaylorPolynomialPairSumEstimateAt_of_localProductSumEstimateAt
    {C : ℝ} (hlocal : VinogradovTaylorPolynomialLocalProductSumEstimateAt C) :
    VinogradovTaylorPolynomialPairSumEstimateAt (C + 9) := by
  refine ⟨by linarith [hlocal.1], ?_⟩
  intro X F α a b f hX hFhigh hα hI hderiv
  let V := vinogradovAveragingRange X
  let R := vinogradovTaylorDegree X F
  let E := Real.exp
    (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
      (Real.log F) ^ 2)
  have hpoint : ∀ n ∈ Finset.Ico a (b - V ^ 2),
      ‖vinogradovTaylorPolynomialLocalProductSum f R n V‖ ≤
        (((V ^ 2 : ℕ) : ℝ)) * (C * α * E) := by
    intro n hn
    have hn' := Finset.mem_Ico.mp hn
    have hnab : (n : ℝ) ∈ Set.Icc (a : ℝ) (b : ℝ) := by
      constructor
      · exact_mod_cast hn'.1
      · exact_mod_cast (show n ≤ b by omega)
    simpa only [R, V, E] using hlocal.2 X F α n f hX hFhigh hα
      (hI hnab) (fun r hr hrR => hderiv n hnab r hr hrR)
  have hpair := norm_vinogradovTaylorPolynomialPairSum_le_of_local
    f R a b V hpoint
  have hcardNat : (Finset.Ico a (b - V ^ 2)).card ≤ b - a := by
    simp only [Nat.card_Ico]
    omega
  have hcard : ((Finset.Ico a (b - V ^ 2)).card : ℝ) ≤ X := by
    have hcardBA : ((Finset.Ico a (b - V ^ 2)).card : ℝ) ≤
        ((b - a : ℕ) : ℝ) := by exact_mod_cast hcardNat
    by_cases hab : a < b
    · have habReal : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab.le
      have hXa : X ≤ (a : ℝ) := (hI ⟨le_rfl, habReal⟩).1
      have hbX : (b : ℝ) ≤ 2 * X := (hI ⟨habReal, le_rfl⟩).2
      calc
        ((Finset.Ico a (b - V ^ 2)).card : ℝ) ≤ ((b - a : ℕ) : ℝ) := hcardBA
        _ = (b : ℝ) - (a : ℝ) := by rw [Nat.cast_sub hab.le]
        _ ≤ X := by linarith
    · have hzero : b - a = 0 := by omega
      rw [hzero, Nat.cast_zero] at hcardBA
      exact hcardBA.trans (by linarith)
  let B := α * X * E
  have hTaylor : Real.sqrt X + 2 * Real.pi ≤ 9 * B := by
    simpa only [B, E] using sqrt_add_two_pi_le_nine_mul_vinogradovScale
      hX hFhigh hα
  have hVtwo : (((V ^ 2 : ℕ) : ℝ)) ≤ 9 * B := by
    calc
      (((V ^ 2 : ℕ) : ℝ)) ≤ Real.sqrt X := by
        simpa only [V] using vinogradovAveragingRange_sq_le_sqrt X
      _ ≤ Real.sqrt X + 2 * Real.pi := le_add_of_nonneg_right (by positivity)
      _ ≤ 9 * B := hTaylor
  have hVnonneg : 0 ≤ (((V ^ 2 : ℕ) : ℝ)) := by positivity
  have hlocalScale : 0 ≤ (((V ^ 2 : ℕ) : ℝ)) * (C * α * E) := by
    have hC : 0 < C := hlocal.1
    positivity
  calc
    ‖vinogradovTaylorPolynomialPairSum f
        (vinogradovTaylorDegree X F) a b (vinogradovAveragingRange X)‖ =
      ‖vinogradovTaylorPolynomialPairSum f R a b V‖ := by rfl
    _ ≤ (((V ^ 2 : ℕ) : ℝ)) * (((V ^ 2 : ℕ) : ℝ)) +
        ((Finset.Ico a (b - V ^ 2)).card : ℝ) *
          ((((V ^ 2 : ℕ) : ℝ)) * (C * α * E)) := hpair
    _ ≤ (((V ^ 2 : ℕ) : ℝ)) * (9 * B) +
        X * ((((V ^ 2 : ℕ) : ℝ)) * (C * α * E)) :=
      add_le_add (mul_le_mul_of_nonneg_left hVtwo hVnonneg)
        (mul_le_mul_of_nonneg_right hcard hlocalScale)
    _ = (((V ^ 2 : ℕ) : ℝ)) * ((C + 9) * B) := by
      dsimp only [B]
      ring
    _ = ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ)) *
        ((C + 9) * α * X * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2)) := by
      dsimp only [V, B, E]
      ring

/-- Existence form of the sole residual Iwaniec--Kowalski polynomial
mean-value estimate. -/
def VinogradovTaylorPolynomialPairSumEstimate : Prop :=
  ∃ C : ℝ, VinogradovTaylorPolynomialPairSumEstimateAt C

/-- Existence form of the pointwise bilinear estimate which is now the
smallest source-faithful residual Vinogradov input. -/
def VinogradovTaylorPolynomialLocalProductSumEstimate : Prop :=
  ∃ C : ℝ, VinogradovTaylorPolynomialLocalProductSumEstimateAt C

/-- Existence form of the coefficient-only bilinear polynomial estimate. -/
def VinogradovBilinearPolynomialEstimate : Prop :=
  ∃ C : ℝ, VinogradovBilinearPolynomialEstimateAt C

/-- Existence form of the genuinely nontrivial coefficient-only branch. -/
def VinogradovBilinearPolynomialNontrivialEstimate : Prop :=
  ∃ C : ℝ, VinogradovBilinearPolynomialNontrivialEstimateAt C

/-- The residual polynomial-pair estimate implies the exact Vinogradov
exponential-sum contract; its absolute coefficient increases by the explicit
Taylor-loss value nine. -/
theorem vinogradovExponentialSumEstimateAt_of_taylorPolynomialPairSumEstimateAt
    {C : ℝ} (hpair : VinogradovTaylorPolynomialPairSumEstimateAt C) :
    VinogradovExponentialSumEstimateAt (C + 9) := by
  refine ⟨by linarith [hpair.1], ?_⟩
  intro X F α a b f hX hFhigh hα hsmall hI hsmooth hderiv
  let B := α * X * Real.exp
    (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
      (Real.log F) ^ 2)
  have hpoly : ‖vinogradovTaylorPolynomialPairSum f
      (vinogradovTaylorDegree X F) a b (vinogradovAveragingRange X)‖ ≤
      ((((vinogradovAveragingRange X) ^ 2 : ℕ) : ℝ) * (C * B)) := by
    simpa only [B, mul_assoc] using hpair.2 X F α a b f
      hX hFhigh hα hI hderiv
  have hsum :=
    norm_sum_Ico_standardAdditiveCharacter_le_of_source_pairSum_of_subset
      hX hFhigh hα hsmall hI hsmooth hderiv hpoly
  have hTaylor : Real.sqrt X + 2 * Real.pi ≤ 9 * B := by
    simpa only [B] using sqrt_add_two_pi_le_nine_mul_vinogradovScale
      hX hFhigh hα
  calc
    ‖∑ n ∈ Finset.Ico a b, standardAdditiveCharacter (f n)‖ ≤
        Real.sqrt X + 2 * Real.pi + C * B := hsum
    _ ≤ 9 * B + C * B := add_le_add hTaylor le_rfl
    _ = (C + 9) * α * X * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log F) ^ 2) := by
      dsimp only [B]
      ring

theorem vinogradovExponentialSumEstimate_of_taylorPolynomialPairSumEstimate
    (hpair : VinogradovTaylorPolynomialPairSumEstimate) :
    VinogradovExponentialSumEstimate := by
  obtain ⟨C, hC⟩ := hpair
  exact ⟨C + 9,
    vinogradovExponentialSumEstimateAt_of_taylorPolynomialPairSumEstimateAt hC⟩

/-- A pointwise Iwaniec--Kowalski bilinear estimate proves the exact source
Vinogradov contract after the two explicit boundary/Taylor absorptions. -/
theorem vinogradovExponentialSumEstimateAt_of_localProductSumEstimateAt
    {C : ℝ} (hlocal : VinogradovTaylorPolynomialLocalProductSumEstimateAt C) :
    VinogradovExponentialSumEstimateAt ((C + 9) + 9) :=
  vinogradovExponentialSumEstimateAt_of_taylorPolynomialPairSumEstimateAt
    (vinogradovTaylorPolynomialPairSumEstimateAt_of_localProductSumEstimateAt hlocal)

theorem vinogradovExponentialSumEstimate_of_localProductSumEstimate
    (hlocal : VinogradovTaylorPolynomialLocalProductSumEstimate) :
    VinogradovExponentialSumEstimate := by
  obtain ⟨C, hC⟩ := hlocal
  exact ⟨(C + 9) + 9,
    vinogradovExponentialSumEstimateAt_of_localProductSumEstimateAt hC⟩

/-- The coefficient-only bilinear polynomial estimate is sufficient for the
full source Vinogradov proposition. -/
theorem vinogradovExponentialSumEstimateAt_of_bilinearPolynomialEstimateAt
    {C : ℝ} (hbilinear : VinogradovBilinearPolynomialEstimateAt C) :
    VinogradovExponentialSumEstimateAt ((C + 9) + 9) :=
  vinogradovExponentialSumEstimateAt_of_localProductSumEstimateAt
    (vinogradovTaylorPolynomialLocalProductSumEstimateAt_of_bilinearPolynomialEstimateAt
      hbilinear)

theorem vinogradovExponentialSumEstimate_of_bilinearPolynomialEstimate
    (hbilinear : VinogradovBilinearPolynomialEstimate) :
    VinogradovExponentialSumEstimate := by
  obtain ⟨C, hC⟩ := hbilinear
  exact ⟨(C + 9) + 9,
    vinogradovExponentialSumEstimateAt_of_bilinearPolynomialEstimateAt hC⟩

theorem vinogradovExponentialSumEstimate_of_bilinearPolynomialNontrivialEstimate
    (hnontrivial : VinogradovBilinearPolynomialNontrivialEstimate) :
    VinogradovExponentialSumEstimate := by
  obtain ⟨C, hC⟩ := hnontrivial
  exact vinogradovExponentialSumEstimate_of_bilinearPolynomialEstimate
    ⟨C, vinogradovBilinearPolynomialEstimateAt_of_nontrivialEstimateAt hC⟩

/-- On every regular interval, the reciprocal phase satisfies the complete
source-normalized derivative window through the literal Vinogradov cutoff
`10⌈log F/log X⌉+1`.  The logarithmic choices of `α` and `q` are discharged
from the common source budget. -/
theorem reciprocalPhase_vinogradov_derivative_bounds_on_regular_interval_sourceCutoff
    (N M P A : ℝ) {j : ℕ} {X Y c d : ℝ}
    (hX : 0 < X) (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff X
      (reciprocalPhaseScale N M j X) + j : ℕ) : ℝ)) ≤ Real.log P)
    (hj : 1 ≤ j) (hI : Set.Icc c d ⊆ Set.Icc X Y)
    (hYtop : Y ≤ 2 * X)
    (hRegular : ∀ t ∈ Set.Icc c d,
      t ∉ reciprocalDerivativeCriticalUnion N M j
        (Finset.Icc 1
          (vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X)))
        X Y ((Real.log P) ^ (-3 * A))) :
    ∀ t ∈ Set.Icc c d, ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X) →
      reciprocalPhaseScale N M j X /
          ((Real.log P) ^ (4 * A)) ^ (r ^ 3) ≤
        t ^ r / (r.factorial : ℝ) *
          |iteratedDeriv r (reciprocalPhase N M j) t| ∧
      t ^ r / (r.factorial : ℝ) *
          |iteratedDeriv r (reciprocalPhase N M j) t| ≤
        ((Real.log P) ^ (4 * A)) ^ (r ^ 3) *
          reciprocalPhaseScale N M j X := by
  obtain ⟨hq, hqOne, hα, hRj, hαq⟩ :=
    vinogradov_log_power_parameters hlog hA hcutoff hten
  exact reciprocalPhase_vinogradov_derivative_bounds_on_regular_interval
    N M hX hq hqOne hα hj hI hYtop hRegular hRj hαq

/-- Regular forward windows of the literal source-cutoff length provide the
complete derivative window on the underlying consecutive real interval.  This
is the exact bridge from the expanded critical-start deletion used by the
global phase-sum decomposition to the smooth hypothesis used by Vinogradov's
estimate. -/
theorem reciprocalPhase_vinogradov_derivative_bounds_of_sourceCutoff_forwardWindows
    (N M P A : ℝ) {j : ℕ} {X Y : ℝ} {c d : ℕ}
    (hX : 0 < X) (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff X
      (reciprocalPhaseScale N M j X) + j : ℕ) : ℝ)) ≤ Real.log P)
    (hj : 1 ≤ j) (hcd : c < d)
    (hI : Set.Icc (c : ℝ) (d : ℝ) ⊆ Set.Icc X Y)
    (hYtop : Y ≤ 2 * X)
    (hwindow : ∀ n ∈ Finset.Ico c d,
      ¬ ∃ t ∈ Set.Icc (n : ℝ)
          ((n + vinogradovDerivativeCutoff X
            (reciprocalPhaseScale N M j X) : ℕ) : ℝ),
        t ∈ reciprocalDerivativeCriticalUnion N M j
          (Finset.Icc 1
            (vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X)))
          X Y ((Real.log P) ^ (-3 * A))) :
    ∀ t ∈ Set.Icc (c : ℝ) (d : ℝ), ∀ r : ℕ, 1 ≤ r →
      r ≤ vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X) →
      reciprocalPhaseScale N M j X /
          ((Real.log P) ^ (4 * A)) ^ (r ^ 3) ≤
        t ^ r / (r.factorial : ℝ) *
          |iteratedDeriv r (reciprocalPhase N M j) t| ∧
      t ^ r / (r.factorial : ℝ) *
          |iteratedDeriv r (reciprocalPhase N M j) t| ≤
        ((Real.log P) ^ (4 * A)) ^ (r ^ 3) *
          reciprocalPhaseScale N M j X := by
  let R := vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X)
  have hR : 1 ≤ R := by
    simp [R, vinogradovDerivativeCutoff]
  have hregularExpanded : ∀ t ∈ Set.Icc (c : ℝ)
      ((d - 1 + R : ℕ) : ℝ),
      t ∉ reciprocalDerivativeCriticalUnion N M j
        (Finset.Icc 1 R) X Y ((Real.log P) ^ (-3 * A)) :=
    forall_Icc_of_forall_Ico_forwardWindow
      (fun t => t ∉ reciprocalDerivativeCriticalUnion N M j
        (Finset.Icc 1 R) X Y ((Real.log P) ^ (-3 * A))) hcd hR
      (fun n hn t ht htCritical => hwindow n hn ⟨t, ht, htCritical⟩)
  have hRegular : ∀ t ∈ Set.Icc (c : ℝ) (d : ℝ),
      t ∉ reciprocalDerivativeCriticalUnion N M j
        (Finset.Icc 1 R) X Y ((Real.log P) ^ (-3 * A)) := by
    intro t ht
    apply hregularExpanded t
    refine ⟨ht.1, ?_⟩
    calc
      t ≤ (d : ℝ) := ht.2
      _ ≤ ((d - 1 + R : ℕ) : ℝ) := by
        exact_mod_cast (by omega : d ≤ d - 1 + R)
  simpa only [R] using
    reciprocalPhase_vinogradov_derivative_bounds_on_regular_interval_sourceCutoff
      N M P A hX hlog hA hten hcutoff hj hI hYtop hRegular

/-- Conditional global high-scale estimate with every non-analytic step
discharged.  The sole callback is a Vinogradov bound for a phase satisfying the
displayed source-normalized derivative window; critical deletion, regular
component counting, and the literal cutoff are handled by this theorem. -/
theorem norm_reciprocalPhaseSum_le_sourceVinogradov_componentEnvelope
    (N M P A B : ℝ) (j a b : ℕ) {X Y : ℝ}
    (hB : 0 ≤ B) (hX : 0 < X) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff X
      (reciprocalPhaseScale N M j X) + j : ℕ) : ℝ)) ≤ Real.log P)
    (hXa : X ≤ (a : ℝ)) (hbY : (b : ℝ) ≤ Y) (hYtop : Y ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1))
    (hvinogradov : ∀ c d : ℕ, a ≤ c → d ≤ b → c < d →
      (∀ t ∈ Set.Icc (c : ℝ) (d : ℝ), ∀ r : ℕ, 1 ≤ r →
        r ≤ vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X) →
        reciprocalPhaseScale N M j X /
            ((Real.log P) ^ (4 * A)) ^ (r ^ 3) ≤
          t ^ r / (r.factorial : ℝ) *
            |iteratedDeriv r (reciprocalPhase N M j) t| ∧
        t ^ r / (r.factorial : ℝ) *
            |iteratedDeriv r (reciprocalPhase N M j) t| ≤
          ((Real.log P) ^ (4 * A)) ^ (r ^ 3) *
            reciprocalPhaseScale N M j X) →
      ‖reciprocalPhaseSum N M j c d‖ ≤ B) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      (((2 * (Finset.Icc 1 (vinogradovDerivativeCutoff X
          (reciprocalPhaseScale N M j X))).card + 1 : ℕ) : ℝ) * B) +
        ((Finset.Icc 1 (vinogradovDerivativeCutoff X
          (reciprocalPhaseScale N M j X))).card : ℝ) *
          (16 * X * (Real.log P) ^ (-3 * A) +
            vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X) + 1) := by
  let R := vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X)
  apply norm_reciprocalPhaseSum_le_expandedHullComponentEnvelope
    N M j (Finset.Icc 1 R) a b R hB hX
      (Real.rpow_nonneg (by linarith : 0 ≤ Real.log P) _) hM hj hpow
  intro c d hac hdb hwindow
  by_cases hcd : c < d
  · apply hvinogradov c d hac hdb hcd
    apply reciprocalPhase_vinogradov_derivative_bounds_of_sourceCutoff_forwardWindows
      N M P A hX hlog hA hten hcutoff (by omega) hcd
    · intro t ht
      constructor
      · calc
          X ≤ (a : ℝ) := hXa
          _ ≤ (c : ℝ) := by exact_mod_cast hac
          _ ≤ t := ht.1
      · calc
          t ≤ (d : ℝ) := ht.2
          _ ≤ (b : ℝ) := by exact_mod_cast hdb
          _ ≤ Y := hbY
    · exact hYtop
    · simpa only [R] using hwindow
  · have hdc : d ≤ c := Nat.le_of_not_gt hcd
    have hempty : Finset.Ico c d = ∅ := Finset.Ico_eq_empty hcd
    simpa [reciprocalPhaseSum, hempty] using hB

/-- Fixed-constant form of the global source Vinogradov consumer.  Keeping the
absolute constant explicit is essential when one subsequently chooses a
single eventual threshold uniform over all Type II pairs. -/
theorem norm_reciprocalPhaseSum_le_sourceVinogradov_componentEnvelopeAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (N M P A : ℝ) (j a b : ℕ) {X Y : ℝ}
    (hX : 2 ≤ X) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff X
      (reciprocalPhaseScale N M j X) + j : ℕ) : ℝ)) ≤ Real.log P)
    (hFhigh : X ^ 4 ≤ reciprocalPhaseScale N M j X)
    (hsmall : Real.log ((Real.log P) ^ (4 * A)) *
      (Real.log (reciprocalPhaseScale N M j X)) ^ 2 /
        (Real.log X) ^ 3 < (1 / 1000 : ℝ))
    (hXa : X ≤ (a : ℝ)) (hbY : (b : ℝ) ≤ Y) (hYtop : Y ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      (((2 * (Finset.Icc 1 (vinogradovDerivativeCutoff X
          (reciprocalPhaseScale N M j X))).card + 1 : ℕ) : ℝ) *
        (C * (Real.log P) ^ (4 * A) * X * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log (reciprocalPhaseScale N M j X)) ^ 2))) +
      ((Finset.Icc 1 (vinogradovDerivativeCutoff X
        (reciprocalPhaseScale N M j X))).card : ℝ) *
        (16 * X * (Real.log P) ^ (-3 * A) +
          vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X) + 1) := by
  obtain ⟨hC, hVinogradov⟩ := hVinogradov
  have hα : 1 ≤ (Real.log P) ^ (4 * A) := by
    obtain ⟨_, _, hα, _, _⟩ :=
      vinogradov_log_power_parameters hlog hA hcutoff hten
    exact hα
  apply norm_reciprocalPhaseSum_le_sourceVinogradov_componentEnvelope
    N M P A
      (C * (Real.log P) ^ (4 * A) * X * Real.exp
        (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
          (Real.log (reciprocalPhaseScale N M j X)) ^ 2))
      j a b (by positivity) (by linarith : 0 < X) hM hj hlog hA hten hcutoff
      hXa hbY hYtop hpow
  intro c d hac hdb _ hderiv
  apply hVinogradov X (reciprocalPhaseScale N M j X)
    ((Real.log P) ^ (4 * A)) c d (reciprocalPhase N M j)
    hX hFhigh hα hsmall
  · intro t ht
    constructor
    · calc
        X ≤ (a : ℝ) := hXa
        _ ≤ (c : ℝ) := by exact_mod_cast hac
        _ ≤ t := ht.1
    · calc
        t ≤ (d : ℝ) := ht.2
        _ ≤ (b : ℝ) := by exact_mod_cast hdb
        _ ≤ Y := hbY
        _ ≤ 2 * X := hYtop
  · intro t ht
    rw [contDiffAt_infty]
    intro r
    apply contDiffAt_reciprocalPhase_of_pos N M j r
    calc
      0 < X := by linarith
      _ ≤ (a : ℝ) := hXa
      _ ≤ (c : ℝ) := by exact_mod_cast hac
      _ ≤ t := ht.1
  · exact hderiv

/-- The exact source Vinogradov lemma implies the global reciprocal-phase
estimate with no residual local callback.  The conclusion exposes the one
absolute constant supplied by that lemma and retains the exact regular-piece
and critical-deletion costs. -/
theorem exists_norm_reciprocalPhaseSum_le_sourceVinogradov_componentEnvelope
    (hVinogradov : VinogradovExponentialSumEstimate)
    (N M P A : ℝ) (j a b : ℕ) {X Y : ℝ}
    (hX : 2 ≤ X) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff X
      (reciprocalPhaseScale N M j X) + j : ℕ) : ℝ)) ≤ Real.log P)
    (hFhigh : X ^ 4 ≤ reciprocalPhaseScale N M j X)
    (hsmall : Real.log ((Real.log P) ^ (4 * A)) *
      (Real.log (reciprocalPhaseScale N M j X)) ^ 2 /
        (Real.log X) ^ 3 < (1 / 1000 : ℝ))
    (hXa : X ≤ (a : ℝ)) (hbY : (b : ℝ) ≤ Y) (hYtop : Y ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    ∃ C : ℝ, 0 < C ∧
      ‖reciprocalPhaseSum N M j a b‖ ≤
        (((2 * (Finset.Icc 1 (vinogradovDerivativeCutoff X
            (reciprocalPhaseScale N M j X))).card + 1 : ℕ) : ℝ) *
          (C * (Real.log P) ^ (4 * A) * X * Real.exp
            (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
              (Real.log (reciprocalPhaseScale N M j X)) ^ 2))) +
        ((Finset.Icc 1 (vinogradovDerivativeCutoff X
          (reciprocalPhaseScale N M j X))).card : ℝ) *
          (16 * X * (Real.log P) ^ (-3 * A) +
            vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X) + 1) := by
  obtain ⟨C, hC, hVinogradov⟩ := hVinogradov
  refine ⟨C, hC, ?_⟩
  have hα : 1 ≤ (Real.log P) ^ (4 * A) := by
    obtain ⟨_, _, hα, _, _⟩ :=
      vinogradov_log_power_parameters hlog hA hcutoff hten
    exact hα
  apply norm_reciprocalPhaseSum_le_sourceVinogradov_componentEnvelope
    N M P A
      (C * (Real.log P) ^ (4 * A) * X * Real.exp
        (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
          (Real.log (reciprocalPhaseScale N M j X)) ^ 2))
      j a b (by positivity) (by linarith : 0 < X) hM hj hlog hA hten hcutoff
      hXa hbY hYtop hpow
  intro c d hac hdb _ hderiv
  apply hVinogradov X (reciprocalPhaseScale N M j X)
    ((Real.log P) ^ (4 * A)) c d (reciprocalPhase N M j)
    hX hFhigh hα hsmall
  · intro t ht
    constructor
    · calc
        X ≤ (a : ℝ) := hXa
        _ ≤ (c : ℝ) := by exact_mod_cast hac
        _ ≤ t := ht.1
    · calc
        t ≤ (d : ℝ) := ht.2
        _ ≤ (b : ℝ) := by exact_mod_cast hdb
        _ ≤ Y := hbY
        _ ≤ 2 * X := hYtop
  · intro t ht
    rw [contDiffAt_infty]
    intro r
    apply contDiffAt_reciprocalPhase_of_pos N M j r
    calc
      0 < X := by linarith
      _ ≤ (a : ℝ) := hXa
      _ ≤ (c : ℝ) := by exact_mod_cast hac
      _ ≤ t := ht.1
  · exact hderiv

/-- Fixed-constant logarithmic simplification of the exact component envelope.
This is the uniform form used after selecting the single absolute constant in
`VinogradovExponentialSumEstimate`. -/
theorem norm_reciprocalPhaseSum_le_sourceVinogradov_logEnvelopeAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (N M P A : ℝ) (j a b : ℕ) {X Y : ℝ}
    (hX : 2 ≤ X) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff X
      (reciprocalPhaseScale N M j X) + j : ℕ) : ℝ)) ≤ Real.log P)
    (hFhigh : X ^ 4 ≤ reciprocalPhaseScale N M j X)
    (hsmall : Real.log ((Real.log P) ^ (4 * A)) *
      (Real.log (reciprocalPhaseScale N M j X)) ^ 2 /
        (Real.log X) ^ 3 < (1 / 1000 : ℝ))
    (hXa : X ≤ (a : ℝ)) (hbY : (b : ℝ) ≤ Y) (hYtop : Y ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    ‖reciprocalPhaseSum N M j a b‖ ≤
      (2 * Real.log P + 1) *
        (C * (Real.log P) ^ (4 * A) * X * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
            (Real.log (reciprocalPhaseScale N M j X)) ^ 2)) +
      Real.log P *
        (16 * X * (Real.log P) ^ (-3 * A) + Real.log P + 1) := by
  have hraw := norm_reciprocalPhaseSum_le_sourceVinogradov_componentEnvelopeAt
    C hVinogradov N M P A j a b hX hM hj hlog hA hten hcutoff hFhigh
      hsmall hXa hbY hYtop hpow
  let R := vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X)
  have hRlog : (R : ℝ) ≤ Real.log P := by
    calc
      (R : ℝ) ≤ ((R + j : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_right R j
      _ ≤ Real.log P := by simpa only [R] using hcutoff
  have hlog0 : 0 ≤ Real.log P := zero_le_one.trans hlog
  have hmain : 0 ≤ C * (Real.log P) ^ (4 * A) * X * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log (reciprocalPhaseScale N M j X)) ^ 2) := by
    obtain ⟨hC, _⟩ := hVinogradov
    positivity
  have hdelete : 0 ≤ 16 * X * (Real.log P) ^ (-3 * A) := by positivity
  simp only [Nat.card_Icc] at hraw ⊢
  push_cast at hraw ⊢
  nlinarith

/-- Logarithmic simplification of the exact component envelope.  Once the
shifted cutoff satisfies `R+j≤log P`, both the number of regular components
and the critical-deletion multiplicity are bounded by `log P`.  This is the
form used to absorb the complete high-scale estimate into a uniform
logarithmic error. -/
theorem exists_norm_reciprocalPhaseSum_le_sourceVinogradov_logEnvelope
    (hVinogradov : VinogradovExponentialSumEstimate)
    (N M P A : ℝ) (j a b : ℕ) {X Y : ℝ}
    (hX : 2 ≤ X) (hM : M ≠ 0) (hj : 2 ≤ j)
    (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff X
      (reciprocalPhaseScale N M j X) + j : ℕ) : ℝ)) ≤ Real.log P)
    (hFhigh : X ^ 4 ≤ reciprocalPhaseScale N M j X)
    (hsmall : Real.log ((Real.log P) ^ (4 * A)) *
      (Real.log (reciprocalPhaseScale N M j X)) ^ 2 /
        (Real.log X) ^ 3 < (1 / 1000 : ℝ))
    (hXa : X ≤ (a : ℝ)) (hbY : (b : ℝ) ≤ Y) (hYtop : Y ≤ 2 * X)
    (hpow : ∀ t ∈ Set.Icc X Y, t ^ (j - 1) ≤ 2 * X ^ (j - 1)) :
    ∃ C : ℝ, 0 < C ∧
      ‖reciprocalPhaseSum N M j a b‖ ≤
        (2 * Real.log P + 1) *
          (C * (Real.log P) ^ (4 * A) * X * Real.exp
            (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
              (Real.log (reciprocalPhaseScale N M j X)) ^ 2)) +
        Real.log P *
          (16 * X * (Real.log P) ^ (-3 * A) + Real.log P + 1) := by
  obtain ⟨C, hC, hraw⟩ :=
    exists_norm_reciprocalPhaseSum_le_sourceVinogradov_componentEnvelope
      hVinogradov N M P A j a b hX hM hj hlog hA hten hcutoff hFhigh
        hsmall hXa hbY hYtop hpow
  refine ⟨C, hC, hraw.trans ?_⟩
  let R := vinogradovDerivativeCutoff X (reciprocalPhaseScale N M j X)
  have hRlog : (R : ℝ) ≤ Real.log P := by
    calc
      (R : ℝ) ≤ ((R + j : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_right R j
      _ ≤ Real.log P := by simpa only [R] using hcutoff
  have hlog0 : 0 ≤ Real.log P := zero_le_one.trans hlog
  have hmain : 0 ≤ C * (Real.log P) ^ (4 * A) * X * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log X) ^ 3 /
        (Real.log (reciprocalPhaseScale N M j X)) ^ 2) := by
    positivity
  have hdelete : 0 ≤ 16 * X * (Real.log P) ^ (-3 * A) := by
    positivity
  simp only [Nat.card_Icc] at hraw ⊢
  push_cast at hraw ⊢
  nlinarith

/-- High transformed-scale Type II correlations are exact consumers of the
source Vinogradov proposition.  The product-restricted support is rewritten as
its ceiling-divided integer interval; its endpoints are discharged from the
short-block geometry, and the conclusion retains the explicit
critical-deletion cost. -/
theorem exists_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov
    (hVinogradov : VinogradovExponentialSumEstimate)
    (a b K₀ K₁ q k : ℕ) (N P A K : ℝ)
    {n n' : ℕ}
    (hKouter : K = ((K₀ + k * q : ℕ) : ℝ))
    (hK : 2 ≤ K) (hq : 0 < q) (hqK : (q : ℝ) ≤ K)
    (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n') (hN : N ≠ 0)
    (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff K
      (reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K) + 2 : ℕ) : ℝ)) ≤
          Real.log P)
    (hFhigh : K ^ 4 ≤ reciprocalPhaseScale
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter N 2 n n') 2 K)
    (hsmall : Real.log ((Real.log P) ^ (4 * A)) *
      (Real.log (reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K)) ^ 2 /
          (Real.log K) ^ 3 < (1 / 1000 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N N 2 n n'‖ ≤
        (((2 * (Finset.Icc 1 (vinogradovDerivativeCutoff K
            (reciprocalPhaseScale
              (typeIICorrelationLinearParameter N n n')
              (typeIICorrelationHigherParameter N 2 n n') 2 K))).card + 1 : ℕ) : ℝ) *
          (C * (Real.log P) ^ (4 * A) * K * Real.exp
            (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log K) ^ 3 /
              (Real.log (reciprocalPhaseScale
                (typeIICorrelationLinearParameter N n n')
                (typeIICorrelationHigherParameter N 2 n n') 2 K)) ^ 2))) +
        ((Finset.Icc 1 (vinogradovDerivativeCutoff K
          (reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K))).card : ℝ) *
          (16 * K * (Real.log P) ^ (-3 * A) +
            vinogradovDerivativeCutoff K
              (reciprocalPhaseScale
                (typeIICorrelationLinearParameter N n n')
                (typeIICorrelationHigherParameter N 2 n n') 2 K) + 1) := by
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter N 2 n n'
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  have hM' : M' ≠ 0 := by
    exact typeIICorrelationHigherParameter_ne_zero hN (by norm_num)
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hloNat : K₀ + k * q ≤ lo := by
    exact le_max_left _ _
  have hlo : K ≤ (lo : ℝ) := by
    rw [hKouter]
    exact_mod_cast hloNat
  have hhiNat : hi ≤ K₀ + (k + 1) * q := by
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hhi : (hi : ℝ) ≤ 2 * K := by
    calc
      (hi : ℝ) ≤ ((K₀ + (k + 1) * q : ℕ) : ℝ) := by exact_mod_cast hhiNat
      _ = K + (q : ℝ) := by
        rw [hKouter]
        push_cast
        ring
      _ ≤ 2 * K := by linarith
  have hpow : ∀ t ∈ Set.Icc K (2 * K),
      t ^ (2 - 1) ≤ 2 * K ^ (2 - 1) := by
    intro t ht
    norm_num
    exact ht.2
  have hglobal :=
    exists_norm_reciprocalPhaseSum_le_sourceVinogradov_componentEnvelope
      hVinogradov N' M' P A 2 lo hi hK hM' (by norm_num) hlog hA hten
        (by simpa only [N', M'] using hcutoff)
        (by simpa only [N', M'] using hFhigh)
        (by simpa only [N', M'] using hsmall)
        hlo hhi le_rfl hpow
  rw [typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
    a b K₀ K₁ q k N N 2 hq hn hn']
  simpa only [N', M', typeIICorrelationLinearParameter,
    typeIICorrelationHigherParameter] using hglobal

/-- Fixed-constant logarithmic-envelope form of the exact high-pair Type II
consumer.  This is the pointwise interface used to build one uniform eventual
high-pair callback. -/
theorem norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_logEnvelopeAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (a b K₀ K₁ q k : ℕ) (N P A K : ℝ)
    {n n' : ℕ}
    (hKouter : K = ((K₀ + k * q : ℕ) : ℝ))
    (hK : 2 ≤ K) (hq : 0 < q) (hqK : (q : ℝ) ≤ K)
    (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n') (hN : N ≠ 0)
    (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff K
      (reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K) + 2 : ℕ) : ℝ)) ≤
          Real.log P)
    (hFhigh : K ^ 4 ≤ reciprocalPhaseScale
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter N 2 n n') 2 K)
    (hsmall : Real.log ((Real.log P) ^ (4 * A)) *
      (Real.log (reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K)) ^ 2 /
          (Real.log K) ^ 3 < (1 / 1000 : ℝ)) :
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
      (shortIntervalBlock K₀ K₁ q k) N N 2 n n'‖ ≤
      (2 * Real.log P + 1) *
        (C * (Real.log P) ^ (4 * A) * K * Real.exp
          (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log K) ^ 3 /
            (Real.log (reciprocalPhaseScale
              (typeIICorrelationLinearParameter N n n')
              (typeIICorrelationHigherParameter N 2 n n') 2 K)) ^ 2)) +
      Real.log P *
        (16 * K * (Real.log P) ^ (-3 * A) + Real.log P + 1) := by
  let N' := typeIICorrelationLinearParameter N n n'
  let M' := typeIICorrelationHigherParameter N 2 n n'
  let lo := typeIIProductRestrictedBlockLower a K₀ q k n n'
  let hi := typeIIProductRestrictedBlockUpper b K₀ K₁ q k n n'
  have hM' : M' ≠ 0 := by
    exact typeIICorrelationHigherParameter_ne_zero hN (by norm_num)
      (Nat.ne_of_gt hn) (Nat.ne_of_gt hn') hne
  have hloNat : K₀ + k * q ≤ lo := le_max_left _ _
  have hlo : K ≤ (lo : ℝ) := by
    rw [hKouter]
    exact_mod_cast hloNat
  have hhiNat : hi ≤ K₀ + (k + 1) * q :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hhi : (hi : ℝ) ≤ 2 * K := by
    calc
      (hi : ℝ) ≤ ((K₀ + (k + 1) * q : ℕ) : ℝ) := by exact_mod_cast hhiNat
      _ = K + (q : ℝ) := by
        rw [hKouter]
        push_cast
        ring
      _ ≤ 2 * K := by linarith
  have hpow : ∀ t ∈ Set.Icc K (2 * K),
      t ^ (2 - 1) ≤ 2 * K ^ (2 - 1) := by
    intro t ht
    norm_num
    exact ht.2
  have hglobal := norm_reciprocalPhaseSum_le_sourceVinogradov_logEnvelopeAt
    C hVinogradov N' M' P A 2 lo hi hK hM' (by norm_num) hlog hA hten
      (by simpa only [N', M'] using hcutoff)
      (by simpa only [N', M'] using hFhigh)
      (by simpa only [N', M'] using hsmall)
      hlo hhi le_rfl hpow
  rw [typeIIProductRestrictedCorrelationSum_shortIntervalBlock_eq
    a b K₀ K₁ q k N N 2 hq hn hn']
  simpa only [N', M', typeIICorrelationLinearParameter,
    typeIICorrelationHigherParameter] using hglobal

/-- Uniform high-pair logarithmic saving supplied by the source Vinogradov
proposition.  One absolute Vinogradov constant and one eventual threshold work
for every product-restricted short-block correlation satisfying the primitive
transformed-scale upper bound and the logarithmic lower bound on `K`. -/
theorem eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_logSaving
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A C₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b K₀ K₁ q k : ℕ) (N K : ℝ) (n n' : ℕ),
        K = ((K₀ + k * q : ℕ) : ℝ) →
        2 ≤ K → 0 < q → (q : ℝ) ≤ K →
        0 < n → 0 < n' → n ≠ n' → N ≠ 0 →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K ≤
          C₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log K →
        K ^ 4 ≤ reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K →
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N N 2 n n'‖ ≤
            3 * K * (Real.log P) ^ (-T) := by
  obtain ⟨C₁, hVinogradovAt⟩ := hVinogradov
  have hC₁ : 0 < C₁ := hVinogradovAt.1
  have hparameters :=
    eventually_sourceVinogradov_quadraticParameterConditions_of_parameterBound
      hA hC₀ hc hε ha
  have henvelope := eventually_sourceVinogradov_logEnvelope_le
    hC₀ hC₁ hc hε ha hAT
  filter_upwards [hparameters, henvelope] with P hparametersP henvelopeP
  intro a b K₀ K₁ q k N K n n' hKouter hK hq hqK hn hn' hne hN
    hFupper hKlower hFhigh
  let F := reciprocalPhaseScale
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter N 2 n n') 2 K
  obtain ⟨hlog, hten, hcutoff, hsmall⟩ :=
    hparametersP K F hK (by simpa only [F] using hFhigh)
      (by simpa only [F] using hFupper) hKlower
  have hraw :=
    norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_logEnvelopeAt
      C₁ hVinogradovAt a b K₀ K₁ q k N P A K hKouter hK hq hqK hn hn'
        hne hN hlog hA hten
        (by simpa only [F] using hcutoff)
        (by simpa only [F] using hFhigh)
        (by simpa only [F] using hsmall)
  exact hraw.trans
    (henvelopeP K F hK (by simpa only [F] using hFhigh)
      (by simpa only [F] using hFupper) hKlower)

/-- Kernel-callback form of the uniform high-pair Vinogradov saving.  The
canonical Type II prefactor dominates `K`, so the pure logarithmic estimate
slots directly into the mixed Weyl--Vinogradov callback with
`V=3(log P)^(-T)`. -/
theorem eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_kernelCallback
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A C₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hC₀ : 0 < C₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b K₀ K₁ q k : ℕ) (N K : ℝ) (n n' : ℕ)
        (orders : Finset ℕ) (B F : ℝ),
        K = ((K₀ + k * q : ℕ) : ℝ) →
        2 ≤ K → 0 < q → (q : ℝ) ≤ K →
        0 < n → 0 < n' → n ≠ n' → N ≠ 0 →
        0 < B → 0 ≤ F →
        reciprocalPhaseScale
            (typeIICorrelationLinearParameter N n n')
            (typeIICorrelationHigherParameter N 2 n n') 2 K ≤
          C₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log K →
        K ^ 4 ≤ reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K →
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (q : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
            3 * (Real.log P) ^ (-T)) := by
  have hsaving :=
    eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_logSaving
      hVinogradov hA hC₀ hc hε ha hAT
  filter_upwards [hsaving,
    Real.tendsto_log_atTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))]
      with P hsavingP hlog
  intro a b K₀ K₁ q k N K n n' orders B F hKouter hK hq hqK hn hn' hne
    hN hB hF hFupper hKlower hFhigh
  dsimp only
  have hnorm := hsavingP a b K₀ K₁ q k N K n n' hKouter hK hq hqK hn hn'
    hne hN hFupper hKlower hFhigh
  let Ccount : ℝ := ((370 * orders.card + 173 : ℕ) : ℝ)
  let J : ℝ := ((((5 + 2) ^ 5 : ℕ) : ℝ))
  let Q : ℝ := Ccount *
    (480 * J * ((J + 1) * (1 + Real.log (q : ℝ))) * K)
  let V : ℝ := 3 * (Real.log P) ^ (-T)
  have hqOne : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hqOne
  have hCcount : 1 ≤ Ccount := by
    unfold Ccount
    exact_mod_cast (by omega : 1 ≤ 370 * orders.card + 173)
  have hJ : 1 ≤ J := by unfold J; norm_num
  have h480J : 1 ≤ 480 * J :=
    one_le_mul_of_one_le_of_one_le (by norm_num) hJ
  have hJplus : 1 ≤ J + 1 := by linarith
  have hlogFactor : 1 ≤ 1 + Real.log (q : ℝ) := by linarith
  have htail : 1 ≤ (J + 1) * (1 + Real.log (q : ℝ)) :=
    one_le_mul_of_one_le_of_one_le hJplus hlogFactor
  have hmiddle : 1 ≤ 480 * J *
      ((J + 1) * (1 + Real.log (q : ℝ))) :=
    one_le_mul_of_one_le_of_one_le h480J htail
  have hcoefficient : 1 ≤ Ccount *
      (480 * J * ((J + 1) * (1 + Real.log (q : ℝ)))) :=
    one_le_mul_of_one_le_of_one_le hCcount hmiddle
  have hKQ : K ≤ Q := by
    have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 2).trans hK
    have hmul := mul_le_mul_of_nonneg_right hcoefficient hK0
    calc
      K = 1 * K := by ring
      _ ≤ (Ccount * (480 * J *
          ((J + 1) * (1 + Real.log (q : ℝ))))) * K := hmul
      _ = Q := by unfold Q; ring
  have hQ0 : 0 ≤ Q :=
    ((by norm_num : (0 : ℝ) ≤ 2).trans hK).trans hKQ
  have hV0 : 0 ≤ V := by unfold V; positivity
  have hkernel := typeIIDecayKernel_nonneg
    (1 / 1024 : ℝ) (Nat.dist n' n) hB hF
  calc
    ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N N 2 n n'‖ ≤
        3 * K * (Real.log P) ^ (-T) := hnorm
    _ = K * V := by unfold V; ring
    _ ≤ Q * V := mul_le_mul_of_nonneg_right hKQ hV0
    _ ≤ Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ)
        (Nat.dist n' n) + V) := by
          gcongr
          nlinarith
    _ = ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
            (1 + Real.log (q : ℝ)) * K) *
        (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
          3 * (Real.log P) ^ (-T)) := by
            unfold Q V Ccount J
            ring

/-- Canonical Vaughan-inner-block specialization of the uniform high-pair
callback.  Membership in the inner dyadic block now discharges the primitive
upper bound for the transformed pair scale with the exact quadratic factor
`5`; only the source bound on `N`, the logarithmic lower bound on `K`, and the
high-scale split remain visible. -/
theorem eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_vaughanInnerBlockCallback
    (hVinogradov : VinogradovExponentialSumEstimate)
    {A A₀ c ε T : ℝ} (hA : 1 / 4 ≤ A) (hA₀ : 0 < A₀) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ P : ℝ in Filter.atTop,
      ∀ (a b Bcap K₀ K₁ q k : ℕ) (N K : ℝ) (n n' : ℕ)
        (orders : Finset ℕ) (B F : ℝ) (tl : ℕ × ℕ),
        K = ((K₀ + k * q : ℕ) : ℝ) →
        2 ≤ K → 0 < q → (q : ℝ) ≤ K →
        n ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl →
        n' ∈ dyadicShortIntervalIndexedBlock
          (vaughanShortIntervalBudget Bcap) tl →
        0 < n → 0 < n' → n ≠ n' → N ≠ 0 →
        0 < B → 0 ≤ F →
        |N| ≤ A₀ * Real.exp ((Real.log P) ^ (3 / 2 - ε)) →
        c * Real.log P ≤ Real.log K →
        K ^ 4 ≤ reciprocalPhaseScale
          (typeIICorrelationLinearParameter N n n')
          (typeIICorrelationHigherParameter N 2 n n') 2 K →
        let Q := ((370 * orders.card + 173 : ℕ) : ℝ) *
          (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
              (1 + Real.log (q : ℝ)) * K)
        ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
          (shortIntervalBlock K₀ K₁ q k) N N 2 n n'‖ ≤
          Q * (4 * typeIIDecayKernel B F (1 / 1024 : ℝ) (Nat.dist n' n) +
            3 * (Real.log P) ^ (-T)) := by
  have hcallback :=
    eventually_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_kernelCallback
      hVinogradov hA (show 0 < 5 * A₀ by positivity) hc hε ha hAT
  filter_upwards [hcallback] with P hcallbackP
  intro a b Bcap K₀ K₁ q k N K n n' orders B F tl hKouter hK hq hqK
    hnBlock hn'Block hn hn' hne hN hB hF hNupper hKlower hFhigh
  have hFupper :=
    reciprocalPhaseScale_typeIICorrelation_le_exp_of_vaughanBlock_quadratic
      Bcap N K P A₀ (3 / 2 - ε) (tl := tl) (n := n) (n' := n')
        (by linarith : 1 ≤ K) hnBlock hn'Block hA₀.le hNupper
  exact hcallbackP a b K₀ K₁ q k N K n n' orders B F hKouter hK hq hqK
    hn hn' hne hN hB hF hFupper hKlower hFhigh

/-- Logarithmic-envelope form of the exact high-pair Type II consumer.  The
raw regular-component count and critical-deletion multiplicity have both been
replaced by `log P`, leaving an expression ready for the uniform logarithmic
absorption lemmas. -/
theorem exists_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov_logEnvelope
    (hVinogradov : VinogradovExponentialSumEstimate)
    (a b K₀ K₁ q k : ℕ) (N P A K : ℝ)
    {n n' : ℕ}
    (hKouter : K = ((K₀ + k * q : ℕ) : ℝ))
    (hK : 2 ≤ K) (hq : 0 < q) (hqK : (q : ℝ) ≤ K)
    (hn : 0 < n) (hn' : 0 < n') (hne : n ≠ n') (hN : N ≠ 0)
    (hlog : 1 ≤ Real.log P) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log P) ^ A)
    (hcutoff : (((vinogradovDerivativeCutoff K
      (reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K) + 2 : ℕ) : ℝ)) ≤
          Real.log P)
    (hFhigh : K ^ 4 ≤ reciprocalPhaseScale
      (typeIICorrelationLinearParameter N n n')
      (typeIICorrelationHigherParameter N 2 n n') 2 K)
    (hsmall : Real.log ((Real.log P) ^ (4 * A)) *
      (Real.log (reciprocalPhaseScale
        (typeIICorrelationLinearParameter N n n')
        (typeIICorrelationHigherParameter N 2 n n') 2 K)) ^ 2 /
          (Real.log K) ^ 3 < (1 / 1000 : ℝ)) :
    ∃ C : ℝ, 0 < C ∧
      ‖typeIIProductRestrictedCorrelationSum (Finset.Ico a b)
        (shortIntervalBlock K₀ K₁ q k) N N 2 n n'‖ ≤
        (2 * Real.log P + 1) *
          (C * (Real.log P) ^ (4 * A) * K * Real.exp
            (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log K) ^ 3 /
              (Real.log (reciprocalPhaseScale
                (typeIICorrelationLinearParameter N n n')
                (typeIICorrelationHigherParameter N 2 n n') 2 K)) ^ 2)) +
        Real.log P *
          (16 * K * (Real.log P) ^ (-3 * A) + Real.log P + 1) := by
  obtain ⟨C, hC, hraw⟩ :=
    exists_norm_typeIIProductRestrictedCorrelationSum_le_sourceVinogradov
      hVinogradov a b K₀ K₁ q k N P A K hKouter hK hq hqK hn hn' hne hN
        hlog hA hten hcutoff hFhigh hsmall
  refine ⟨C, hC, hraw.trans ?_⟩
  let F := reciprocalPhaseScale
    (typeIICorrelationLinearParameter N n n')
    (typeIICorrelationHigherParameter N 2 n n') 2 K
  let R := vinogradovDerivativeCutoff K F
  have hRlog : (R : ℝ) ≤ Real.log P := by
    calc
      (R : ℝ) ≤ ((R + 2 : ℕ) : ℝ) := by
        exact_mod_cast Nat.le_add_right R 2
      _ ≤ Real.log P := by simpa only [R, F] using hcutoff
  have hlog0 : 0 ≤ Real.log P := zero_le_one.trans hlog
  have hmain : 0 ≤ C * (Real.log P) ^ (4 * A) * K * Real.exp
      (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log K) ^ 3 /
        (Real.log F) ^ 2) := by
    positivity
  have hdelete : 0 ≤ 16 * K * (Real.log P) ^ (-3 * A) := by
    positivity
  simp only [Nat.card_Icc] at hraw ⊢
  push_cast at hraw ⊢
  nlinarith

end Tao2026
