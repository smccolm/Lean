import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import RiemannZeta.GuthMaynard.HughesYoungGCD

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Hughes--Young height cleaning

This file begins the source step represented by Hughes--Young equations
(59)--(70).  For a fixed Mellin ordinate, the entire height dependence is
packaged as a compactly supported Fourier input.  Its Fourier transform is
proved smooth from Mathlib's differentiation theorem, rather than assumed.
-/

/-- Deligne's real Gamma factor is continuous when the height variable moves
on a vertical line in the open right half-plane. -/
theorem continuous_GammaR_afe_height (c u : ℝ)
    (hc : 0 < 1 / 2 + c) :
    Continuous (fun t : ℝ =>
      Complex.Gammaℝ
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) := by
  let s : ℝ → ℂ := fun t =>
    afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)
  have hs : Continuous s := by
    dsimp [s, afeCriticalPoint]
    fun_prop
  rw [continuous_iff_continuousAt]
  intro t
  unfold Complex.Gammaℝ
  apply ContinuousAt.mul
  · exact (continuousAt_const_cpow
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).comp
        ((hs.neg.div_const 2).continuousAt)
  · apply (Complex.continuousAt_Gamma _ ?_).comp
    · exact (hs.div_const 2).continuousAt
    · intro m hm
      have hre := congrArg Complex.re hm
      simp [afeCriticalPoint] at hre
      linarith

/-- The same vertical-line Gamma factor is smooth to every real order. -/
theorem contDiff_GammaR_afe_height (c u : ℝ)
    (hc : 0 < 1 / 2 + c) :
    ContDiff ℝ ∞ (fun t : ℝ =>
      Complex.Gammaℝ
        (afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I))) := by
  let s : ℝ → ℂ := fun t =>
    afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I)
  have hs : ContDiff ℝ ∞ s := by
    dsimp [s, afeCriticalPoint]
    exact (contDiff_const.add
      (Complex.ofRealCLM.contDiff.mul contDiff_const)).add contDiff_const
  let S : Set ℂ := {z | 0 < z.re}
  have hSopen : IsOpen S := by
    dsimp [S]
    exact isOpen_lt continuous_const continuous_re
  have hGammaDiff : DifferentiableOn ℂ Complex.Gamma S := by
    intro z hz
    apply (Complex.differentiableAt_Gamma z ?_).differentiableWithinAt
    intro m hm
    have hre := congrArg Complex.re hm
    simp [S] at hz
    simp at hre
    linarith
  have hGammaAnalytic : AnalyticOnNhd ℂ Complex.Gamma S :=
    hGammaDiff.analyticOnNhd hSopen
  letI : NeZero (Real.pi : ℂ) :=
    ⟨Complex.ofReal_ne_zero.mpr Real.pi_ne_zero⟩
  have hPiDiff : Differentiable ℂ (fun z : ℂ => (Real.pi : ℂ) ^ z) :=
    differentiable_const_cpow_of_neZero (Real.pi : ℂ)
  rw [contDiff_iff_contDiffAt]
  intro t
  unfold Complex.Gammaℝ
  have hz : s t / 2 ∈ S := by
    simp [S, s, afeCriticalPoint]
    linarith
  have hpowAt : ContDiffAt ℝ ∞
      (fun z : ℂ => (Real.pi : ℂ) ^ z) (-s t / 2) :=
    ((hPiDiff.analyticAt (-s t / 2)).restrictScalars).contDiffAt
  have hgammaAt : ContDiffAt ℝ ∞ Complex.Gamma (s t / 2) :=
    ((hGammaAnalytic (s t / 2) hz).restrictScalars).contDiffAt
  exact (hpowAt.comp t (hs.neg.div_const 2).contDiffAt).mul
    (hgammaAt.comp t (hs.div_const 2).contDiffAt)

theorem continuous_afePoleNormalization :
    Continuous afePoleNormalization := by
  unfold afePoleNormalization afeCriticalPoint
  fun_prop

theorem contDiff_afePoleNormalization :
    ContDiff ℝ ∞ afePoleNormalization := by
  unfold afePoleNormalization afeCriticalPoint
  have ht : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) :=
    Complex.ofRealCLM.contDiff
  have hneg : ContDiff ℝ ∞ (fun t : ℝ => ((-t : ℝ) : ℂ)) :=
    ht.comp contDiff_neg
  have hplus : ContDiff ℝ ∞ (fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I) :=
    contDiff_const.add (ht.mul contDiff_const)
  have hminus : ContDiff ℝ ∞ (fun t : ℝ =>
      (1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I) :=
    contDiff_const.add (hneg.mul contDiff_const)
  exact (((hplus.mul (contDiff_const.sub hplus)).mul hminus).mul
    (contDiff_const.sub hminus)).pow 2

theorem continuous_afeGammaNormalization :
    Continuous afeGammaNormalization := by
  unfold afeGammaNormalization
  have hplus : Continuous (fun t : ℝ => Complex.Gammaℝ (afeCriticalPoint t)) := by
    simpa using continuous_GammaR_afe_height 0 0 (by norm_num)
  exact (hplus.pow 2).mul ((hplus.comp continuous_neg).pow 2)

theorem contDiff_afeGammaNormalization :
    ContDiff ℝ ∞ afeGammaNormalization := by
  unfold afeGammaNormalization
  have hplus : ContDiff ℝ ∞
      (fun t : ℝ => Complex.Gammaℝ (afeCriticalPoint t)) := by
    simpa using contDiff_GammaR_afe_height 0 0 (by norm_num)
  exact (hplus.pow 2).mul ((hplus.comp contDiff_neg).pow 2)

/-- The exact right-contour coefficient is continuous in the height
parameter.  Positivity of the right-line real part excludes every Gamma
pole, and the two normalizations are already known to be nonzero. -/
theorem continuous_hughesYoungRightContourWeight_height
    {c : ℝ} (hc : 0 < c) (u : ℝ) :
    Continuous (fun t : ℝ => hughesYoungRightContourWeight t c u) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let s₁ : ℝ → ℂ := fun t => afeCriticalPoint t + w
  let s₂ : ℝ → ℂ := fun t => afeCriticalPoint (-t) + w
  have hs₁ : Continuous s₁ := by
    dsimp [s₁, w, afeCriticalPoint]
    fun_prop
  have hs₂ : Continuous s₂ := by
    dsimp [s₂, w, afeCriticalPoint]
    fun_prop
  have hgamma₁ : Continuous (fun t => Complex.Gammaℝ (s₁ t)) := by
    simpa only [s₁, w] using
      continuous_GammaR_afe_height c u (by linarith)
  have hgamma₂ : Continuous (fun t => Complex.Gammaℝ (s₂ t)) := by
    simpa only [s₂, w] using
      (continuous_GammaR_afe_height c u (by linarith)).comp continuous_neg
  have hnum : Continuous (fun t : ℝ =>
      Complex.exp (100 * w ^ 2) *
        (s₁ t * (1 - s₁ t)) ^ 2 * (s₂ t * (1 - s₂ t)) ^ 2 *
        Complex.Gammaℝ (s₁ t) ^ 2 * Complex.Gammaℝ (s₂ t) ^ 2) := by
    exact ((((continuous_const.mul
      ((hs₁.mul (continuous_const.sub hs₁)).pow 2)).mul
      ((hs₂.mul (continuous_const.sub hs₂)).pow 2)).mul
      (hgamma₁.pow 2)).mul (hgamma₂.pow 2))
  have hw : Continuous (fun _t : ℝ => w) := continuous_const
  have hwne : ∀ t : ℝ, w ≠ 0 := by
    intro t hw0
    have hre := congrArg Complex.re hw0
    simp [w] at hre
    linarith
  have hweight := (((hnum.div₀ continuous_afePoleNormalization
      afePoleNormalization_ne_zero).div₀ hw hwne).div₀
        continuous_afeGammaNormalization afeGammaNormalization_ne_zero)
  simpa only [hughesYoungRightContourWeight, w, s₁, s₂] using hweight

/-- Joint continuity in the physical height and Mellin ordinate.  This is
the missing regularity input for applying Fubini on a compact Mellin strip
and the compact support of the Hughes--Young height cutoff. -/
theorem continuous_uncurry_hughesYoungRightContourWeight
    {c : ℝ} (hc : 0 < c) :
    Continuous (Function.uncurry
      (fun t u : ℝ => hughesYoungRightContourWeight t c u)) := by
  let w : ℝ × ℝ → ℂ := fun p => (c : ℂ) + (p.2 : ℂ) * I
  let s₁ : ℝ × ℝ → ℂ := fun p => afeCriticalPoint p.1 + w p
  let s₂ : ℝ × ℝ → ℂ := fun p => afeCriticalPoint (-p.1) + w p
  have hw : Continuous w := by
    dsimp [w]
    fun_prop
  have hs₁ : Continuous s₁ := by
    dsimp [s₁, w, afeCriticalPoint]
    fun_prop
  have hs₂ : Continuous s₂ := by
    dsimp [s₂, w, afeCriticalPoint]
    fun_prop
  have hgamma₁ : Continuous (fun p => Complex.Gammaℝ (s₁ p)) := by
    rw [continuous_iff_continuousAt]
    intro p
    unfold Complex.Gammaℝ
    apply ContinuousAt.mul
    · exact (continuousAt_const_cpow
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).comp
          ((hs₁.neg.div_const 2).continuousAt)
    · apply (Complex.continuousAt_Gamma _ ?_).comp
      · exact (hs₁.div_const 2).continuousAt
      · intro m hm
        have hre := congrArg Complex.re hm
        simp [s₁, w, afeCriticalPoint] at hre
        linarith
  have hgamma₂ : Continuous (fun p => Complex.Gammaℝ (s₂ p)) := by
    rw [continuous_iff_continuousAt]
    intro p
    unfold Complex.Gammaℝ
    apply ContinuousAt.mul
    · exact (continuousAt_const_cpow
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)).comp
          ((hs₂.neg.div_const 2).continuousAt)
    · apply (Complex.continuousAt_Gamma _ ?_).comp
      · exact (hs₂.div_const 2).continuousAt
      · intro m hm
        have hre := congrArg Complex.re hm
        simp [s₂, w, afeCriticalPoint] at hre
        linarith
  have hnum : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (100 * w p ^ 2) *
        (s₁ p * (1 - s₁ p)) ^ 2 * (s₂ p * (1 - s₂ p)) ^ 2 *
        Complex.Gammaℝ (s₁ p) ^ 2 * Complex.Gammaℝ (s₂ p) ^ 2) := by
    have hexp : Continuous (fun p : ℝ × ℝ =>
        Complex.exp (100 * w p ^ 2)) := by fun_prop
    have hpoly₁ : Continuous (fun p : ℝ × ℝ =>
        (s₁ p * (1 - s₁ p)) ^ 2) := by fun_prop
    have hpoly₂ : Continuous (fun p : ℝ × ℝ =>
        (s₂ p * (1 - s₂ p)) ^ 2) := by fun_prop
    exact (((hexp.mul hpoly₁).mul hpoly₂).mul
      (hgamma₁.pow 2)).mul (hgamma₂.pow 2)
  have hwne : ∀ p : ℝ × ℝ, w p ≠ 0 := by
    intro p hp
    have hre := congrArg Complex.re hp
    simp [w] at hre
    linarith
  have hpole : Continuous (fun p : ℝ × ℝ =>
      afePoleNormalization p.1) :=
    continuous_afePoleNormalization.comp continuous_fst
  have hgammaNorm : Continuous (fun p : ℝ × ℝ =>
      afeGammaNormalization p.1) :=
    continuous_afeGammaNormalization.comp continuous_fst
  have hdivPole : Continuous (fun p : ℝ × ℝ =>
      (Complex.exp (100 * w p ^ 2) *
        (s₁ p * (1 - s₁ p)) ^ 2 * (s₂ p * (1 - s₂ p)) ^ 2 *
        Complex.Gammaℝ (s₁ p) ^ 2 * Complex.Gammaℝ (s₂ p) ^ 2) /
        afePoleNormalization p.1) :=
    hnum.div₀ hpole (fun p => afePoleNormalization_ne_zero p.1)
  have hdivW : Continuous (fun p : ℝ × ℝ =>
      (Complex.exp (100 * w p ^ 2) *
        (s₁ p * (1 - s₁ p)) ^ 2 * (s₂ p * (1 - s₂ p)) ^ 2 *
        Complex.Gammaℝ (s₁ p) ^ 2 * Complex.Gammaℝ (s₂ p) ^ 2) /
        afePoleNormalization p.1 / w p) :=
    hdivPole.div₀ hw hwne
  have hweight := hdivW.div₀ hgammaNorm
    (fun p => afeGammaNormalization_ne_zero p.1)
  simpa only [Function.uncurry_apply_pair, hughesYoungRightContourWeight,
    w, s₁, s₂] using hweight

/-- Smoothness in height of the exact right-contour coefficient. -/
theorem contDiff_hughesYoungRightContourWeight_height
    {c : ℝ} (hc : 0 < c) (u : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => hughesYoungRightContourWeight t c u) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let s₁ : ℝ → ℂ := fun t => afeCriticalPoint t + w
  let s₂ : ℝ → ℂ := fun t => afeCriticalPoint (-t) + w
  have hs₁ : ContDiff ℝ ∞ s₁ := by
    dsimp [s₁, w, afeCriticalPoint]
    exact (contDiff_const.add
      (Complex.ofRealCLM.contDiff.mul contDiff_const)).add contDiff_const
  have hs₂ : ContDiff ℝ ∞ s₂ := by
    dsimp [s₂, w, afeCriticalPoint]
    have hneg : ContDiff ℝ ∞ (fun t : ℝ => ((-t : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_neg
    exact (contDiff_const.add (hneg.mul contDiff_const)).add contDiff_const
  have hgamma₁ : ContDiff ℝ ∞ (fun t => Complex.Gammaℝ (s₁ t)) := by
    simpa only [s₁, w] using
      contDiff_GammaR_afe_height c u (by linarith)
  have hgamma₂ : ContDiff ℝ ∞ (fun t => Complex.Gammaℝ (s₂ t)) := by
    simpa only [s₂, w] using
      (contDiff_GammaR_afe_height c u (by linarith)).comp contDiff_neg
  have hnum : ContDiff ℝ ∞ (fun t : ℝ =>
      Complex.exp (100 * w ^ 2) *
        (s₁ t * (1 - s₁ t)) ^ 2 * (s₂ t * (1 - s₂ t)) ^ 2 *
        Complex.Gammaℝ (s₁ t) ^ 2 * Complex.Gammaℝ (s₂ t) ^ 2) := by
    exact ((((contDiff_const.mul
      ((hs₁.mul (contDiff_const.sub hs₁)).pow 2)).mul
      ((hs₂.mul (contDiff_const.sub hs₂)).pow 2)).mul
      (hgamma₁.pow 2)).mul (hgamma₂.pow 2))
  have hw : ContDiff ℝ ∞ (fun _t : ℝ => w) := contDiff_const
  have hwne : ∀ t : ℝ, w ≠ 0 := by
    intro t hw0
    have hre := congrArg Complex.re hw0
    simp [w] at hre
    linarith
  have hweight := (((hnum.mul
      (contDiff_afePoleNormalization.inv afePoleNormalization_ne_zero)).mul
        (hw.inv hwne)).mul
          (contDiff_afeGammaNormalization.inv afeGammaNormalization_ne_zero))
  simpa only [hughesYoungRightContourWeight, w, s₁, s₂, div_eq_mul_inv,
    mul_assoc] using hweight

/-- The compactly supported height input whose Fourier variable is the
logarithmic ratio `log(y/x)`. -/
noncomputable def hughesYoungHeightFourierInput
    (T c u : ℝ) (t : ℝ) : ℂ :=
  (hughesYoungHeightWeight T t : ℂ) *
    hughesYoungRightContourWeight t c u

theorem continuous_hughesYoungHeightFourierInput
    (T : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ) :
    Continuous (hughesYoungHeightFourierInput T c u) := by
  unfold hughesYoungHeightFourierInput
  exact (Complex.ofRealCLM.continuous.comp
    (contDiff_hughesYoungHeightWeight T).continuous).mul
      (continuous_hughesYoungRightContourWeight_height hc u)

theorem contDiff_hughesYoungHeightFourierInput
    (T : ℝ) {c : ℝ} (hc : 0 < c) (u : ℝ) :
    ContDiff ℝ ∞ (hughesYoungHeightFourierInput T c u) := by
  unfold hughesYoungHeightFourierInput
  exact (Complex.ofRealCLM.contDiff.comp
    (contDiff_hughesYoungHeightWeight T)).mul
      (contDiff_hughesYoungRightContourWeight_height hc u)

theorem hasCompactSupport_hughesYoungHeightFourierInput
    {T : ℝ} (hT : 0 < T) (c u : ℝ) :
    HasCompactSupport (hughesYoungHeightFourierInput T c u) := by
  have hcutoffCompact : HasCompactSupport (hughesYoungCutoff : ℝ → ℝ) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      hughesYoungCutoff.support
  have hweightCompact : HasCompactSupport (hughesYoungHeightWeight T) := by
    simpa only [hughesYoungHeightWeight] using
      hcutoffCompact.comp_smul (inv_ne_zero hT.ne')
  have hcastCompact :
      HasCompactSupport (fun t : ℝ => (hughesYoungHeightWeight T t : ℂ)) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hweightCompact ⊢
    filter_upwards [hweightCompact] with t ht
    simp only [Pi.zero_apply] at ht ⊢
    rw [ht]
    norm_num
  unfold hughesYoungHeightFourierInput
  exact hcastCompact.mul_right

theorem integrable_heightFourierInput_moment
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (u : ℝ) (n : ℕ) :
    Integrable (fun t : ℝ => ‖t‖ ^ n *
      ‖hughesYoungHeightFourierInput T c u t‖) := by
  have hcont : Continuous (fun t : ℝ => ‖t‖ ^ n *
      ‖hughesYoungHeightFourierInput T c u t‖) :=
    (continuous_norm.pow n).mul
      (continuous_hughesYoungHeightFourierInput T hc u).norm
  apply hcont.integrable_of_hasCompactSupport
  apply HasCompactSupport.mul_left
  exact (hasCompactSupport_hughesYoungHeightFourierInput hT c u).norm

/-- Fourier transform of the height input in the exact phase normalization
`exp(i t ξ)`. -/
noncomputable def hughesYoungHeightTransform
    (T c u ξ : ℝ) : ℂ :=
  𝓕 (hughesYoungHeightFourierInput T c u)
    (-ξ / (2 * Real.pi))

theorem hughesYoungHeightTransform_eq_integral
    (T c u ξ : ℝ) :
    hughesYoungHeightTransform T c u ξ =
      ∫ t : ℝ, Complex.exp (((t * ξ : ℝ) : ℂ) * I) *
        hughesYoungHeightFourierInput T c u t := by
  rw [hughesYoungHeightTransform, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  simp only [smul_eq_mul]
  congr 2
  push_cast
  field_simp [Real.pi_ne_zero]

/-- Compact support of the height input gives a smooth Fourier transform of
all orders, exactly the analytic regularity used in Hughes--Young (65). -/
theorem contDiff_hughesYoungHeightTransform
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ) :
    ContDiff ℝ ∞ (hughesYoungHeightTransform T c u) := by
  have hfourier : ContDiff ℝ ∞
      (𝓕 (hughesYoungHeightFourierInput T c u)) :=
    Real.contDiff_fourier fun n _hn =>
      integrable_heightFourierInput_moment hT hc u n
  unfold hughesYoungHeightTransform
  exact hfourier.comp (by fun_prop)

/-- Every height derivative remains compactly supported.  This is the
boundary-term input for iterating Hughes--Young's integration by parts. -/
theorem hasCompactSupport_iteratedDeriv_hughesYoungHeightFourierInput
    {T : ℝ} (hT : 0 < T) (c u : ℝ) (n : ℕ) :
    HasCompactSupport
      (iteratedDeriv n (hughesYoungHeightFourierInput T c u)) := by
  induction n with
  | zero =>
      simpa using hasCompactSupport_hughesYoungHeightFourierInput hT c u
  | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- All derivatives of the compactly supported height input are integrable. -/
theorem integrable_iteratedDeriv_hughesYoungHeightFourierInput
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (u : ℝ) (n : ℕ) :
    Integrable (iteratedDeriv n (hughesYoungHeightFourierInput T c u)) := by
  have hcont : Continuous
      (iteratedDeriv n (hughesYoungHeightFourierInput T c u)) :=
    (contDiff_hughesYoungHeightFourierInput T hc u).continuous_iteratedDeriv n
      (WithTop.coe_le_coe.mpr (le_of_lt (ENat.coe_lt_top n)))
  exact hcont.integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv_hughesYoungHeightFourierInput hT c u n)

/-- Exact repeated-integration-by-parts estimate in the phase convention
`exp(i t ξ)`.  No factor of `2π` remains because the transform is evaluated
at `-ξ/(2π)`.  This is the kernel-checked Fourier form of Hughes--Young (65). -/
theorem abs_pow_mul_norm_hughesYoungHeightTransform_le
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (u ξ : ℝ) (j : ℕ) :
    |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ ≤
      ∫ t : ℝ,
        ‖iteratedDeriv j (hughesYoungHeightFourierInput T c u) t‖ := by
  let f : ℝ → ℂ := hughesYoungHeightFourierInput T c u
  have hf : ContDiff ℝ ∞ f :=
    contDiff_hughesYoungHeightFourierInput T hc u
  have hall : ∀ n : ℕ, n ≤ (⊤ : ℕ∞) →
      Integrable (iteratedDeriv n f) := by
    intro n _hn
    exact integrable_iteratedDeriv_hughesYoungHeightFourierInput hT hc u n
  have hjtop : j ≤ (⊤ : ℕ∞) := le_of_lt (ENat.coe_lt_top j)
  have hpoint := congrFun (Real.fourier_iteratedDeriv hf hall hjtop)
    (-ξ / (2 * Real.pi))
  have hnorm := congrArg norm hpoint
  have hfactor :
      ‖(2 * Real.pi * Complex.I * ((-ξ / (2 * Real.pi) : ℝ) : ℂ)) ^ j‖ =
        |ξ| ^ j := by
    have hinside :
        (2 * Real.pi * Complex.I * ((-ξ / (2 * Real.pi) : ℝ) : ℂ)) =
          -(ξ : ℂ) * Complex.I := by
      push_cast
      field_simp [Real.pi_ne_zero]
    rw [hinside, norm_pow, norm_mul]
    simp
  rw [norm_smul, hfactor] at hnorm
  calc
    |ξ| ^ j * ‖hughesYoungHeightTransform T c u ξ‖ =
        ‖𝓕 (iteratedDeriv j f) (-ξ / (2 * Real.pi))‖ := by
      rw [hnorm]
      rfl
    _ ≤ ∫ t : ℝ, ‖iteratedDeriv j f t‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        𝐞 MeasureTheory.volume (innerₗ ℝ)
        (iteratedDeriv j f) (-ξ / (2 * Real.pi))

/-! ## Exact separation of the height oscillation -/

/-- Split the positive-real logarithmic power into its height-free part and
the negative Fourier phase. -/
theorem hughesYoungLogPower_afeCriticalPoint_add
    (t : ℝ) (w : ℂ) (x : ℝ) :
    hughesYoungLogPower (afeCriticalPoint t + w) x =
      hughesYoungLogPower ((1 / 2 : ℂ) + w) x *
        Complex.exp (-((t : ℂ) * I) * (Real.log x : ℂ)) := by
  unfold hughesYoungLogPower afeCriticalPoint
  rw [← Complex.exp_add]
  congr 1
  ring

/-- The conjugate critical line contributes the opposite Fourier phase. -/
theorem hughesYoungLogPower_afeCriticalPoint_neg_add
    (t : ℝ) (w : ℂ) (x : ℝ) :
    hughesYoungLogPower (afeCriticalPoint (-t) + w) x =
      hughesYoungLogPower ((1 / 2 : ℂ) + w) x *
        Complex.exp (((t : ℂ) * I) * (Real.log x : ℂ)) := by
  unfold hughesYoungLogPower afeCriticalPoint
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The height-independent amplitude of one localized Hughes--Young Mellin
summand.  All oscillation in `t` has been removed from this expression. -/
noncomputable def hughesYoungLocalizedStaticWeight
    (T c u X Y : ℝ) (h k : ℕ) (x y : ℝ) : ℂ :=
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  shortMobiusSquareCoeff T h *
    hughesYoungLogPower (1 / 2 : ℂ) (h : ℝ) *
    shortMobiusSquareCoeff T k *
    hughesYoungLogPower (1 / 2 : ℂ) (k : ℝ) *
    (1 / (Real.pi : ℂ)) *
    (hughesYoungDyadicCutoffAt X x : ℂ) *
    (hughesYoungDyadicCutoffAt Y y : ℂ) *
    hughesYoungLogPower ((1 / 2 : ℂ) + w) (x / h) *
    hughesYoungLogPower ((1 / 2 : ℂ) + w) (y / k)

/-- The four elementary height phases combine to the single source phase
`exp(i t log(y/x))`. -/
theorem hughesYoung_combined_height_phase
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (t : ℝ) :
    Complex.exp (-((t : ℂ) * I) * (Real.log (h : ℝ) : ℂ)) *
        Complex.exp (((t : ℂ) * I) * (Real.log (k : ℝ) : ℂ)) *
        Complex.exp (-((t : ℂ) * I) * (Real.log (x / h) : ℂ)) *
        Complex.exp (((t : ℂ) * I) * (Real.log (y / k) : ℂ)) =
      Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hlogX : Real.log (x / h) = Real.log x - Real.log (h : ℝ) :=
    Real.log_div hx.ne' hhR.ne'
  have hlogY : Real.log (y / k) = Real.log y - Real.log (k : ℝ) :=
    Real.log_div hy.ne' hkR.ne'
  have hlogRatio : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div hy.ne' hx.ne'
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  rw [hlogX, hlogY, hlogRatio]
  congr 1
  push_cast
  ring

/-- Pointwise source identity behind Hughes--Young (65): after all four
critical-line powers are combined, the only height oscillation is the
Fourier character at `log(y/x)`. -/
theorem heightWeight_mul_hughesYoungLocalizedMellinWeight_eq_static_mul_phase
    (T t c u X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLocalizedMellinWeight T t c u X Y h k x y =
      hughesYoungLocalizedStaticWeight T c u X Y h k x y *
        Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
        hughesYoungHeightFourierInput T c u t := by
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hpowH : (h : ℂ) ^ (-afeCriticalPoint t) =
      hughesYoungLogPower (afeCriticalPoint t) (h : ℝ) := by
    simpa only [Complex.ofReal_natCast] using
      (hughesYoungLogPower_eq_cpow hhR (afeCriticalPoint t)).symm
  have hpowK : (k : ℂ) ^ (-afeCriticalPoint (-t)) =
      hughesYoungLogPower (afeCriticalPoint (-t)) (k : ℝ) := by
    simpa only [Complex.ofReal_natCast] using
      (hughesYoungLogPower_eq_cpow hkR (afeCriticalPoint (-t))).symm
  have hsplitH : hughesYoungLogPower (afeCriticalPoint t) (h : ℝ) =
      hughesYoungLogPower (1 / 2 : ℂ) (h : ℝ) *
        Complex.exp (-((t : ℂ) * I) * (Real.log (h : ℝ) : ℂ)) := by
    simpa using hughesYoungLogPower_afeCriticalPoint_add t 0 (h : ℝ)
  have hsplitK : hughesYoungLogPower (afeCriticalPoint (-t)) (k : ℝ) =
      hughesYoungLogPower (1 / 2 : ℂ) (k : ℝ) *
        Complex.exp (((t : ℂ) * I) * (Real.log (k : ℝ) : ℂ)) := by
    simpa using hughesYoungLogPower_afeCriticalPoint_neg_add t 0 (k : ℝ)
  rw [hughesYoungLocalizedMellinWeight]
  unfold hughesYoungMellinScalar hughesYoungLocalizedLogKernel
  rw [hpowH, hpowK, hsplitH, hsplitK,
    hughesYoungLogPower_afeCriticalPoint_add t
      ((c : ℂ) + (u : ℂ) * I),
    hughesYoungLogPower_afeCriticalPoint_neg_add t
      ((c : ℂ) + (u : ℂ) * I)]
  unfold hughesYoungLocalizedStaticWeight hughesYoungHeightFourierInput
  dsimp only
  rw [← hughesYoung_combined_height_phase hh hk hx hy t]
  ring

/-- Joint continuity of one localized source summand in the Mellin ordinate
and the physical height.  The coordinate order is `(u,t)`, matching the
product measure used in the subsequent interval-integral Fubini theorem. -/
theorem continuous_uncurry_hughesYoungLocalizedMellinWeight_ordinate_height
    (T : ℝ) {c : ℝ} (hc : 0 < c) (X Y : ℝ)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Continuous (fun p : ℝ × ℝ =>
      hughesYoungLocalizedMellinWeight T p.2 c p.1 X Y h k x y) := by
  let swap : ℝ × ℝ → ℝ × ℝ := fun p => (p.2, p.1)
  have hswap : Continuous swap := continuous_snd.prodMk continuous_fst
  have hright0 : Continuous (fun p : ℝ × ℝ =>
      Function.uncurry
        (fun t u : ℝ => hughesYoungRightContourWeight t c u) (swap p)) :=
    (continuous_uncurry_hughesYoungRightContourWeight hc).comp hswap
  have hright : Continuous (fun p : ℝ × ℝ =>
      hughesYoungRightContourWeight p.2 c p.1) := by
    simpa only [Function.uncurry_apply_pair, swap] using hright0
  have hhR : (0 : ℝ) < h := by exact_mod_cast hh
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hbaseX : (((x / h : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero hx.ne' hhR.ne')
  have hbaseY : (((y / k : ℝ) : ℂ)) ≠ 0 := by
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero hy.ne' hkR.ne')
  have hexpX : Continuous (fun p : ℝ × ℝ =>
      (((x / h : ℝ) : ℂ)) ^
        (-(afeCriticalPoint p.2 + ((c : ℂ) + (p.1 : ℂ) * I)))) := by
    have he : Continuous (fun p : ℝ × ℝ =>
        -(afeCriticalPoint p.2 + ((c : ℂ) + (p.1 : ℂ) * I))) := by
      unfold afeCriticalPoint
      fun_prop
    exact he.const_cpow (Or.inl hbaseX)
  have hexpY : Continuous (fun p : ℝ × ℝ =>
      (((y / k : ℝ) : ℂ)) ^
        (-(afeCriticalPoint (-p.2) + ((c : ℂ) + (p.1 : ℂ) * I)))) := by
    have he : Continuous (fun p : ℝ × ℝ =>
        -(afeCriticalPoint (-p.2) + ((c : ℂ) + (p.1 : ℂ) * I))) := by
      unfold afeCriticalPoint
      fun_prop
    exact he.const_cpow (Or.inl hbaseY)
  rw [show (fun p : ℝ × ℝ =>
      hughesYoungLocalizedMellinWeight T p.2 c p.1 X Y h k x y) =
      fun p : ℝ × ℝ =>
        (hughesYoungDyadicCutoffAt X x : ℂ) *
          (hughesYoungDyadicCutoffAt Y y : ℂ) *
          (shortMobiusSquareCoeff T h *
            (h : ℂ) ^ (-afeCriticalPoint p.2) *
            shortMobiusSquareCoeff T k *
            (k : ℂ) ^ (-afeCriticalPoint (-p.2)) *
            (1 / (Real.pi : ℂ)) *
            (hughesYoungRightContourWeight p.2 c p.1 *
              (((x / h : ℝ) : ℂ)) ^
                (-(afeCriticalPoint p.2 +
                  ((c : ℂ) + (p.1 : ℂ) * I))) *
              (((y / k : ℝ) : ℂ)) ^
                (-(afeCriticalPoint (-p.2) +
                  ((c : ℂ) + (p.1 : ℂ) * I))))) by
    funext p
    exact hughesYoungLocalizedMellinWeight_eq_source_integrand
      T p.2 c p.1 X Y hh hk hx hy]
  have hpowH : Continuous (fun p : ℝ × ℝ =>
      (h : ℂ) ^ (-afeCriticalPoint p.2)) := by
    have he : Continuous (fun p : ℝ × ℝ => -afeCriticalPoint p.2) := by
      unfold afeCriticalPoint
      fun_prop
    exact he.const_cpow (Or.inl (by exact_mod_cast hh.ne'))
  have hpowK : Continuous (fun p : ℝ × ℝ =>
      (k : ℂ) ^ (-afeCriticalPoint (-p.2))) := by
    have he : Continuous (fun p : ℝ × ℝ => -afeCriticalPoint (-p.2)) := by
      unfold afeCriticalPoint
      fun_prop
    exact he.const_cpow (Or.inl (by exact_mod_cast hk.ne'))
  exact (continuous_const.mul continuous_const).mul
    (((((continuous_const.mul hpowH).mul continuous_const).mul hpowK).mul
      continuous_const).mul ((hright.mul hexpX).mul hexpY))

/-- The joint localized integrand vanishes outside the compact height
interval from the authoritative cutoff. -/
theorem support_uncurry_heightWeight_mul_hughesYoungLocalizedMellinWeight_subset
    {T : ℝ} (hT : 0 < T) (c X Y : ℝ) (h k : ℕ) (x y : ℝ) :
    Function.support (fun p : ℝ × ℝ =>
      (hughesYoungHeightWeight T p.2 : ℂ) *
        hughesYoungLocalizedMellinWeight T p.2 c p.1 X Y h k x y) ⊆
      Set.univ ×ˢ Set.Icc (T / 4) (4 * T) := by
  intro p hp
  refine ⟨Set.mem_univ _, hughesYoungHeightWeight_support hT ?_⟩
  intro hzero
  apply hp
  change (hughesYoungHeightWeight T p.2 : ℂ) *
    hughesYoungLocalizedMellinWeight T p.2 c p.1 X Y h k x y = 0
  have hcast : (hughesYoungHeightWeight T p.2 : ℂ) = 0 := by
    exact_mod_cast hzero
  rw [hcast, zero_mul]

/-- Exact evaluation of the height integral by the Fourier transform.  This
is the non-asymptotic identity from which the repeated-integration-by-parts
bound of Hughes--Young (65) is derived. -/
theorem integral_heightWeight_mul_hughesYoungLocalizedMellinWeight_eq_transform
    (T c u X Y : ℝ) {h k : ℕ} (hh : 0 < h) (hk : 0 < k)
    {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (∫ t : ℝ, (hughesYoungHeightWeight T t : ℂ) *
        hughesYoungLocalizedMellinWeight T t c u X Y h k x y) =
      hughesYoungLocalizedStaticWeight T c u X Y h k x y *
        hughesYoungHeightTransform T c u (Real.log (y / x)) := by
  simp_rw [heightWeight_mul_hughesYoungLocalizedMellinWeight_eq_static_mul_phase
    T _ c u X Y hh hk hx hy]
  rw [show (fun t : ℝ =>
      hughesYoungLocalizedStaticWeight T c u X Y h k x y *
        Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
          hughesYoungHeightFourierInput T c u t) =
      fun t : ℝ => hughesYoungLocalizedStaticWeight T c u X Y h k x y *
        (Complex.exp ((((t * Real.log (y / x) : ℝ) : ℂ)) * I) *
          hughesYoungHeightFourierInput T c u t) by
    funext t
    ring]
  rw [integral_const_mul]
  rw [← hughesYoungHeightTransform_eq_integral]

end RiemannZeta.GuthMaynard
