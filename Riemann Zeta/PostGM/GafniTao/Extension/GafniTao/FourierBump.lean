import GafniTao.ExplicitFormulaSetup
import RiemannZeta.GuthMaynard.DFIParametricMellin

/-!
# The logarithmic bump in Gafni--Tao Lemma 2.3

This module constructs one literal nonnegative smooth bump in logarithmic
coordinates from the frozen Guth--Maynard cutoff.  Its support, plateau, and
Fourier convention are exposed, and its Fourier transform is given a
kernel-checked all-orders Schwartz decay estimate.
-/

open Complex Set
open scoped ContDiff FourierTransform

namespace GafniTao

open RiemannZeta.GuthMaynard

/-- The source bump after the affine change to logarithmic coordinates. -/
noncomputable def logScaleBump (cutoff : GMSmoothCutoff) (u : ℝ) : ℝ :=
  cutoff (6 / 5 + u / 2)

theorem contDiff_logScaleBump (cutoff : GMSmoothCutoff) :
    ContDiff ℝ ∞ (logScaleBump cutoff) := by
  exact cutoff.smooth.comp
    (contDiff_const.add (contDiff_id.div_const 2))

theorem logScaleBump_nonneg (cutoff : GMSmoothCutoff) (u : ℝ) :
    0 ≤ logScaleBump cutoff u := by
  exact cutoff.nonneg _

theorem logScaleBump_le_one (cutoff : GMSmoothCutoff) (u : ℝ) :
    logScaleBump cutoff u ≤ 1 := by
  exact cutoff.bounded _

/-- The affine support is kept as an exact closed interval. -/
theorem support_logScaleBump (cutoff : GMSmoothCutoff) :
    Function.support (logScaleBump cutoff) ⊆ Set.Icc (-2 / 5) (8 / 5) := by
  intro u hu
  have hrange := cutoff.support (by
    simpa only [logScaleBump, Function.mem_support] using hu)
  rw [Set.mem_Icc] at hrange ⊢
  constructor <;> linarith

theorem hasCompactSupport_logScaleBump (cutoff : GMSmoothCutoff) :
    HasCompactSupport (logScaleBump cutoff) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro u hu
  by_contra hne
  exact hu (support_logScaleBump cutoff (by
    simpa only [Function.mem_support] using hne))

/-- The bump is exactly one throughout the paper's interval `[0, log 2]`. -/
theorem logScaleBump_eq_one (cutoff : GMSmoothCutoff) {u : ℝ}
    (hu : u ∈ Set.Icc 0 (Real.log 2)) :
    logScaleBump cutoff u = 1 := by
  apply cutoff.equals_one
  rw [Set.mem_Icc] at hu ⊢
  constructor
  · linarith
  · have hlog : Real.log 2 < 1 :=
      Real.log_two_lt_d9.trans (by norm_num)
    linarith

theorem one_le_logScaleBump (cutoff : GMSmoothCutoff) {u : ℝ}
    (hu : u ∈ Set.Icc 0 (Real.log 2)) :
    1 ≤ logScaleBump cutoff u := by
  rw [logScaleBump_eq_one cutoff hu]

/-- Complexification of the source bump. -/
noncomputable def logScaleBumpComplex
    (cutoff : GMSmoothCutoff) (u : ℝ) : ℂ :=
  (logScaleBump cutoff u : ℂ)

theorem contDiff_logScaleBumpComplex (cutoff : GMSmoothCutoff) :
    ContDiff ℝ ∞ (logScaleBumpComplex cutoff) := by
  exact Complex.ofRealCLM.contDiff.comp (contDiff_logScaleBump cutoff)

theorem support_logScaleBumpComplex (cutoff : GMSmoothCutoff) :
    Function.support (logScaleBumpComplex cutoff) ⊆
      Set.Icc (-2 / 5) (8 / 5) := by
  intro u hu
  apply support_logScaleBump cutoff
  rw [Function.mem_support] at hu ⊢
  intro hzero
  apply hu
  simp [logScaleBumpComplex, hzero]

theorem hasCompactSupport_logScaleBumpComplex (cutoff : GMSmoothCutoff) :
    HasCompactSupport (logScaleBumpComplex cutoff) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro u hu
  by_contra hne
  exact hu (support_logScaleBumpComplex cutoff (by
    simpa only [Function.mem_support] using hne))

/-- The literal logarithmic bump as a Schwartz function. -/
noncomputable def logScaleBumpSchwartz (cutoff : GMSmoothCutoff) :
    SchwartzMap ℝ ℂ :=
  (hasCompactSupport_logScaleBumpComplex cutoff).toSchwartzMap
    (contDiff_logScaleBumpComplex cutoff)

@[simp]
theorem logScaleBumpSchwartz_apply (cutoff : GMSmoothCutoff) (u : ℝ) :
    logScaleBumpSchwartz cutoff u = logScaleBumpComplex cutoff u := rfl

/-- Fourier convention used below: Mathlib's transform, whose phase is
`exp (-2 * pi * i * u * xi)`. -/
noncomputable def logScaleBumpFourier
    (cutoff : GMSmoothCutoff) (xi : ℝ) : ℂ :=
  FourierTransform.fourier (logScaleBumpSchwartz cutoff) xi

theorem logScaleBumpFourier_eq_fourierIntegral
    (cutoff : GMSmoothCutoff) (xi : ℝ) :
    logScaleBumpFourier cutoff xi =
      FourierTransform.fourier (logScaleBumpComplex cutoff) xi := by
  rw [logScaleBumpFourier, SchwartzMap.fourier_coe]
  rfl

/-- Exact all-orders polynomial decay.  The visible Schwartz seminorm is the
uniform constant for the fixed bump; no unspecified bounded weight occurs. -/
theorem logScaleBumpFourier_polynomial_decay
    (cutoff : GMSmoothCutoff) (p : ℕ) (xi : ℝ) :
    |xi| ^ p * ‖logScaleBumpFourier cutoff xi‖ ≤
      SchwartzMap.seminorm ℝ p 0
        (FourierTransform.fourier (logScaleBumpSchwartz cutoff)) := by
  simpa only [logScaleBumpFourier, iteratedDeriv_zero] using
    SchwartzMap.le_seminorm' ℝ p 0
      (FourierTransform.fourier (logScaleBumpSchwartz cutoff)) xi

/-- The tenfold `(1+|xi|)^{-10}` decay used in Lemma 2.3, with a literal
constant determined by the fixed cutoff. -/
theorem logScaleBumpFourier_tenfold_decay
    (cutoff : GMSmoothCutoff) (xi : ℝ) :
    (1 + |xi|) ^ 10 * ‖logScaleBumpFourier cutoff xi‖ ≤
      2 ^ 10 *
        (SchwartzMap.seminorm ℝ 0 0
            (FourierTransform.fourier (logScaleBumpSchwartz cutoff)) +
          SchwartzMap.seminorm ℝ 10 0
            (FourierTransform.fourier (logScaleBumpSchwartz cutoff))) := by
  let F : SchwartzMap ℝ ℂ :=
    FourierTransform.fourier (logScaleBumpSchwartz cutoff)
  have hzero : ‖F xi‖ ≤ SchwartzMap.seminorm ℝ 0 0 F := by
    simpa only [iteratedDeriv_zero, pow_zero, one_mul] using
      SchwartzMap.le_seminorm' ℝ 0 0 F xi
  have hten : |xi| ^ 10 * ‖F xi‖ ≤
      SchwartzMap.seminorm ℝ 10 0 F := by
    simpa only [iteratedDeriv_zero] using
      SchwartzMap.le_seminorm' ℝ 10 0 F xi
  change (1 + |xi|) ^ 10 * ‖F xi‖ ≤ _
  by_cases hxi : |xi| ≤ 1
  · have hweight : (1 + |xi|) ^ 10 ≤ 2 ^ 10 := by
      have hbase : 1 + |xi| ≤ 2 := by linarith
      gcongr
    calc
      (1 + |xi|) ^ 10 * ‖F xi‖ ≤
          2 ^ 10 * SchwartzMap.seminorm ℝ 0 0 F :=
        mul_le_mul hweight hzero (norm_nonneg _) (by positivity)
      _ ≤ 2 ^ 10 *
          (SchwartzMap.seminorm ℝ 0 0 F +
            SchwartzMap.seminorm ℝ 10 0 F) := by
        gcongr
        exact le_add_of_nonneg_right (by positivity)
  · have hone : 1 ≤ |xi| := le_of_lt (lt_of_not_ge hxi)
    have hweight : (1 + |xi|) ^ 10 ≤ 2 ^ 10 * |xi| ^ 10 := by
      have hbase : 1 + |xi| ≤ 2 * |xi| := by linarith
      calc
        (1 + |xi|) ^ 10 ≤ (2 * |xi|) ^ 10 := by gcongr
        _ = 2 ^ 10 * |xi| ^ 10 := by rw [mul_pow]
    calc
      (1 + |xi|) ^ 10 * ‖F xi‖ ≤
          (2 ^ 10 * |xi| ^ 10) * ‖F xi‖ :=
        mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
      _ = 2 ^ 10 * (|xi| ^ 10 * ‖F xi‖) := by ring
      _ ≤ 2 ^ 10 * SchwartzMap.seminorm ℝ 10 0 F := by
        gcongr
      _ ≤ 2 ^ 10 *
          (SchwartzMap.seminorm ℝ 0 0 F +
            SchwartzMap.seminorm ℝ 10 0 F) := by
        gcongr
        exact le_add_of_nonneg_left (by positivity)

end GafniTao
