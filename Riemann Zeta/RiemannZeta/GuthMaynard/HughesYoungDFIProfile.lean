import RiemannZeta.GuthMaynard.HughesYoungContourShift
import RiemannZeta.GuthMaynard.HughesYoungShiftWeight
import RiemannZeta.GuthMaynard.DFITheorem1
import RiemannZeta.GuthMaynard.LargeValuesReflection
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno

open Complex Filter MeasureTheory Set Topology
open scoped ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Uniform Hughes--Young input for the DFI theorem

This module supplies the quantitative equation-(2) profile needed to apply
the uniform DFI error theorem to the fixed-shift Hughes--Young weight.  The
first step is the exact all-orders Fourier derivative estimate: each
derivative in the logarithmic frequency inserts one power of the physical
height, with no residual `2 * pi` loss in the normalization used by
`hughesYoungHeightTransform`.
-/

/-! ## Scalar normalization of the DFI source theorem

Hughes--Young apply DFI after pulling the parameter-dependent size of their
weight out of equation (70).  The following identities make that step exact:
both the shifted divisor sum and DFI's equation-(27) central series are
complex-linear in the source weight.  Consequently a quantitative
equation-(2) profile may be proved for a normalized weight without changing
either the main term or the error by an untracked constant.
-/

/-- Complex scalar multiplication of a two-variable DFI weight. -/
noncomputable def dfiComplexScaleWeight
    (z : ℂ) (f : ℝ → ℝ → ℂ) (x y : ℝ) : ℂ := z * f x y

theorem dfiDyadicShiftedDivisorSum_scale
    (z : ℂ) (f : ℝ → ℝ → ℂ) (a b M N : ℕ) (r : ℤ) :
    dfiDyadicShiftedDivisorSum (dfiComplexScaleWeight z f) a b M N r =
      z * dfiDyadicShiftedDivisorSum f a b M N r := by
  unfold dfiDyadicShiftedDivisorSum dfiComplexScaleWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  by_cases hs : quadraticDivisorShift a b m n = r
  · rw [if_pos hs, if_pos hs]
    ring
  · simp [hs]

theorem dfiEquation27CentralIntegral_scale
    (z : ℂ) (f : ℝ → ℝ → ℂ) (a b A B : ℕ) (r : ℝ) :
    dfiEquation27CentralIntegral a b A B (dfiComplexScaleWeight z f) r =
      z * dfiEquation27CentralIntegral a b A B f r := by
  unfold dfiEquation27CentralIntegral dfiEquation27C dfiComplexScaleWeight
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem dfiEquation27CentralSummand_scale
    (z : ℂ) (f : ℝ → ℝ → ℂ) (a b r q : ℕ) :
    dfiEquation27CentralSummand a b r (dfiComplexScaleWeight z f) q =
      z * dfiEquation27CentralSummand a b r f q := by
  unfold dfiEquation27CentralSummand
  rw [dfiEquation27CentralIntegral_scale z f a b
    (dfiReducedDenominator a q) (dfiReducedDenominator b q) (r : ℝ)]
  ring

theorem dfiEquation27CentralSeries_scale
    (z : ℂ) (f : ℝ → ℝ → ℂ) (a b r : ℕ) :
    dfiEquation27CentralSeries a b r (dfiComplexScaleWeight z f) =
      z * dfiEquation27CentralSeries a b r f := by
  unfold dfiEquation27CentralSeries
  simp_rw [dfiEquation27CentralSummand_scale]
  exact tsum_mul_left

theorem dfiSwapWeight_scale
    (z : ℂ) (f : ℝ → ℝ → ℂ) :
    dfiSwapWeight (dfiComplexScaleWeight z f) =
      dfiComplexScaleWeight z (dfiSwapWeight f) := by
  funext x y
  rfl

theorem dfiSignedCentralSeries_scale
    (z : ℂ) (f : ℝ → ℝ → ℂ) (a b : ℕ) (r : ℤ) :
    dfiSignedCentralSeries a b r (dfiComplexScaleWeight z f) =
      z * dfiSignedCentralSeries a b r f := by
  unfold dfiSignedCentralSeries
  split_ifs
  · exact dfiEquation27CentralSeries_scale z f a b r.toNat
  · rw [dfiSwapWeight_scale,
      dfiEquation27CentralSeries_scale z (dfiSwapWeight f)]

/-- The full signed DFI discrepancy scales exactly with the source weight. -/
theorem dfiSignedDiscrepancy_scale
    (z : ℂ) (f : ℝ → ℝ → ℂ) (a b M N : ℕ) (r : ℤ) :
    dfiDyadicShiftedDivisorSum (dfiComplexScaleWeight z f) a b M N r -
        dfiSignedCentralSeries a b r (dfiComplexScaleWeight z f) =
      z * (dfiDyadicShiftedDivisorSum f a b M N r -
        dfiSignedCentralSeries a b r f) := by
  rw [dfiDyadicShiftedDivisorSum_scale, dfiSignedCentralSeries_scale]
  ring

theorem norm_dfiSignedDiscrepancy_scale_le
    {B : ℝ} (z : ℂ) (f : ℝ → ℝ → ℂ) (a b M N : ℕ) (r : ℤ)
    (h : ‖dfiDyadicShiftedDivisorSum f a b M N r -
        dfiSignedCentralSeries a b r f‖ ≤ B) :
    ‖dfiDyadicShiftedDivisorSum (dfiComplexScaleWeight z f) a b M N r -
        dfiSignedCentralSeries a b r (dfiComplexScaleWeight z f)‖ ≤
      ‖z‖ * B := by
  rw [dfiSignedDiscrepancy_scale, norm_mul]
  exact mul_le_mul_of_nonneg_left h (norm_nonneg z)

theorem dfiMixedDeriv_scale
    {f : ℝ → ℝ → ℂ} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (z : ℂ) (i j : ℕ) (x y : ℝ) :
    dfiMixedDeriv i j (dfiComplexScaleWeight z f) x y =
      z * dfiMixedDeriv i j f x y := by
  unfold dfiMixedDeriv dfiComplexScaleWeight
  have hinner :
      (fun x' : ℝ => iteratedDeriv j (fun y' : ℝ => z * f x' y') y) =
        fun x' : ℝ => z * iteratedDeriv j (f x') y := by
    funext x'
    rw [iteratedDeriv_const_mul]
    exact (contDiff_slice_right hf x').contDiffAt.of_le
      (by exact_mod_cast le_top)
  rw [hinner, iteratedDeriv_const_mul]
  exact (contDiff_iteratedDeriv_slice_right hf j y).contDiffAt.of_le
    (by exact_mod_cast le_top)

theorem DFIEquation2.scale
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} (hf : DFIEquation2 f P X Y)
    (z : ℂ) : DFIEquation2 (dfiComplexScaleWeight z f) P X Y := by
  refine
    { one_le_P := hf.one_le_P
      one_le_X := hf.one_le_X
      one_le_Y := hf.one_le_Y
      smooth := ?_
      compactSupport := ?_
      support_pos := ?_
      derivativeBound := ?_ }
  · change ContDiff ℝ ∞ (fun p : ℝ × ℝ => z * f p.1 p.2)
    exact contDiff_const.mul hf.smooth
  · apply HasCompactSupport.mono hf.compactSupport
    intro p hp
    change z * f p.1 p.2 ≠ 0 at hp
    simpa only [Function.mem_support, Function.uncurry_apply_pair] using
      fun hz => hp (mul_eq_zero_of_right z hz)
  · intro p hp
    apply hf.support_pos
    change z * f p.1 p.2 ≠ 0 at hp
    simpa only [Function.mem_support, Function.uncurry_apply_pair] using
      fun hz => hp (mul_eq_zero_of_right z hz)
  · intro i j
    obtain ⟨C, hC, hbound⟩ := hf.derivativeBound i j
    refine ⟨(‖z‖ + 1) * C, mul_pos (by positivity) hC, ?_⟩
    intro x y hx hy
    rw [dfiMixedDeriv_scale hf.smooth, norm_mul]
    have hbaseNonneg :
        0 ≤ (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j) := by
      have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hf.one_le_X
      have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hf.one_le_Y
      have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hf.one_le_P
      have hxden : 0 < 1 + x / X := by positivity
      have hyden : 0 < 1 + y / Y := by positivity
      exact mul_nonneg
        (mul_nonneg (inv_nonneg.mpr hxden.le) (inv_nonneg.mpr hyden.le))
        (pow_nonneg hP0.le _)
    calc
      |x| ^ i * |y| ^ j * (‖z‖ * ‖dfiMixedDeriv i j f x y‖) =
          ‖z‖ * (|x| ^ i * |y| ^ j * ‖dfiMixedDeriv i j f x y‖) := by ring
      _ ≤ ‖z‖ *
          (C * (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j)) := by
        exact mul_le_mul_of_nonneg_left (hbound x y hx hy) (norm_nonneg z)
      _ ≤ (‖z‖ + 1) * C *
          (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j) := by
        have hz : ‖z‖ ≤ ‖z‖ + 1 := by linarith
        have hCB : 0 ≤ C *
            ((1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j)) :=
          mul_nonneg hC.le hbaseNonneg
        calc
          ‖z‖ * (C * (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j)) =
              ‖z‖ * (C *
                ((1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j))) := by ring
          _ ≤ (‖z‖ + 1) * (C *
                ((1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j))) :=
            mul_le_mul_of_nonneg_right hz hCB
          _ = _ := by ring

theorem DFIEquation2Profile.scale
    {f : ℝ → ℝ → ℂ} {P X Y : ℝ} {C : ℕ → ℕ → ℝ}
    (hf : DFIEquation2 f P X Y) (hC : DFIEquation2Profile f P X Y C)
    (z : ℂ) :
    DFIEquation2Profile (dfiComplexScaleWeight z f) P X Y
      (fun i j => (‖z‖ + 1) * C i j) := by
  refine ⟨fun i j => mul_pos (by positivity) (hC.positive i j), ?_⟩
  intro i j x y hx hy
  rw [dfiMixedDeriv_scale hf.smooth, norm_mul]
  have hbaseNonneg :
      0 ≤ (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j) := by
    have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hf.one_le_X
    have hY0 : 0 < Y := lt_of_lt_of_le zero_lt_one hf.one_le_Y
    have hP0 : 0 < P := lt_of_lt_of_le zero_lt_one hf.one_le_P
    have hxden : 0 < 1 + x / X := by positivity
    have hyden : 0 < 1 + y / Y := by positivity
    exact mul_nonneg
      (mul_nonneg (inv_nonneg.mpr hxden.le) (inv_nonneg.mpr hyden.le))
      (pow_nonneg hP0.le _)
  calc
    |x| ^ i * |y| ^ j * (‖z‖ * ‖dfiMixedDeriv i j f x y‖) =
        ‖z‖ * (|x| ^ i * |y| ^ j * ‖dfiMixedDeriv i j f x y‖) := by ring
    _ ≤ ‖z‖ *
        (C i j * (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j)) := by
      exact mul_le_mul_of_nonneg_left (hC.bound i j x y hx hy) (norm_nonneg z)
    _ ≤ (‖z‖ + 1) * C i j *
        (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j) := by
      have hz : ‖z‖ ≤ ‖z‖ + 1 := by linarith
      have hCB : 0 ≤ C i j *
          ((1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j)) :=
        mul_nonneg (hC.positive i j).le hbaseNonneg
      calc
        ‖z‖ * (C i j * (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j)) =
            ‖z‖ * (C i j *
              ((1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j))) := by ring
        _ ≤ (‖z‖ + 1) * (C i j *
              ((1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j))) :=
          mul_le_mul_of_nonneg_right hz hCB
        _ = _ := by ring

/-- Every frequency derivative of the cleaned height transform is controlled
by the corresponding physical-height moment.  This is the quantitative
Fourier half of Hughes--Young (65). -/
theorem norm_iteratedDeriv_hughesYoungHeightTransform_le_moment
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    (j : ℕ) (xi : ℝ) :
    ‖iteratedDeriv j (hughesYoungHeightTransform T c u) xi‖ ≤
      ∫ t : ℝ, ‖t‖ ^ j * ‖hughesYoungHeightFourierInput T c u t‖ := by
  let f : ℝ → ℂ := hughesYoungHeightFourierInput T c u
  let a : ℝ := -(1 / (2 * Real.pi))
  have hfMoment : ∀ n : ℕ, Integrable (fun t : ℝ => t ^ n • f t) := by
    intro n
    have hnorm : Integrable (fun t : ℝ => ‖t‖ ^ n * ‖f t‖) := by
      simpa only [f] using integrable_heightFourierInput_moment hT hc u n
    refine ⟨?_, ?_⟩
    · exact ((continuous_id.pow n).smul
        (continuous_hughesYoungHeightFourierInput T hc u)).aestronglyMeasurable
    · exact hnorm.hasFiniteIntegral.congr' (by
        filter_upwards with t
        simp only [norm_smul, Real.norm_eq_abs, abs_pow]
        rw [abs_of_nonneg
          (mul_nonneg (pow_nonneg (abs_nonneg t) n) (norm_nonneg _))])
  have hfourier : ContDiff ℝ j (FourierTransform.fourier f) :=
    Real.contDiff_fourier fun n _hn => by
      have hnorm : Integrable (fun t : ℝ => ‖t‖ ^ n * ‖f t‖) := by
        simpa only [f] using integrable_heightFourierInput_moment hT hc u n
      exact hnorm
  have hcomp := congrFun
    (iteratedDeriv_comp_const_smul
      hfourier a) xi
  have hfreq := congrFun
    (Real.iteratedDeriv_fourier
      (N := (j : ℕ∞))
      (fun n _hn => hfMoment n) (n := j) le_rfl)
    (a * xi)
  have hFourierNorm :
      ‖FourierTransform.fourier
          (fun t : ℝ => (-2 * Real.pi * I * t) ^ j • f t) (a * xi)‖ ≤
        ∫ t : ℝ, ‖(-2 * Real.pi * I * t) ^ j • f t‖ :=
    VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar MeasureTheory.volume (innerₗ ℝ)
      (fun t : ℝ => (-2 * Real.pi * I * t) ^ j • f t) (a * xi)
  rw [show hughesYoungHeightTransform T c u =
      fun x => FourierTransform.fourier f (a * x) by
    funext x
    unfold hughesYoungHeightTransform a f
    ring]
  rw [hcomp, hfreq, norm_smul, norm_pow]
  calc
    ‖(a : ℝ)‖ ^ j *
          ‖FourierTransform.fourier
            (fun t : ℝ => (-2 * Real.pi * I * t) ^ j • f t) (a * xi)‖
        ≤ ‖(a : ℝ)‖ ^ j *
          (∫ t : ℝ, ‖(-2 * Real.pi * I * t) ^ j • f t‖) := by
            gcongr
    _ = ∫ t : ℝ, ‖t‖ ^ j * ‖f t‖ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      rw [norm_smul, norm_pow, norm_mul, norm_mul]
      simp only [norm_real, norm_I, mul_one, Real.norm_eq_abs]
      have hpi : 0 < 2 * Real.pi := by positivity
      have hnormpi : ‖(2 : ℂ) * (Real.pi : ℂ)‖ = 2 * Real.pi := by
        rw [norm_mul]
        norm_num [norm_real, abs_of_pos Real.pi_pos]
      simp only [a, abs_neg, abs_div, abs_one, abs_of_pos hpi]
      rw [div_pow]
      field_simp [ne_of_gt hpi]
      rw [norm_neg, hnormpi]
      ring
    _ = ∫ t : ℝ, ‖t‖ ^ j *
          ‖hughesYoungHeightFourierInput T c u t‖ := by rfl

/-- A uniform bound for the right-contour factor on the physical height
support converts the exact Fourier moment into the expected `T^(j+1)`
derivative cost.  The numerical constant is deliberately kept as the exact
length of `[T/4,4T]`; no compactness-selected constant enters this lemma. -/
theorem integral_norm_heightFourierInput_moment_le
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u A : ℝ)
    (hWeight : ∀ t ∈ Set.Icc (T / 4) (4 * T),
      ‖hughesYoungRightContourWeight t c u‖ ≤ A)
    (j : ℕ) :
    ∫ t : ℝ, ‖t‖ ^ j * ‖hughesYoungHeightFourierInput T c u t‖ ≤
      (15 * T / 4) * ((4 * T) ^ j * A) := by
  let S : Set ℝ := Set.Icc (T / 4) (4 * T)
  let g : ℝ → ℝ := fun t =>
    ‖t‖ ^ j * ‖hughesYoungHeightFourierInput T c u t‖
  let B : ℝ := (4 * T) ^ j * A
  have hg : Integrable g := by
    simpa only [g] using integrable_heightFourierInput_moment hT hc u j
  have hzero : ∀ t ∉ S, g t = 0 := by
    intro t ht
    have hcut : hughesYoungHeightWeight T t = 0 := by
      by_contra hne
      exact ht (hughesYoungHeightWeight_support hT hne)
    simp [g, hughesYoungHeightFourierInput, hcut]
  have hfull : (∫ t : ℝ, g t) = ∫ t in S, g t := by
    rw [← MeasureTheory.integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards with t
    by_cases ht : t ∈ S
    · have ht' : t ∈ Set.Icc (T / 4) (4 * T) := by simpa only [S] using ht
      simp [ht']
    · have ht' : t ∉ Set.Icc (T / 4) (4 * T) := by simpa only [S] using ht
      rw [hzero t ht]
      simp [ht']
  have hBint : IntegrableOn (fun _t : ℝ => B) S :=
    MeasureTheory.integrableOn_const isCompact_Icc.measure_ne_top
  have hpoint : ∀ t ∈ S, g t ≤ B := by
    intro t ht
    have htUpper : |t| ≤ 4 * T := by
      rw [Set.mem_Icc] at ht
      have htLower : 0 ≤ t := by linarith
      simpa [abs_of_nonneg htLower] using ht.2
    have hcutNonneg := hughesYoungHeightWeight_nonneg T t
    have hcutOne := hughesYoungHeightWeight_le_one T t
    have hright := hWeight t ht
    have hinput :
        ‖hughesYoungHeightFourierInput T c u t‖ ≤ A := by
      rw [hughesYoungHeightFourierInput, norm_mul, norm_real,
        Real.norm_eq_abs, abs_of_nonneg hcutNonneg]
      calc
        hughesYoungHeightWeight T t *
              ‖hughesYoungRightContourWeight t c u‖
            ≤ 1 * A := mul_le_mul hcutOne hright (norm_nonneg _) (by norm_num)
        _ = A := one_mul A
    dsimp only [g, B]
    exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg t) htUpper j)
      hinput (norm_nonneg _) (pow_nonneg (by positivity) j)
  rw [hfull]
  calc
    (∫ t in S, g t) ≤ ∫ _t in S, B :=
      MeasureTheory.setIntegral_mono_on hg.integrableOn hBint
        measurableSet_Icc hpoint
    _ = (15 * T / 4) * B := by
      simp only [S, MeasureTheory.setIntegral_const, smul_eq_mul]
      rw [Real.volume_real_Icc_of_le (by linarith)]
      have hsub : 4 * T - T / 4 = 15 * T / 4 := by ring
      rw [hsub]
    _ = (15 * T / 4) * ((4 * T) ^ j * A) := by rfl

/-- Quantitative version of the preceding exact Fourier derivative lemma. -/
theorem norm_iteratedDeriv_hughesYoungHeightTransform_le
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u A : ℝ)
    (hWeight : ∀ t ∈ Set.Icc (T / 4) (4 * T),
      ‖hughesYoungRightContourWeight t c u‖ ≤ A)
    (j : ℕ) (xi : ℝ) :
    ‖iteratedDeriv j (hughesYoungHeightTransform T c u) xi‖ ≤
      (15 * T / 4) * ((4 * T) ^ j * A) :=
  (norm_iteratedDeriv_hughesYoungHeightTransform_le_moment hT hc u j xi).trans
    (integral_norm_heightFourierInput_moment_le hT hc u A hWeight j)

/-! ## Scale-uniform dyadic-cutoff derivatives

The constants in DFI equation (2) must be fixed before the Hughes--Young
dyadic scales are selected.  The exact dilation formula below cancels the
physical scale against the source weights `|x|^i |y|^j`; consequently only
derivatives of the one fixed cutoff on `[1,2]` enter the profile.
-/

/-- Every derivative of every positive dilation of the fixed Hughes--Young
cutoff has a common scale-weighted bound.  The constant depends only on the
derivative order, not on the physical dyadic scale. -/
theorem exists_uniform_hughesYoungDyadicCutoffAt_derivativeProfile :
    ∃ C : ℕ → ℝ, ∀ n : ℕ, 0 < C n ∧ ∀ (X : ℝ), 0 < X → ∀ x : ℝ,
      |x| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt X) x‖ ≤ C n := by
  choose B hB hbound using fun n : ℕ =>
    exists_scaled_iteratedDeriv_bound
      contDiff_hughesYoungDyadicCutoff
      hasCompactSupport_hughesYoungDyadicCutoff
      (A := (1 : ℝ)) zero_lt_one n
  let C : ℕ → ℝ := fun n => 2 ^ n * B n
  refine ⟨C, fun n => ⟨mul_pos (pow_pos (by norm_num) n) (hB n), ?_⟩⟩
  intro X hX x
  have hnSmooth : ContDiff ℝ n hughesYoungDyadicCutoff :=
    contDiff_hughesYoungDyadicCutoff.of_le (by exact_mod_cast le_top)
  have hformula := congrFun
    (iteratedDeriv_comp_const_mul hnSmooth X⁻¹) x
  have hcutFormula :
      iteratedDeriv n (hughesYoungDyadicCutoffAt X) x =
        X⁻¹ ^ n * iteratedDeriv n hughesYoungDyadicCutoff (X⁻¹ * x) := by
    rw [show hughesYoungDyadicCutoffAt X =
        fun y : ℝ => hughesYoungDyadicCutoff (X⁻¹ * y) by
      funext y
      simp only [hughesYoungDyadicCutoffAt]
      ring]
    exact hformula
  rw [hcutFormula, norm_mul, Real.norm_eq_abs, abs_pow, abs_inv,
    abs_of_pos hX]
  by_cases hd : iteratedDeriv n hughesYoungDyadicCutoff (X⁻¹ * x) = 0
  · rw [hd, norm_zero, mul_zero, mul_zero]
    exact (mul_pos (pow_pos (by norm_num) n) (hB n)).le
  · have hmemSupport : X⁻¹ * x ∈
        Function.support (iteratedDeriv n hughesYoungDyadicCutoff) := hd
    have hmemTSupport : X⁻¹ * x ∈
        tsupport (iteratedDeriv n hughesYoungDyadicCutoff) :=
      subset_closure hmemSupport
    have hbaseTSupport : tsupport hughesYoungDyadicCutoff ⊆ Set.Icc 1 2 :=
      closure_minimal support_hughesYoungDyadicCutoff_subset isClosed_Icc
    have hz : X⁻¹ * x ∈ Set.Icc (1 : ℝ) 2 :=
      hbaseTSupport (tsupport_iteratedDeriv_subset hughesYoungDyadicCutoff n hmemTSupport)
    have habs : |X⁻¹ * x| ≤ 2 := by
      rw [abs_of_nonneg (le_trans (by norm_num) hz.1)]
      exact hz.2
    have hderiv : ‖iteratedDeriv n hughesYoungDyadicCutoff (X⁻¹ * x)‖ ≤ B n := by
      simpa using hbound n (X⁻¹ * x)
    have hscale : |x| * X⁻¹ = |X⁻¹ * x| := by
      rw [abs_mul, abs_inv, abs_of_pos hX]
      ring
    calc
      |x| ^ n * (X⁻¹ ^ n *
          ‖iteratedDeriv n hughesYoungDyadicCutoff (X⁻¹ * x)‖) =
          (|x| * X⁻¹) ^ n *
            ‖iteratedDeriv n hughesYoungDyadicCutoff (X⁻¹ * x)‖ := by ring
      _ = |X⁻¹ * x| ^ n *
            ‖iteratedDeriv n hughesYoungDyadicCutoff (X⁻¹ * x)‖ := by rw [hscale]
      _ ≤ 2 ^ n * B n :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) habs n) hderiv
          (norm_nonneg _) (pow_nonneg (by norm_num) n)
      _ = C n := by rfl

/-! ## Scale-uniform logarithmic Mellin factors -/

/-- Exact separation of the arithmetic index from the physical variable in
one Hughes--Young logarithmic power. -/
theorem hughesYoungLogPower_div_eq_cpow_mul_cpow
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (s : ℂ) :
    hughesYoungLogPower s (x / h) =
      (h : ℂ) ^ s * (x : ℂ) ^ (-s) := by
  unfold hughesYoungLogPower
  rw [Real.log_div hx.ne' hh.ne', Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr hh.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne'),
    ← Complex.ofReal_log hh.le, ← Complex.ofReal_log hx.le,
    ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Exact repeated derivative of a localized logarithmic Mellin power on the
positive axis. -/
theorem iteratedDeriv_hughesYoungLogPower_div
    (s : ℂ) (n : ℕ) {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    iteratedDeriv n (fun z : ℝ => hughesYoungLogPower s (z / h)) x =
      (h : ℂ) ^ s * gmCpowDerivativeCoeff (-s) n *
        (x : ℂ) ^ (-s - n) := by
  have hevent :
      (fun z : ℝ => hughesYoungLogPower s (z / h)) =ᶠ[𝓝 x]
        (fun z : ℝ => (h : ℂ) ^ s * (z : ℂ) ^ (-s)) := by
    filter_upwards [Ioi_mem_nhds hx] with z hz
    exact hughesYoungLogPower_div_eq_cpow_mul_cpow hz hh s
  rw [hevent.iteratedDeriv_eq n, iteratedDeriv_const_mul_field,
    iteratedDeriv_ofReal_cpow (-s) n hx]
  ring

/-- Exact scale-weighted norm of the repeated derivative.  The physical
power `x^n` cancels the derivative loss, leaving only the dimensionless
ratio `h/x` raised to the real part of the Mellin exponent. -/
theorem abs_pow_mul_norm_iteratedDeriv_hughesYoungLogPower_div
    (s : ℂ) (n : ℕ) {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    |x| ^ n *
        ‖iteratedDeriv n (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖ =
      ‖gmCpowDerivativeCoeff (-s) n‖ * (h / x) ^ s.re := by
  rw [iteratedDeriv_hughesYoungLogPower_div s n hx hh,
    norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hh,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hexp : (-s - (n : ℂ)).re = -(s.re) - (n : ℝ) := by
    simp
  rw [hexp, abs_of_pos hx, ← Real.rpow_natCast]
  have hcancel : x ^ (n : ℝ) * x ^ (-(s.re) - (n : ℝ)) =
      x ^ (-(s.re)) := by
    rw [← Real.rpow_add hx]
    congr 1
    ring
  calc
    x ^ (n : ℝ) *
        (h ^ s.re * ‖gmCpowDerivativeCoeff (-s) n‖ *
          x ^ (-(s.re) - (n : ℝ))) =
        ‖gmCpowDerivativeCoeff (-s) n‖ * h ^ s.re *
          (x ^ (n : ℝ) * x ^ (-(s.re) - (n : ℝ))) := by ring
    _ = ‖gmCpowDerivativeCoeff (-s) n‖ * h ^ s.re *
          x ^ (-(s.re)) := by rw [hcancel]
    _ = ‖gmCpowDerivativeCoeff (-s) n‖ *
          (h ^ s.re * x ^ (-(s.re))) := by ring
    _ = ‖gmCpowDerivativeCoeff (-s) n‖ * (h / x) ^ s.re := by
      rw [Real.rpow_neg hx.le, Real.div_rpow hh.le hx.le]
      rfl

/-- The dyadic source range bounds the residual Mellin ratio uniformly over
the small horizontal contour. -/
theorem rpow_div_le_two_rpow_three_halves
    {X x h c : ℝ} (hX : 0 < X) (hx : X ≤ x) (hh : 0 < h)
    (hhUpper : h ≤ 2 * X) (hc : 0 < c) (hc1 : c ≤ 1) :
    (h / x) ^ ((1 / 2 : ℝ) + c) ≤ 2 ^ (3 / 2 : ℝ) := by
  have hxPos : 0 < x := hX.trans_le hx
  have hratio0 : 0 ≤ h / x := (div_pos hh hxPos).le
  have hratio : h / x ≤ 2 := by
    rw [div_le_iff₀ hxPos]
    nlinarith
  by_cases hsmall : h / x ≤ 1
  · calc
      (h / x) ^ ((1 / 2 : ℝ) + c) ≤ 1 :=
        Real.rpow_le_one hratio0 hsmall (by positivity)
      _ ≤ 2 ^ (3 / 2 : ℝ) := by
        exact Real.one_le_rpow (by norm_num) (by norm_num)
  · have hbase : 1 ≤ h / x := le_of_not_ge hsmall
    have hexp : (1 / 2 : ℝ) + c ≤ 3 / 2 := by linarith
    calc
      (h / x) ^ ((1 / 2 : ℝ) + c) ≤ (h / x) ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hbase hexp
      _ ≤ 2 ^ (3 / 2 : ℝ) :=
        Real.rpow_le_rpow hratio0 hratio (by norm_num)

/-- Explicit all-orders derivative bound for one localized Hughes--Young
Mellin factor on its dyadic source range. -/
theorem abs_pow_mul_norm_iteratedDeriv_hughesYoungLogPower_shift_le
    {X x h c u : ℝ} (hX : 0 < X) (hx : X ≤ x)
    (hh : 0 < h) (hhUpper : h ≤ 2 * X) (hc : 0 < c) (hc1 : c ≤ 1)
    (n : ℕ) :
    |x| ^ n * ‖iteratedDeriv n
        (fun z : ℝ => hughesYoungLogPower
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) (z / h)) x‖ ≤
      (|u| + 2 + n) ^ n * 2 ^ (3 / 2 : ℝ) := by
  let s : ℂ := (1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)
  have hxPos : 0 < x := hX.trans_le hx
  have hsre : s.re = (1 / 2 : ℝ) + c := by simp [s]
  have hsnorm : ‖-s‖ ≤ |u| + 2 := by
    rw [norm_neg]
    have hsEq : s = (((1 / 2 : ℝ) + c : ℝ) : ℂ) + (u : ℂ) * I := by
      dsimp only [s]
      push_cast
      ring
    rw [hsEq]
    calc
      ‖(((1 / 2 : ℝ) + c : ℝ) : ℂ) + (u : ℂ) * I‖ ≤
          ‖(((1 / 2 : ℝ) + c : ℝ) : ℂ)‖ + ‖(u : ℂ) * I‖ :=
        norm_add_le _ _
      _ = |(1 / 2 : ℝ) + c| + |u| := by
        rw [norm_mul, norm_I, mul_one, norm_real, norm_real,
          Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |u| + 2 := by
        rw [abs_of_pos (by positivity : 0 < (1 / 2 : ℝ) + c)]
        linarith
  have hcoeff : ‖gmCpowDerivativeCoeff (-s) n‖ ≤
      (|u| + 2 + n) ^ n := by
    exact (norm_gmCpowDerivativeCoeff_le (-s) n).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) n)
  have hratio : (h / x) ^ s.re ≤ 2 ^ (3 / 2 : ℝ) := by
    rw [hsre]
    exact rpow_div_le_two_rpow_three_halves hX hx hh hhUpper hc hc1
  rw [show (fun z : ℝ => hughesYoungLogPower
      ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) (z / h)) =
      fun z : ℝ => hughesYoungLogPower s (z / h) by rfl,
    abs_pow_mul_norm_iteratedDeriv_hughesYoungLogPower_div s n hxPos hh]
  exact mul_le_mul hcoeff hratio
    (Real.rpow_nonneg (div_nonneg hh.le hxPos.le) _) (by positivity)

/-- One separated physical-variable factor of the localized Hughes--Young
kernel. -/
noncomputable def hughesYoungLocalizedOneFactor
    (X h : ℝ) (s : ℂ) (x : ℝ) : ℂ :=
  (hughesYoungDyadicCutoffAt X x : ℂ) *
    hughesYoungLogPower s (x / h)

local notation "𝒩" => nhds

/-- The apparent logarithmic singularity in one localized factor is removed
by the dyadic cutoff, which vanishes on a neighborhood of the origin. -/
theorem contDiff_hughesYoungLocalizedOneFactor
    {X h : ℝ} (hX : 0 < X) (hh : 0 < h) (s : ℂ) :
    ContDiff ℝ ∞ (hughesYoungLocalizedOneFactor X h s) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x < X
  · have hnhds : Set.Iio X ∈ 𝒩 x := Iio_mem_nhds hx
    have hzero : hughesYoungLocalizedOneFactor X h s =ᶠ[𝒩 x]
        (fun _ => 0) := by
      filter_upwards [hnhds] with z hz
      unfold hughesYoungLocalizedOneFactor
      have hcut : hughesYoungDyadicCutoffAt X z = 0 :=
        hughesYoungDyadicCutoff_eq_zero_of_le_one
          ((div_le_one hX).2 hz.le)
      rw [hcut]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hzero
  · have hxPos : 0 < x := hX.trans_le (le_of_not_gt hx)
    have hlogArg : ContDiffAt ℝ ∞ (fun z : ℝ => Real.log (z / h)) x :=
      (Real.contDiffAt_log.2 (div_ne_zero hxPos.ne' hh.ne')).comp x
        (contDiff_id.div_const h).contDiffAt
    unfold hughesYoungLocalizedOneFactor hughesYoungLogPower
    exact (Complex.ofRealCLM.contDiff.comp
        (contDiff_hughesYoungDyadicCutoffAt X)).contDiffAt.mul
      ((contDiffAt_const.mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp x hlogArg)).cexp)

/-- Exact Leibniz expansion of one localized physical-variable factor. -/
theorem iteratedDeriv_hughesYoungLocalizedOneFactor
    {X h x : ℝ} (hh : 0 < h) (hx : 0 < x)
    (s : ℂ) (n : ℕ) :
    iteratedDeriv n (hughesYoungLocalizedOneFactor X h s) x =
      ∑ q ∈ Finset.range (n + 1),
        (n.choose q : ℂ) *
          iteratedDeriv q
            (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x *
          iteratedDeriv (n - q)
            (fun z : ℝ => hughesYoungLogPower s (z / h)) x := by
  have hcut : ContDiffAt ℝ n
      (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x :=
    (Complex.ofRealCLM.contDiff.comp
      (contDiff_hughesYoungDyadicCutoffAt X)).contDiffAt.of_le
        (by exact_mod_cast le_top)
  have hlogArg : ContDiffAt ℝ ∞ (fun z : ℝ => Real.log (z / h)) x :=
    (Real.contDiffAt_log.2 (div_ne_zero hx.ne' hh.ne')).comp x
      (contDiff_id.div_const h).contDiffAt
  have hpow : ContDiffAt ℝ n
      (fun z : ℝ => hughesYoungLogPower s (z / h)) x := by
    unfold hughesYoungLogPower
    exact (contDiffAt_const.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x hlogArg)).cexp.of_le
        (by exact_mod_cast le_top)
  unfold hughesYoungLocalizedOneFactor
  change iteratedDeriv n
      ((fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) *
        fun z : ℝ => hughesYoungLogPower s (z / h)) x = _
  rw [iteratedDeriv_mul hcut hpow]

/-- The physical-scale weighted derivatives of one localized
Hughes--Young Mellin factor are controlled by the fixed cutoff profile and
the exact logarithmic-power cancellation.  No dyadic scale occurs in the
right-hand side. -/
theorem abs_pow_mul_norm_iteratedDeriv_hughesYoungLocalizedOneFactor_le
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (X : ℝ), 0 < X → ∀ x : ℝ,
      |x| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt X) x‖ ≤ Ccut n)
    {X x h c u : ℝ} (hX : 0 < X) (hx : X ≤ x)
    (hh : 0 < h) (hhUpper : h ≤ 2 * X) (hc : 0 < c) (hc1 : c ≤ 1)
    (n : ℕ) :
    |x| ^ n * ‖iteratedDeriv n
        (hughesYoungLocalizedOneFactor X h
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) x‖ ≤
      ∑ q ∈ Finset.range (n + 1),
        (n.choose q : ℝ) * Ccut q *
          ((|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
            2 ^ (3 / 2 : ℝ)) := by
  let s : ℂ := (1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)
  have hxPos : 0 < x := hX.trans_le hx
  rw [show ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) = s by rfl,
    iteratedDeriv_hughesYoungLocalizedOneFactor hh hxPos s n]
  calc
    |x| ^ n * ‖∑ q ∈ Finset.range (n + 1),
        (n.choose q : ℂ) *
          iteratedDeriv q
            (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x *
          iteratedDeriv (n - q)
            (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖ ≤
        |x| ^ n * ∑ q ∈ Finset.range (n + 1),
          ‖(n.choose q : ℂ) *
            iteratedDeriv q
              (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x *
            iteratedDeriv (n - q)
              (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg (abs_nonneg _) _)
    _ = ∑ q ∈ Finset.range (n + 1), |x| ^ n *
          ‖(n.choose q : ℂ) *
            iteratedDeriv q
              (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x *
            iteratedDeriv (n - q)
              (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ Finset.range (n + 1),
        (n.choose q : ℝ) * Ccut q *
          ((|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
            2 ^ (3 / 2 : ℝ)) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqn : q ≤ n := by
        have hqlt : q < n + 1 := Finset.mem_range.mp hq
        omega
      have hcutComplex :
          |x| ^ q * ‖iteratedDeriv q
            (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x‖ ≤
              Ccut q := by
        rw [congrFun (iteratedDeriv_ofReal_comp
          (hughesYoungDyadicCutoffAt X)
          (contDiff_hughesYoungDyadicCutoffAt X) q) x,
          norm_real, Real.norm_eq_abs]
        simpa using (hcut q).2 X hX x
      have hpowBound :
          |x| ^ (n - q) * ‖iteratedDeriv (n - q)
            (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖ ≤
              (|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
                2 ^ (3 / 2 : ℝ) := by
        dsimp only [s]
        exact abs_pow_mul_norm_iteratedDeriv_hughesYoungLogPower_shift_le
          (u := u) hX hx hh hhUpper hc hc1 (n - q)
      have hchoose : 0 ≤ (n.choose q : ℝ) := by positivity
      have hcutNonneg : 0 ≤ Ccut q := (hcut q).1.le
      have hrightNonneg : 0 ≤
          (|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
            2 ^ (3 / 2 : ℝ) := by
        exact mul_nonneg (pow_nonneg (by positivity :
            0 ≤ |u| + 2 + ((n - q : ℕ) : ℝ)) _)
          (Real.rpow_nonneg (by norm_num) _)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have hxpow : |x| ^ n = |x| ^ q * |x| ^ (n - q) := by
        rw [← pow_add, Nat.add_sub_of_le hqn]
      rw [hxpow]
      calc
        (|x| ^ q * |x| ^ (n - q)) *
            ((n.choose q : ℝ) *
              ‖iteratedDeriv q
                (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x‖ *
              ‖iteratedDeriv (n - q)
                (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖) =
            (n.choose q : ℝ) *
              (|x| ^ q * ‖iteratedDeriv q
                (fun z : ℝ => (hughesYoungDyadicCutoffAt X z : ℂ)) x‖) *
              (|x| ^ (n - q) * ‖iteratedDeriv (n - q)
                (fun z : ℝ => hughesYoungLogPower s (z / h)) x‖) := by ring
        _ ≤ (n.choose q : ℝ) * Ccut q *
            ((|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
              2 ^ (3 / 2 : ℝ)) := by
          gcongr

/-- Order-dependent coefficient in the scale-free one-factor estimate. -/
noncomputable def hughesYoungOneFactorDerivativeProfile
    (Ccut : ℕ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (n + 1),
    (n.choose q : ℝ) * Ccut q *
      ((|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
        2 ^ (3 / 2 : ℝ))

theorem hughesYoungOneFactorDerivativeProfile_pos
    (Ccut : ℕ → ℝ) (hcut : ∀ n, 0 < Ccut n) (u : ℝ) (n : ℕ) :
    0 < hughesYoungOneFactorDerivativeProfile Ccut u n := by
  unfold hughesYoungOneFactorDerivativeProfile
  apply Finset.sum_pos'
  · intro q hq
    have hqn : q ≤ n := by
      have : q < n + 1 := Finset.mem_range.mp hq
      omega
    exact mul_nonneg
      (mul_nonneg (by positivity) (hcut q).le)
      (mul_nonneg (pow_nonneg (by positivity) _)
        (Real.rpow_nonneg (by norm_num) _))
  · refine ⟨n, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.choose_self, Nat.sub_self]
    norm_num
    exact mul_pos (hcut n) (Real.rpow_pos_of_pos (by norm_num) _)

theorem abs_pow_mul_norm_iteratedDeriv_hughesYoungLocalizedOneFactor_profile_le
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (X : ℝ), 0 < X → ∀ x : ℝ,
      |x| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt X) x‖ ≤ Ccut n)
    {X x h c u : ℝ} (hX : 0 < X) (hx : X ≤ x)
    (hh : 0 < h) (hhUpper : h ≤ 2 * X) (hc : 0 < c) (hc1 : c ≤ 1)
    (n : ℕ) :
    |x| ^ n * ‖iteratedDeriv n
        (hughesYoungLocalizedOneFactor X h
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) x‖ ≤
      hughesYoungOneFactorDerivativeProfile Ccut u n := by
  exact abs_pow_mul_norm_iteratedDeriv_hughesYoungLocalizedOneFactor_le
    Ccut hcut hX hx hh hhUpper hc hc1 n

/-- Exact mixed derivative of a separated two-variable product. -/
theorem dfiMixedDeriv_separated_product
    {f g : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i j : ℕ) (x y : ℝ) :
    dfiMixedDeriv i j (fun x' y' => f x' * g y') x y =
      iteratedDeriv i f x * iteratedDeriv j g y := by
  unfold dfiMixedDeriv
  have hyfun :
      (fun x' : ℝ => iteratedDeriv j (fun y' : ℝ => f x' * g y') y) =
        fun x' : ℝ => f x' * iteratedDeriv j g y := by
    funext x'
    rw [iteratedDeriv_const_mul (f x')
      (hg.contDiffAt.of_le (by exact_mod_cast le_top))]
  rw [hyfun]
  rw [show (fun x' : ℝ => f x' * iteratedDeriv j g y) =
      fun x' : ℝ => iteratedDeriv j g y * f x' by
    funext x'
    ring]
  rw [iteratedDeriv_const_mul (iteratedDeriv j g y)
    (hf.contDiffAt.of_le (by exact_mod_cast le_top))]
  ring

/-! ## Fixed-shift logarithmic phase

The point of freezing the additive shift before invoking DFI is that every
positive derivative of the Fourier phase retains a factor `|r| / Y`.  The
next lemmas prove this gain explicitly instead of bounding the two logarithms
separately.
-/

/-- The real-valued version of the positive-order logarithmic derivative
formula used in DFI equation (27). -/
theorem iteratedDeriv_real_log_succ
    (n : ℕ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv (n + 1) Real.log x =
      (-1 : ℝ) ^ n * n.factorial * x ^ (-(n + 1 : ℕ) : ℤ) := by
  induction n generalizing x with
  | zero =>
      rw [show 0 + 1 = 1 by omega, iteratedDeriv_one]
      rw [(Real.hasDerivAt_log hx.ne').deriv]
      norm_num [zpow_neg, zpow_natCast]
  | succ n ih =>
      rw [show (n + 1) + 1 = (n + 1) + 1 by rfl, iteratedDeriv_succ]
      have heq : Set.EqOn
          (iteratedDeriv (n + 1) Real.log)
          (fun y : ℝ =>
            (-1 : ℝ) ^ n * n.factorial *
              y ^ (-(n + 1 : ℕ) : ℤ))
          (Set.Ioi 0) := by
        intro y hy
        exact ih hy
      rw [heq.deriv isOpen_Ioi hx]
      have hpow : HasDerivAt
          (fun y : ℝ => y ^ (-(n + 1 : ℕ) : ℤ))
          ((-(n + 1 : ℕ) : ℤ) *
            x ^ (-(n + 1 : ℕ) - 1 : ℤ)) x :=
        hasDerivAt_zpow _ _ (Or.inl hx.ne')
      have hderiv := hpow.const_mul ((-1 : ℝ) ^ n * n.factorial)
      rw [hderiv.deriv]
      push_cast
      norm_num [pow_succ, Nat.factorial_succ]
      ring

/-- On the positive fixed-shift range, Hughes--Young's phase is the
difference of two logarithms. -/
theorem neg_log_one_add_shift_div_eq_log_sub_log_add
    {y r : ℝ} (hy : 0 < y) (hyr : 0 < y + r) :
    -Real.log (1 + r / y) = Real.log y - Real.log (y + r) := by
  have hratio : 1 + r / y = (y + r) / y := by
    field_simp [hy.ne']
  rw [hratio, Real.log_div hyr.ne' hy.ne']
  ring

/-- Exact positive-order derivatives of the frozen Hughes--Young phase.
Writing the result as a difference of inverse powers keeps the additive
shift visible for the subsequent mean-value bound. -/
theorem iteratedDeriv_neg_log_one_add_shift_div_succ
    (n : ℕ) {y r : ℝ} (hy : 0 < y) (hyr : 0 < y + r) :
    iteratedDeriv (n + 1) (fun z : ℝ => -Real.log (1 + r / z)) y =
      (-1 : ℝ) ^ n * n.factorial *
        (y ^ (-(n + 1 : ℕ) : ℤ) -
          (y + r) ^ (-(n + 1 : ℕ) : ℤ)) := by
  have hlocal :
      (fun z : ℝ => -Real.log (1 + r / z)) =ᶠ[𝓝 y]
        (fun z : ℝ => Real.log z - Real.log (z + r)) := by
    have hyN : Set.Ioi 0 ∈ 𝓝 y := Ioi_mem_nhds hy
    have hyrN : Set.Ioi (-r) ∈ 𝓝 y := Ioi_mem_nhds (by linarith)
    filter_upwards [hyN, hyrN] with z hz hzShift
    change -r < z at hzShift
    exact neg_log_one_add_shift_div_eq_log_sub_log_add hz (by linarith)
  rw [hlocal.iteratedDeriv_eq]
  have hlog : ContDiffAt ℝ (n + 1) Real.log y :=
    (Real.contDiffAt_log.2 hy.ne').of_le (by exact_mod_cast le_top)
  have hlogShift : ContDiffAt ℝ (n + 1) (fun z : ℝ => Real.log (z + r)) y :=
    ((Real.contDiffAt_log.2 hyr.ne').comp y
      (contDiffAt_id.add contDiffAt_const)).of_le (by exact_mod_cast le_top)
  change iteratedDeriv (n + 1)
      (Real.log - fun z : ℝ => Real.log (z + r)) y = _
  rw [iteratedDeriv_sub hlog hlogShift,
    iteratedDeriv_real_log_succ n hy]
  have hshiftFormula := congrFun
    (iteratedDeriv_comp_add_const (n := n + 1) (f := Real.log) r) y
  rw [hshiftFormula, iteratedDeriv_real_log_succ n hyr]
  ring

/-- Difference of equal negative powers on a common positive scale.  This is
the elementary mean-value estimate which preserves the small additive shift. -/
theorem abs_zpow_neg_nat_sub_zpow_neg_nat_le
    {Y y z : ℝ} (hY : 0 < Y) (hy : Y / 2 ≤ y) (hz : Y / 2 ≤ z)
    (m : ℕ) :
    |y ^ (-(m : ℕ) : ℤ) - z ^ (-(m : ℕ) : ℤ)| ≤
      |y - z| * m * (2 / Y) ^ (m + 1) := by
  have hhalf : 0 < Y / 2 := by positivity
  have hypos : 0 < y := hhalf.trans_le hy
  have hzpos : 0 < z := hhalf.trans_le hz
  rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast,
    ← inv_pow, ← inv_pow]
  have hyInv : |y⁻¹| ≤ 2 / Y := by
    rw [abs_inv, abs_of_pos hypos]
    have h := one_div_le_one_div_of_le hhalf hy
    simpa [one_div, div_eq_mul_inv] using h
  have hzInv : |z⁻¹| ≤ 2 / Y := by
    rw [abs_inv, abs_of_pos hzpos]
    have h := one_div_le_one_div_of_le hhalf hz
    simpa [one_div, div_eq_mul_inv] using h
  have hmax : max |y⁻¹| |z⁻¹| ≤ 2 / Y := max_le hyInv hzInv
  have hInvDiff : |y⁻¹ - z⁻¹| ≤ |y - z| * (2 / Y) ^ 2 := by
    have heq : y⁻¹ - z⁻¹ = (z - y) / (y * z) := by
      field_simp [hypos.ne', hzpos.ne']
    rw [heq, abs_div, abs_mul, abs_of_pos hypos, abs_of_pos hzpos]
    have hprod : (Y / 2) ^ 2 ≤ y * z := by
      nlinarith [mul_le_mul hy hz hhalf.le (le_trans hhalf.le hy)]
    have hquot : 1 / (y * z) ≤ 1 / (Y / 2) ^ 2 :=
      one_div_le_one_div_of_le (sq_pos_of_pos hhalf) hprod
    calc
      |z - y| / (y * z) = |y - z| * (1 / (y * z)) := by
        rw [abs_sub_comm]
        ring
      _ ≤ |y - z| * (1 / (Y / 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hquot (abs_nonneg _)
      _ = |y - z| * (2 / Y) ^ 2 := by
        field_simp [hY.ne']
  calc
    |y⁻¹ ^ m - z⁻¹ ^ m| ≤
        |y⁻¹ - z⁻¹| * m * max |y⁻¹| |z⁻¹| ^ (m - 1) :=
      abs_pow_sub_pow_le (a := y⁻¹) (b := z⁻¹) (n := m)
    _ ≤ (|y - z| * (2 / Y) ^ 2) * m *
        (2 / Y) ^ (m - 1) := by
      gcongr
    _ ≤ |y - z| * m * (2 / Y) ^ (m + 1) := by
      by_cases hm : m = 0
      · subst m
        norm_num
      · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
        rw [show m + 1 = 2 + (m - 1) by omega, pow_add]
        exact le_of_eq (by ac_rfl)

/-- Exact cancellation of a physical scale against the corresponding
inverse derivative scale. -/
theorem two_mul_scale_pow_mul_two_div_scale_pow
    {Y : ℝ} (hY : 0 < Y) (m : ℕ) :
    (2 * Y) ^ m * (2 / Y) ^ (m + 1) = 2 ^ (2 * m + 1) / Y := by
  induction m with
  | zero =>
      norm_num
  | succ m ih =>
      calc
        (2 * Y) ^ (m + 1) * (2 / Y) ^ (m + 1 + 1) =
            ((2 * Y) ^ m * (2 / Y) ^ (m + 1)) *
              ((2 * Y) * (2 / Y)) := by
          rw [pow_succ (2 * Y) m, pow_succ (2 / Y) (m + 1)]
          ring
        _ = (2 ^ (2 * m + 1) / Y) * 4 := by
          rw [ih]
          field_simp [hY.ne']
          norm_num
        _ = 2 ^ (2 * (m + 1) + 1) / Y := by
          field_simp [hY.ne']
          rw [show 2 * (m + 1) + 1 = 2 * m + 3 by omega,
            pow_add]
          norm_num
          ring

/-- Scale-weighted derivative bound for the frozen logarithmic phase.  Each
positive derivative carries one factor `|r| / Y`, exactly as required in
Hughes--Young equation (70). -/
theorem norm_iteratedDeriv_neg_log_one_add_shift_div_succ_le
    (n : ℕ) {Y y r : ℝ} (hY : 0 < Y)
    (hyLower : Y ≤ y) (hyUpper : y ≤ 2 * Y)
    (hr : |r| ≤ Y / 2) :
    |y| ^ (n + 1) *
        ‖iteratedDeriv (n + 1)
          (fun z : ℝ => -Real.log (1 + r / z)) y‖ ≤
      (n.factorial : ℝ) * (n + 1) * 2 ^ (2 * n + 4) * (|r| / Y) := by
  have hyPos : 0 < y := hY.trans_le hyLower
  have hyrLower : Y / 2 ≤ y + r := by
    have hrLower : -(Y / 2) ≤ r := by
      exact (neg_le_of_abs_le hr)
    linarith
  have hyrPos : 0 < y + r := (by positivity : 0 < Y / 2).trans_le hyrLower
  have hfacAbs : |(n.factorial : ℝ)| = n.factorial :=
    abs_of_nonneg (Nat.cast_nonneg n.factorial)
  rw [iteratedDeriv_neg_log_one_add_shift_div_succ n hyPos hyrPos,
    Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, hfacAbs]
  simp only [one_mul]
  have hdiff := abs_zpow_neg_nat_sub_zpow_neg_nat_le
    hY (by linarith : Y / 2 ≤ y) hyrLower (n + 1)
  have hyAbs : |y| ≤ 2 * Y := by simpa [abs_of_pos hyPos] using hyUpper
  have hpowY : |y| ^ (n + 1) ≤ (2 * Y) ^ (n + 1) :=
    pow_le_pow_left₀ (abs_nonneg _) hyAbs _
  have hdiff' :
      |y ^ (-(n + 1 : ℕ) : ℤ) -
          (y + r) ^ (-(n + 1 : ℕ) : ℤ)| ≤
        |r| * (n + 1) * (2 / Y) ^ (n + 2) := by
    simpa [abs_neg] using hdiff
  calc
    |y| ^ (n + 1) *
        ((n.factorial : ℝ) *
          |y ^ (-(n + 1 : ℕ) : ℤ) -
            (y + r) ^ (-(n + 1 : ℕ) : ℤ)|) =
        (n.factorial : ℝ) * |y| ^ (n + 1) *
          |y ^ (-(n + 1 : ℕ) : ℤ) -
            (y + r) ^ (-(n + 1 : ℕ) : ℤ)| := by ring
    _ ≤ (n.factorial : ℝ) * (2 * Y) ^ (n + 1) *
          |y ^ (-(n + 1 : ℕ) : ℤ) -
            (y + r) ^ (-(n + 1 : ℕ) : ℤ)| := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpowY (by positivity)) (abs_nonneg _)
    _ ≤ (n.factorial : ℝ) * (2 * Y) ^ (n + 1) *
          (|r| * (n + 1) * (2 / Y) ^ (n + 2)) := by
      exact mul_le_mul_of_nonneg_left hdiff' (by positivity)
    _ = (n.factorial : ℝ) * (n + 1) * |r| *
          ((2 * Y) ^ (n + 1) * (2 / Y) ^ (n + 2)) := by ring
    _ = (n.factorial : ℝ) * (n + 1) * 2 ^ (2 * n + 3) *
          (|r| / Y) := by
      rw [show n + 2 = (n + 1) + 1 by omega,
        two_mul_scale_pow_mul_two_div_scale_pow hY (n + 1)]
      ring
    _ ≤ (n.factorial : ℝ) * (n + 1) * 2 ^ (2 * n + 4) *
          (|r| / Y) := by
      have hratio : 0 ≤ |r| / Y := div_nonneg (abs_nonneg _) hY.le
      have hp : (2 : ℝ) ^ (2 * n + 3) ≤ 2 ^ (2 * n + 4) := by
        calc
          (2 : ℝ) ^ (2 * n + 3) ≤ 2 ^ (2 * n + 3) * 2 := by
            nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 * n + 3)]
          _ = 2 ^ ((2 * n + 3) + 1) := (pow_succ _ _).symm
          _ = 2 ^ (2 * n + 4) :=
            congrArg (fun k : ℕ => (2 : ℝ) ^ k) (by omega)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hp (by positivity)) hratio

/-- Order-only constant in the frozen-shift phase estimate. -/
noncomputable def hughesYoungShiftPhaseDerivativeConstant (q : ℕ) : ℝ :=
  (q - 1).factorial * q * 2 ^ (2 * (q - 1) + 4)

theorem hughesYoungShiftPhaseDerivativeConstant_pos
    {q : ℕ} (hq : 0 < q) :
    0 < hughesYoungShiftPhaseDerivativeConstant q := by
  unfold hughesYoungShiftPhaseDerivativeConstant
  positivity

/-- The phase estimate indexed directly by its positive derivative order. -/
theorem norm_iteratedDeriv_neg_log_one_add_shift_div_le
    {q : ℕ} (hq : 0 < q) {Y y r : ℝ} (hY : 0 < Y)
    (hyLower : Y ≤ y) (hyUpper : y ≤ 2 * Y)
    (hr : |r| ≤ Y / 2) :
    |y| ^ q *
        ‖iteratedDeriv q (fun z : ℝ => -Real.log (1 + r / z)) y‖ ≤
      hughesYoungShiftPhaseDerivativeConstant q * (|r| / Y) := by
  have hqPred : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hqCast : ((q - 1 : ℕ) : ℝ) + 1 = q := by
    exact_mod_cast hqPred
  simpa only [hqPred, hughesYoungShiftPhaseDerivativeConstant] using
    (norm_iteratedDeriv_neg_log_one_add_shift_div_succ_le
      (q - 1) hY hyLower hyUpper hr).trans_eq (by rw [hqCast])

/-- The part sizes of an ordered finite partition sum to the size of the
partitioned finite set. -/
theorem OrderedFinpartition.sum_partSize
    {n : ℕ} (c : OrderedFinpartition n) :
    ∑ j, c.partSize j = n := by
  have hcard := Fintype.card_congr c.equivSigma
  simpa only [Fintype.card_fin, Fintype.card_sigma] using hcard

/-- Order-only Faà di Bruno constant for the height-transform composition. -/
noncomputable def hughesYoungShiftCompositionConstant (n : ℕ) : ℝ :=
  1 + ∑ c : OrderedFinpartition n,
    (15 / 4 : ℝ) * 4 ^ c.length *
      ∏ j, hughesYoungShiftPhaseDerivativeConstant (c.partSize j)

theorem one_le_hughesYoungShiftCompositionConstant (n : ℕ) :
    1 ≤ hughesYoungShiftCompositionConstant n := by
  unfold hughesYoungShiftCompositionConstant
  have hsum : 0 ≤ ∑ c : OrderedFinpartition n,
      (15 / 4 : ℝ) * 4 ^ c.length *
        ∏ j, hughesYoungShiftPhaseDerivativeConstant (c.partSize j) := by
    apply Finset.sum_nonneg
    intro c _hc
    have hprod : 0 ≤
        ∏ j, hughesYoungShiftPhaseDerivativeConstant (c.partSize j) :=
      Finset.prod_nonneg fun j _hj =>
        (hughesYoungShiftPhaseDerivativeConstant_pos (c.partSize_pos j)).le
    positivity
  linarith

/-! ## Small horizontal shifts of the archimedean factor

Hughes--Young move each opened divisor pair from the absolutely convergent
line to a small positive line.  The quantitative point is that a horizontal
shift by `d` costs only `exp (O(d log(2 + |t|)))`.  The pinned PNT+ library
already proves the logarithmic vertical-strip bound for `digamma`; Gronwall's
inequality turns that logarithmic derivative estimate into the required
Gamma quotient estimate without invoking an unformalized Stirling formula.
-/

/-- On the open right half-plane, the derivative of Gamma is Gamma times its
logarithmic derivative. -/
theorem hasDerivAt_Gamma_eq_mul_digamma_of_re_pos
    {z : ℂ} (hz : 0 < z.re) :
    HasDerivAt Complex.Gamma (Complex.Gamma z * Complex.digamma z) z := by
  have hpoles : ∀ n : ℕ, z ≠ -(n : ℂ) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp only [neg_re, natCast_re] at hre
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hdiff := (Complex.differentiableAt_Gamma z hpoles).hasDerivAt
  convert hdiff using 1
  rw [Complex.digamma_def, logDeriv_apply]
  field_simp [Complex.Gamma_ne_zero hpoles]

/-- A fixed-width horizontal shift from the critical Gamma line has precisely
logarithmic height cost.  The constant is uniform in the ordinate and in the
shift `0 ≤ d ≤ 1/2`. -/
theorem exists_norm_Gamma_quarter_horizontal_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (z : ℂ) (d : ℝ),
      z.re = 1 / 4 → 0 ≤ d → d ≤ 1 / 2 →
      ‖Complex.Gamma (z + (d : ℂ))‖ ≤
        ‖Complex.Gamma z‖ *
          Real.exp (C * d * Real.log (|z.im| + 2)) := by
  obtain ⟨C, hC, hdigamma⟩ :=
    Complex.exists_norm_digamma_le_log
      (a := (1 / 4 : ℝ)) (b := (3 / 4 : ℝ)) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro z d hzre hd0 hd1
  let f : ℝ → ℂ := fun x => Complex.Gamma (z + (x : ℂ))
  let f' : ℝ → ℂ := fun x =>
    Complex.Gamma (z + (x : ℂ)) * Complex.digamma (z + (x : ℂ))
  let K : ℝ := C * Real.log (|z.im| + 2)
  have hlog : 0 ≤ Real.log (|z.im| + 2) := by
    exact Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hK : 0 ≤ K := mul_nonneg hC.le hlog
  have hzpos (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      0 < (z + (x : ℂ)).re := by
    simp only [add_re, ofReal_re, hzre]
    linarith [hx.1]
  have hfderiv (x : ℝ) (hx : x ∈ Set.Icc 0 d) :
      HasDerivAt f (f' x) x := by
    have houter := hasDerivAt_Gamma_eq_mul_digamma_of_re_pos (hzpos x hx)
    have hshift : HasDerivAt (fun w : ℂ => z + w) 1 (x : ℂ) :=
      (hasDerivAt_id (x : ℂ)).const_add z
    convert (houter.comp (x : ℂ) hshift).comp_ofReal using 1
    all_goals simp only [f']
    all_goals ring
  have hfcont : ContinuousOn f (Set.Icc 0 d) := by
    intro x hx
    exact (hfderiv x hx).continuousAt.continuousWithinAt
  have hderivWithin : ∀ x ∈ Set.Ico 0 d,
      HasDerivWithinAt f (f' x) (Set.Ici x) x := by
    intro x hx
    exact (hfderiv x ⟨hx.1, hx.2.le⟩).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Ico 0 d,
      ‖f' x‖ ≤ K * ‖f x‖ + 0 := by
    intro x hx
    have hxreLower : (1 / 4 : ℝ) ≤ (z + (x : ℂ)).re := by
      simp only [add_re, ofReal_re, hzre]
      linarith [hx.1]
    have hxreUpper : (z + (x : ℂ)).re ≤ (3 / 4 : ℝ) := by
      simp only [add_re, ofReal_re, hzre]
      linarith [hx.2.le, hd1]
    have him : (z + (x : ℂ)).im = z.im := by simp
    have hdig := hdigamma (z + (x : ℂ)) hxreLower hxreUpper
    rw [him] at hdig
    simp only [f', f, norm_mul, add_zero]
    calc
      ‖Complex.Gamma (z + (x : ℂ))‖ *
            ‖Complex.digamma (z + (x : ℂ))‖
          ≤ ‖Complex.Gamma (z + (x : ℂ))‖ *
              (C * Real.log (|z.im| + 2)) :=
        mul_le_mul_of_nonneg_left hdig (norm_nonneg _)
      _ = K * ‖Complex.Gamma (z + (x : ℂ))‖ := by
        dsimp only [K]
        ring
  have hgronwall := norm_le_gronwallBound_of_norm_deriv_right_le
    hfcont hderivWithin (show ‖f 0‖ ≤ ‖f 0‖ by rfl) hbound d
    (show d ∈ Set.Icc 0 d from ⟨hd0, le_rfl⟩)
  rw [gronwallBound_ε0, sub_zero] at hgronwall
  change ‖Complex.Gamma (z + (d : ℂ))‖ ≤
    ‖Complex.Gamma z‖ *
      Real.exp (C * d * Real.log (|z.im| + 2))
  convert hgronwall using 1
  all_goals simp only [f, ofReal_zero, add_zero, K]
  all_goals ring

/-- Deligne's real Gamma factor inherits the small horizontal-shift bound.
This is the archimedean estimate used when the opened Hughes--Young pair is
moved to `Re w = c`. -/
theorem exists_norm_GammaR_critical_horizontal_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (y c : ℝ), 0 ≤ c → c ≤ 1 →
      ‖Complex.Gammaℝ
          (((1 / 2 + c : ℝ) : ℂ) + (y : ℂ) * I)‖ ≤
        ‖Complex.Gammaℝ
          ((1 / 2 : ℂ) + (y : ℂ) * I)‖ *
          Real.exp (C * c * Real.log (|y| + 2)) := by
  obtain ⟨C, hC, hGamma⟩ := exists_norm_Gamma_quarter_horizontal_shift_le
  refine ⟨C, hC, ?_⟩
  intro y c hc0 hc1
  let z : ℂ := (1 / 4 : ℂ) + ((y / 2 : ℝ) : ℂ) * I
  let d : ℝ := c / 2
  have hzre : z.re = 1 / 4 := by simp [z]
  have hd0 : 0 ≤ d := by dsimp [d]; linarith
  have hd1 : d ≤ 1 / 2 := by dsimp [d]; linarith
  have hGammaShift := hGamma z d hzre hd0 hd1
  have hzim : z.im = y / 2 := by simp [z]
  have hlogArg : |z.im| + 2 ≤ |y| + 2 := by
    rw [hzim]
    rw [abs_div]
    norm_num
  have hlogSmall : 0 ≤ Real.log (|z.im| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg z.im])
  have hlogBig : 0 ≤ Real.log (|y| + 2) :=
    Real.log_nonneg (by linarith [abs_nonneg y])
  have hlogLe : Real.log (|z.im| + 2) ≤ Real.log (|y| + 2) :=
    Real.log_le_log (by linarith [abs_nonneg z.im]) hlogArg
  have hexponent :
      C * d * Real.log (|z.im| + 2) ≤
        C * c * Real.log (|y| + 2) := by
    calc
      C * d * Real.log (|z.im| + 2) ≤
          C * d * Real.log (|y| + 2) := by
        gcongr
      _ ≤ C * c * Real.log (|y| + 2) := by
        have hdc : d ≤ c := by dsimp [d]; linarith
        gcongr
  have hexp :
      Real.exp (C * d * Real.log (|z.im| + 2)) ≤
        Real.exp (C * c * Real.log (|y| + 2)) :=
    Real.exp_le_exp.mpr hexponent
  let pShift : ℝ := Real.pi ^ (-(1 / 2 + c) / 2)
  let pBase : ℝ := Real.pi ^ (-(1 / 2 : ℝ) / 2)
  have hpShift : 0 ≤ pShift := by dsimp [pShift]; positivity
  have hpBase : 0 ≤ pBase := by dsimp [pBase]; positivity
  have hpLe : pShift ≤ pBase := by
    dsimp only [pShift, pBase]
    apply Real.rpow_le_rpow_of_exponent_le
    · exact le_of_lt (by linarith [Real.pi_gt_three])
    · linarith
  have hShiftNorm :
      ‖Complex.Gammaℝ
          (((1 / 2 + c : ℝ) : ℂ) + (y : ℂ) * I)‖ =
        pShift * ‖Complex.Gamma (z + (d : ℂ))‖ := by
    rw [Complex.Gammaℝ_def, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    · dsimp [pShift]
      congr 1
      simp
    · congr 2
      dsimp [z, d]
      push_cast
      ring
  have hBaseNorm :
      ‖Complex.Gammaℝ ((1 / 2 : ℂ) + (y : ℂ) * I)‖ =
        pBase * ‖Complex.Gamma z‖ := by
    rw [Complex.Gammaℝ_def, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos]
    congr 1
    · dsimp [pBase]
      congr 1
      simp
    · congr 2
      dsimp [z]
      push_cast
      ring
  rw [hShiftNorm, hBaseNorm]
  calc
    pShift * ‖Complex.Gamma (z + (d : ℂ))‖ ≤
        pShift * (‖Complex.Gamma z‖ *
          Real.exp (C * d * Real.log (|z.im| + 2))) :=
      mul_le_mul_of_nonneg_left hGammaShift hpShift
    _ ≤ pShift * (‖Complex.Gamma z‖ *
          Real.exp (C * c * Real.log (|y| + 2))) := by
      gcongr
    _ ≤ pBase * (‖Complex.Gamma z‖ *
          Real.exp (C * c * Real.log (|y| + 2))) := by
      exact mul_le_mul_of_nonneg_right hpLe (by positivity)
    _ = pBase * ‖Complex.Gamma z‖ *
          Real.exp (C * c * Real.log (|y| + 2)) := by ring

/-- The two horizontally shifted Gamma factors retain the cancellation of
the critical symmetric pair.  This is the source-faithful form of the
archimedean estimate: the height cost is `exp (O(c log T))`, not a fixed
positive power introduced by moving to an unnecessarily distant line. -/
theorem exists_norm_GammaR_shifted_symmetric_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u c : ℝ), 0 ≤ c → c ≤ 1 →
      ‖Complex.Gammaℝ
          (((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
        ‖Complex.Gammaℝ
          (((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖ ≤
      (‖Complex.Gammaℝ
          ((1 / 2 : ℂ) + (t : ℂ) * I)‖ *
        ‖Complex.Gammaℝ
          ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖) *
        Real.exp
          (2 * C * c * Real.log (|t| + |u| + 2) + 8 * u ^ 2) := by
  obtain ⟨C, hC, hshift⟩ := exists_norm_GammaR_critical_horizontal_shift_le
  refine ⟨C, hC, ?_⟩
  intro t u c hc0 hc1
  let L : ℝ := Real.log (|t| + |u| + 2)
  have hargPos : 0 < |t| + |u| + 2 := by positivity
  have hL : 0 ≤ L := by
    dsimp [L]
    exact Real.log_nonneg (by linarith [abs_nonneg t, abs_nonneg u])
  have hplusArg : |t + u| + 2 ≤ |t| + |u| + 2 := by
    linarith [abs_add_le t u]
  have hminusArg : |-t + u| + 2 ≤ |t| + |u| + 2 := by
    have htri := abs_add_le (-t) u
    simp only [abs_neg] at htri
    linarith
  have hplusLog : Real.log (|t + u| + 2) ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by positivity) hplusArg
  have hminusLog : Real.log (|-t + u| + 2) ≤ L := by
    dsimp [L]
    exact Real.log_le_log (by positivity) hminusArg
  have hp := hshift (t + u) c hc0 hc1
  have hm := hshift (-t + u) c hc0 hc1
  have hcp : 0 ≤ C * c := mul_nonneg hC.le hc0
  have hp' :
      ‖Complex.Gammaℝ
          (((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ ≤
        ‖Complex.Gammaℝ
          ((1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
          Real.exp (C * c * L) := by
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hplusLog hcp))
      (norm_nonneg _))
  have hm' :
      ‖Complex.Gammaℝ
          (((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖ ≤
        ‖Complex.Gammaℝ
          ((1 / 2 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖ *
          Real.exp (C * c * L) := by
    exact hm.trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hminusLog hcp))
      (norm_nonneg _))
  have hcritical := norm_GammaR_critical_symmetric_le t u
  have hshiftPair :
      ‖Complex.Gammaℝ
          (((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
        ‖Complex.Gammaℝ
          (((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖ ≤
      (‖Complex.Gammaℝ
          ((1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
        ‖Complex.Gammaℝ
          ((1 / 2 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖) *
        Real.exp (2 * C * c * L) := by
    calc
      _ ≤ (‖Complex.Gammaℝ
              ((1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
            Real.exp (C * c * L)) *
          (‖Complex.Gammaℝ
              ((1 / 2 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖ *
            Real.exp (C * c * L)) := by gcongr
      _ = (‖Complex.Gammaℝ
              ((1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
            ‖Complex.Gammaℝ
              ((1 / 2 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖) *
          Real.exp (2 * C * c * L) := by
        rw [show Real.exp (2 * C * c * L) =
            Real.exp (C * c * L) * Real.exp (C * c * L) by
          rw [← Real.exp_add]
          congr 1
          ring]
        ring
  calc
    _ ≤ (‖Complex.Gammaℝ
            ((1 / 2 : ℂ) + ((t + u : ℝ) : ℂ) * I)‖ *
          ‖Complex.Gammaℝ
            ((1 / 2 : ℂ) + ((-t + u : ℝ) : ℂ) * I)‖) *
        Real.exp (2 * C * c * L) := hshiftPair
    _ ≤ (Real.exp (8 * u ^ 2) *
          (‖Complex.Gammaℝ
            ((1 / 2 : ℂ) + (t : ℂ) * I)‖ *
          ‖Complex.Gammaℝ
            ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖)) *
          Real.exp (2 * C * c * L) :=
      mul_le_mul_of_nonneg_right hcritical (Real.exp_nonneg _)
    _ = (‖Complex.Gammaℝ
            ((1 / 2 : ℂ) + (t : ℂ) * I)‖ *
          ‖Complex.Gammaℝ
            ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖) *
        Real.exp (2 * C * c * Real.log (|t| + |u| + 2) + 8 * u ^ 2) := by
      dsimp [L]
      rw [Real.exp_add]
      ring

/-- The paired Gamma quotient occurring on the shifted Hughes--Young line.
Unlike the temporary `c = 2` estimate below, this statement preserves the
small shift and hence records only the source `T^(O(c))` cost. -/
noncomputable def hughesYoungGammaRatioShift
    (t c u : ℝ) : ℂ :=
  let s₁ : ℂ := ((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I
  let s₂ : ℂ := ((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I
  Complex.Gammaℝ s₁ ^ 2 * Complex.Gammaℝ s₂ ^ 2 /
    afeGammaNormalization t

theorem exists_norm_hughesYoungGammaRatioShift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u c : ℝ), 0 ≤ c → c ≤ 1 →
      ‖hughesYoungGammaRatioShift t c u‖ ≤
        Real.exp
          (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) := by
  obtain ⟨C, hC, hpair⟩ := exists_norm_GammaR_shifted_symmetric_le
  refine ⟨C, hC, ?_⟩
  intro t u c hc0 hc1
  let central : ℝ :=
    ‖Complex.Gammaℝ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ *
      ‖Complex.Gammaℝ
        ((1 / 2 : ℂ) + ((-t : ℝ) : ℂ) * I)‖
  let E : ℝ := 2 * C * c * Real.log (|t| + |u| + 2) + 8 * u ^ 2
  have hcentral : 0 < central := by
    dsimp [central]
    apply mul_pos <;> rw [norm_pos_iff]
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
    · exact Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num)
  have hpair' := hpair t u c hc0 hc1
  change _ ≤ central * Real.exp E at hpair'
  have hpairSq := pow_le_pow_left₀
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpair' 2
  have hden : ‖afeGammaNormalization t‖ = central ^ 2 := by
    unfold afeGammaNormalization
    rw [norm_mul, norm_pow, norm_pow]
    dsimp [central, afeCriticalPoint]
    ring
  unfold hughesYoungGammaRatioShift
  dsimp only
  rw [norm_div, norm_mul, norm_pow, norm_pow, hden]
  rw [div_le_iff₀ (sq_pos_of_pos hcentral)]
  calc
    ‖Complex.Gammaℝ
          (↑(1 / 2 + c) + ↑(t + u) * I)‖ ^ 2 *
        ‖Complex.Gammaℝ
          (↑(1 / 2 + c) + ↑(-t + u) * I)‖ ^ 2 =
      (‖Complex.Gammaℝ
          (↑(1 / 2 + c) + ↑(t + u) * I)‖ *
        ‖Complex.Gammaℝ
          (↑(1 / 2 + c) + ↑(-t + u) * I)‖) ^ 2 := by ring
    _ ≤ (central * Real.exp E) ^ 2 := hpairSq
    _ = Real.exp
          (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) *
        central ^ 2 := by
      have h2E : 2 * E =
          4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2 := by
        dsimp [E]
        ring
      rw [mul_pow]
      rw [show Real.exp E ^ 2 = Real.exp (2 * E) by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring]
      rw [h2E]
      ring

/-- The pole-cancelling polynomial quotient on an arbitrary small positive
Hughes--Young line. -/
noncomputable def hughesYoungPolynomialRatioShift
    (t c u : ℝ) : ℂ :=
  let s₁ : ℂ := ((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I
  let s₂ : ℂ := ((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I
  (s₁ * (1 - s₁)) ^ 2 * (s₂ * (1 - s₂)) ^ 2 /
    afePoleNormalization t

/-- Uniform polynomial control of the shifted pole-normalization quotient.
The estimate is independent of the height and uniform for `0 ≤ c ≤ 1`. -/
theorem norm_hughesYoungPolynomialRatioShift_le
    (t u c : ℝ) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ‖hughesYoungPolynomialRatioShift t c u‖ ≤
      (25 + 8 * u ^ 2) ^ 4 := by
  let A : ℝ := (1 / 4 : ℝ) + t ^ 2
  let B : ℝ := 25 + 8 * u ^ 2
  let qp : ℝ := (1 / 2 + c) ^ 2 + (t + u) ^ 2
  let qp' : ℝ := (1 / 2 - c) ^ 2 + (t + u) ^ 2
  let qm : ℝ := (1 / 2 + c) ^ 2 + (-t + u) ^ 2
  let qm' : ℝ := (1 / 2 - c) ^ 2 + (-t + u) ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hqp0 : 0 ≤ qp := by dsimp [qp]; positivity
  have hqp0' : 0 ≤ qp' := by dsimp [qp']; positivity
  have hqm0 : 0 ≤ qm := by dsimp [qm]; positivity
  have hqm0' : 0 ≤ qm' := by dsimp [qm']; positivity
  have hqp : qp ≤ B * A := by
    dsimp [qp, B, A]
    nlinarith [sq_nonneg t, sq_nonneg u, sq_nonneg (t - u)]
  have hqp' : qp' ≤ B * A := by
    dsimp [qp', B, A]
    nlinarith [sq_nonneg t, sq_nonneg u, sq_nonneg (t - u)]
  have hqm : qm ≤ B * A := by
    dsimp [qm, B, A]
    nlinarith [sq_nonneg t, sq_nonneg u, sq_nonneg (t + u)]
  have hqm' : qm' ≤ B * A := by
    dsimp [qm', B, A]
    nlinarith [sq_nonneg t, sq_nonneg u, sq_nonneg (t + u)]
  let s₁ : ℂ := ((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I
  let s₂ : ℂ := ((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I
  have hs₁ : ‖s₁‖ ^ 2 = qp := by
    rw [Complex.sq_norm]
    simp [s₁, qp, Complex.normSq]
    ring
  have hs₁' : ‖1 - s₁‖ ^ 2 = qp' := by
    rw [Complex.sq_norm]
    simp [s₁, qp', Complex.normSq]
    ring
  have hs₂ : ‖s₂‖ ^ 2 = qm := by
    rw [Complex.sq_norm]
    simp [s₂, qm, Complex.normSq]
    ring
  have hs₂' : ‖1 - s₂‖ ^ 2 = qm' := by
    rw [Complex.sq_norm]
    simp [s₂, qm', Complex.normSq]
    ring
  have hnum₁ : ‖(s₁ * (1 - s₁)) ^ 2‖ = qp * qp' := by
    rw [norm_pow, norm_mul, mul_pow, hs₁, hs₁']
  have hnum₂ : ‖(s₂ * (1 - s₂)) ^ 2‖ = qm * qm' := by
    rw [norm_pow, norm_mul, mul_pow, hs₂, hs₂']
  have hden : ‖afePoleNormalization t‖ = A ^ 4 := by
    unfold afePoleNormalization
    have hcritical (v : ℝ) :
        ‖(1 / 2 : ℂ) + (v : ℂ) * I‖ *
            ‖1 - ((1 / 2 : ℂ) + (v : ℂ) * I)‖ =
          (1 / 4 : ℝ) + v ^ 2 := by
      have h₁ : ‖(1 / 2 : ℂ) + (v : ℂ) * I‖ =
          Real.sqrt ((1 / 4 : ℝ) + v ^ 2) := by
        rw [Complex.norm_def]
        congr 1
        simp [Complex.normSq, sq]
        ring
      have h₂ : ‖1 - ((1 / 2 : ℂ) + (v : ℂ) * I)‖ =
          Real.sqrt ((1 / 4 : ℝ) + v ^ 2) := by
        rw [Complex.norm_def]
        congr 1
        simp [Complex.normSq, sq]
        ring
      rw [h₁, h₂, ← sq]
      exact Real.sq_sqrt (by positivity)
    have hcrit : ‖afeCriticalPoint t * (1 - afeCriticalPoint t)‖ = A := by
      rw [norm_mul]
      simpa only [afeCriticalPoint, A] using hcritical t
    have hcritNeg :
        ‖afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))‖ = A := by
      rw [norm_mul]
      have h := hcritical (-t)
      simpa only [afeCriticalPoint, A, neg_sq] using h
    rw [norm_pow, show afeCriticalPoint t * (1 - afeCriticalPoint t) *
        afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)) =
      (afeCriticalPoint t * (1 - afeCriticalPoint t)) *
        (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) by ring,
      norm_mul, hcrit, hcritNeg]
    ring
  have hprod : (qp * qp') * (qm * qm') ≤ (B * A) ^ 4 := by
    calc
      (qp * qp') * (qm * qm') ≤
          ((B * A) * (B * A)) * ((B * A) * (B * A)) := by
        gcongr
      _ = (B * A) ^ 4 := by ring
  have hratio : (qp * qp') * (qm * qm') / A ^ 4 ≤ B ^ 4 := by
    rw [div_le_iff₀ (pow_pos hA 4)]
    calc
      (qp * qp') * (qm * qm') ≤ (B * A) ^ 4 := hprod
      _ = B ^ 4 * A ^ 4 := by ring
  unfold hughesYoungPolynomialRatioShift
  dsimp only
  rw [show (↑(1 / 2 + c) + ↑(t + u) * I : ℂ) = s₁ by rfl,
      show (↑(1 / 2 + c) + ↑(-t + u) * I : ℂ) = s₂ by rfl]
  rw [norm_div, norm_mul, hnum₁, hnum₂, hden]
  exact hratio

/-- Exact factorization of the complete right-contour coefficient on an
arbitrary positive line. -/
theorem hughesYoungRightContourWeight_shift_eq
    (t c u : ℝ) :
    hughesYoungRightContourWeight t c u =
      (Complex.exp (100 * (((c : ℂ) + (u : ℂ) * I) ^ 2)) *
        hughesYoungAuxiliaryZero ((c : ℂ) + (u : ℂ) * I)) *
        hughesYoungPolynomialRatioShift t c u *
        hughesYoungGammaRatioShift t c u /
        ((c : ℂ) + (u : ℂ) * I) := by
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  have hs₁ : s₁ =
      ((1 / 2 + c : ℝ) : ℂ) + ((t + u : ℝ) : ℂ) * I := by
    dsimp [s₁, w, afeCriticalPoint]
    push_cast
    ring
  have hs₂ : s₂ =
      ((1 / 2 + c : ℝ) : ℂ) + ((-t + u : ℝ) : ℂ) * I := by
    dsimp [s₂, w, afeCriticalPoint]
    push_cast
    ring
  by_cases hw : w = 0
  · have hc : c = 0 := by
      have := congrArg Complex.re hw
      simpa [w] using this
    have hu : u = 0 := by
      have := congrArg Complex.im hw
      simpa [w] using this
    subst c
    subst u
    simp [hughesYoungRightContourWeight, hughesYoungPolynomialRatioShift,
      hughesYoungGammaRatioShift]
  ·
    rw [hughesYoungRightContourWeight]
    rw [show afeCriticalPoint t + ((c : ℂ) + (u : ℂ) * I) = s₁ by rfl,
      show afeCriticalPoint (-t) + ((c : ℂ) + (u : ℂ) * I) = s₂ by rfl,
      hs₁, hs₂]
    unfold hughesYoungPolynomialRatioShift hughesYoungGammaRatioShift
    dsimp only
    field_simp [afePoleNormalization_ne_zero t,
      afeGammaNormalization_ne_zero t, hw]

/-- Complete small-line estimate.  The Gaussian in the Mellin ordinate is
retained, while the only height dependence is the source-faithful
`exp (O(c log T))` factor. -/
theorem exists_norm_hughesYoungRightContourWeight_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (t u c : ℝ), 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (|t| + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 8 := by
  obtain ⟨C, hC, hgamma⟩ := exists_norm_hughesYoungGammaRatioShift_le
  refine ⟨C, hC, ?_⟩
  intro t u c hc hc1
  let w : ℂ := (c : ℂ) + (u : ℂ) * I
  have hw : c ≤ ‖w‖ := by
    have hre := Complex.abs_re_le_norm w
    simpa [w, abs_of_pos hc] using hre
  have hwpos : 0 < ‖w‖ := hc.trans_le hw
  have hgauss : ‖Complex.exp (100 * w ^ 2)‖ =
      Real.exp (100 * c ^ 2 - 100 * u ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [w, pow_two, Complex.mul_re]
    ring
  have hwSq : ‖w‖ ^ 2 = c ^ 2 + u ^ 2 := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg w)]
    simp [w, Complex.normSq_add_mul_I]
  have haux : ‖hughesYoungAuxiliaryZero w‖ ≤ (25 + 8 * u ^ 2) ^ 4 := by
    unfold hughesYoungAuxiliaryZero
    rw [norm_pow]
    have hbase : ‖1 - 4 * w ^ 2‖ ≤ 25 + 8 * u ^ 2 := by
      calc
        ‖1 - 4 * w ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖4 * w ^ 2‖ := norm_sub_le _ _
        _ = 1 + 4 * ‖w‖ ^ 2 := by simp [norm_pow]
        _ = 1 + 4 * (c ^ 2 + u ^ 2) := by rw [hwSq]
        _ ≤ 25 + 8 * u ^ 2 := by nlinarith [sq_nonneg u]
    gcongr
  have hpoly := norm_hughesYoungPolynomialRatioShift_le t u c hc.le hc1
  have hgamma' := hgamma t u c hc.le hc1
  rw [hughesYoungRightContourWeight_shift_eq]
  change ‖(Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w) *
      hughesYoungPolynomialRatioShift t c u *
      hughesYoungGammaRatioShift t c u / w‖ ≤ _
  rw [norm_div, norm_mul, norm_mul, norm_mul, hgauss]
  calc
    Real.exp (100 * c ^ 2 - 100 * u ^ 2) * ‖hughesYoungAuxiliaryZero w‖ *
          ‖hughesYoungPolynomialRatioShift t c u‖ *
          ‖hughesYoungGammaRatioShift t c u‖ / ‖w‖
        ≤ Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
          (25 + 8 * u ^ 2) ^ 4 *
          (25 + 8 * u ^ 2) ^ 4 *
          Real.exp
            (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) /
          ‖w‖ := by gcongr
    _ ≤ Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
          (25 + 8 * u ^ 2) ^ 4 *
          (25 + 8 * u ^ 2) ^ 4 *
          Real.exp
            (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) /
          c := by
      exact div_le_div_of_nonneg_left (by positivity) hc hw
    _ = c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (|t| + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 8 := by
      rw [div_eq_mul_inv]
      calc
        Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
              (25 + 8 * u ^ 2) ^ 4 *
              (25 + 8 * u ^ 2) ^ 4 *
              Real.exp
                (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2) * c⁻¹ =
            c⁻¹ *
              (Real.exp (100 * c ^ 2 - 100 * u ^ 2) *
                Real.exp
                  (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2)) *
              (25 + 8 * u ^ 2) ^ 8 := by ring
        _ = c⁻¹ * Real.exp
              ((100 * c ^ 2 - 100 * u ^ 2) +
                (4 * C * c * Real.log (|t| + |u| + 2) + 16 * u ^ 2)) *
              (25 + 8 * u ^ 2) ^ 8 := by
          rw [← Real.exp_add]
        _ = _ := by
          congr 2
          ring

/-- On the physical-height support the only occurrence of the height variable
in the small-line bound may be replaced by the common dyadic height `T`.
This is the form used before taking Fourier derivatives in the Hughes--Young
cleaning step. -/
theorem exists_norm_hughesYoungRightContourWeight_shift_le_on_height_support :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t u c : ℝ), 1 ≤ T →
      t ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 8 := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le
  refine ⟨C, hC, ?_⟩
  intro T t u c hT ht hc hc1
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have habst : |t| ≤ 4 * T := by
    simpa [abs_of_nonneg ht0] using ht.2
  have harg : |t| + |u| + 2 ≤ 4 * T + |u| + 2 := by linarith
  have hargPos : 0 < |t| + |u| + 2 := by positivity
  have hlog : Real.log (|t| + |u| + 2) ≤
      Real.log (4 * T + |u| + 2) :=
    Real.log_le_log hargPos harg
  refine (hbound t u c hc hc1).trans ?_
  gcongr

/-- Uniform frequency-derivative estimate for the cleaned height transform on
a small positive contour.  It records exactly the `T^(j+1)` Fourier-moment
cost and leaves the source-faithful `exp (O(c log(T+|u|)))` loss explicit. -/
theorem exists_norm_iteratedDeriv_hughesYoungHeightTransform_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (T u c : ℝ), 1 ≤ T → 0 < c → c ≤ 1 →
      ∀ (j : ℕ) (xi : ℝ),
      ‖iteratedDeriv j (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 * T / 4) * ((4 * T) ^ j *
          (c⁻¹ * Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (4 * T + |u| + 2)) *
            (25 + 8 * u ^ 2) ^ 8)) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_on_height_support
  refine ⟨C, hC, ?_⟩
  intro T u c hT hc hc1 j xi
  apply norm_iteratedDeriv_hughesYoungHeightTransform_le
    (lt_of_lt_of_le (by norm_num) hT) hc u
  intro t ht
  exact hbound T t u c hT ht hc hc1

/-- Elementary separation of the physical height from the Mellin ordinate in
the logarithm appearing in the horizontal Gamma-shift bound. -/
theorem log_four_mul_add_abs_add_two_le
    {T : ℝ} (hT : 1 ≤ T) (u : ℝ) :
    Real.log (4 * T + |u| + 2) ≤
      Real.log T + Real.log (6 * (|u| + 1)) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hu0 : 0 ≤ |u| := abs_nonneg u
  have hcoef : 0 ≤ 6 * T - 1 := by linarith
  have hmul : 0 ≤ (6 * T - 1) * |u| := mul_nonneg hcoef hu0
  have harg : 4 * T + |u| + 2 ≤ T * (6 * (|u| + 1)) := by
    nlinarith
  have hleft : 0 < 4 * T + |u| + 2 := by positivity
  have hright : 0 < 6 * (|u| + 1) := by positivity
  calc
    Real.log (4 * T + |u| + 2) ≤
        Real.log (T * (6 * (|u| + 1))) :=
      Real.log_le_log hleft harg
    _ = Real.log T + Real.log (6 * (|u| + 1)) := by
      rw [Real.log_mul hTpos.ne' hright.ne']

/-- Source-scale form of the small-contour kernel estimate.  The complete
height dependence is now the real power `T^(4 C c)`; the remaining factor is
an explicit rapidly decreasing function of the Mellin ordinate. -/
theorem exists_norm_hughesYoungRightContourWeight_shift_le_height_power :
    ∃ C : ℝ, 0 < C ∧ ∀ (T t u c : ℝ), 1 ≤ T →
      t ∈ Set.Icc (T / 4) (4 * T) → 0 < c → c ≤ 1 →
      ‖hughesYoungRightContourWeight t c u‖ ≤
        c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_on_height_support
  refine ⟨C, hC, ?_⟩
  intro T t u c hT ht hc hc1
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hlog := log_four_mul_add_abs_add_two_le hT u
  refine (hbound T t u c hT ht hc hc1).trans ?_
  have hk : 0 ≤ 4 * C * c :=
    mul_nonneg (mul_nonneg (by positivity) hC.le) hc.le
  have hexp :
      Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (4 * T + |u| + 2)) ≤
        Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c *
              (Real.log T + Real.log (6 * (|u| + 1)))) := by
    apply Real.exp_le_exp.mpr
    have hscaled := mul_le_mul_of_nonneg_left hlog hk
    linarith
  calc
    c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c * Real.log (4 * T + |u| + 2)) *
          (25 + 8 * u ^ 2) ^ 8
        ≤ c⁻¹ * Real.exp
          (100 * c ^ 2 - 84 * u ^ 2 +
            4 * C * c *
              (Real.log T + Real.log (6 * (|u| + 1)))) *
          (25 + 8 * u ^ 2) ^ 8 := by
      gcongr
    _ = c⁻¹ * T ^ (4 * C * c) *
          (Real.exp
            (100 * c ^ 2 - 84 * u ^ 2 +
              4 * C * c * Real.log (6 * (|u| + 1))) *
            (25 + 8 * u ^ 2) ^ 8) := by
      have heq :
          Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c *
                  (Real.log T + Real.log (6 * (|u| + 1)))) =
            Real.exp (Real.log T * (4 * C * c)) *
              Real.exp
                (100 * c ^ 2 - 84 * u ^ 2 +
                  4 * C * c * Real.log (6 * (|u| + 1))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [Real.rpow_def_of_pos hTpos]
      rw [heq]
      ring

/-- Frequency derivatives of the cleaned height transform with the height
power separated.  This is the quantitative Fourier statement corresponding
to Hughes--Young (65) after shifting to the small contour. -/
theorem exists_norm_iteratedDeriv_hughesYoungHeightTransform_shift_le_height_power :
    ∃ C : ℝ, 0 < C ∧ ∀ (T u c : ℝ), 1 ≤ T → 0 < c → c ≤ 1 →
      ∀ (j : ℕ) (xi : ℝ),
      ‖iteratedDeriv j (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 * T / 4) * ((4 * T) ^ j *
          (c⁻¹ * T ^ (4 * C * c) *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_hughesYoungRightContourWeight_shift_le_height_power
  refine ⟨C, hC, ?_⟩
  intro T u c hT hc hc1 j xi
  apply norm_iteratedDeriv_hughesYoungHeightTransform_le
    (lt_of_lt_of_le (by norm_num) hT) hc u
  intro t ht
  exact hbound T t u c hT ht hc hc1

/-- The explicit `1/T` in Hughes--Young (70) cancels the physical length of
the height integral.  The remaining `j`-th frequency derivative costs exactly
`(4T)^j`, before composition with the fixed-shift logarithm. -/
theorem exists_norm_one_div_mul_iteratedDeriv_hughesYoungHeightTransform_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (T u c : ℝ), 1 ≤ T → 0 < c → c ≤ 1 →
      ∀ (j : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv j (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ j *
          (c⁻¹ * T ^ (4 * C * c) *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8))) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_norm_iteratedDeriv_hughesYoungHeightTransform_shift_le_height_power
  refine ⟨C, hC, ?_⟩
  intro T u c hT hc hc1 j xi
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  rw [norm_mul, norm_div, norm_one, norm_real, Real.norm_eq_abs,
    abs_of_pos hTpos]
  calc
    (1 / T) * ‖iteratedDeriv j (hughesYoungHeightTransform T c u) xi‖
        ≤ (1 / T) *
          ((15 * T / 4) * ((4 * T) ^ j *
            (c⁻¹ * T ^ (4 * C * c) *
              (Real.exp
                (100 * c ^ 2 - 84 * u ^ 2 +
                  4 * C * c * Real.log (6 * (|u| + 1))) *
                (25 + 8 * u ^ 2) ^ 8)))) := by
      exact mul_le_mul_of_nonneg_left (hbound T u c hT hc hc1 j xi)
        (by positivity)
    _ = (15 / 4 : ℝ) * ((4 * T) ^ j *
          (c⁻¹ * T ^ (4 * C * c) *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8))) := by
      field_simp [hTpos.ne']

/-! ## Uniform Faà di Bruno control of the shifted height transform -/

/-- Exact all-orders Faà di Bruno expansion for the height transform after
the frozen Hughes--Young logarithmic shift.  This is the differential
identity underlying equation (70), before any majorization. -/
theorem iteratedDeriv_hughesYoungHeightTransform_comp_shift_eq
    {T c u Y y r : ℝ} (hT : 0 < T) (hc : 0 < c) (hY : 0 < Y)
    (hyLower : Y ≤ y) (hr : |r| ≤ Y / 2) (n : ℕ) :
    iteratedDeriv n
        (fun z : ℝ =>
          hughesYoungHeightTransform T c u (-Real.log (1 + r / z))) y =
      ∑ p : OrderedFinpartition n,
        (∏ j, iteratedDeriv (p.partSize j)
          (fun z : ℝ => -Real.log (1 + r / z)) y) •
          iteratedDeriv p.length (hughesYoungHeightTransform T c u)
            (-Real.log (1 + r / y)) := by
  have hyPos : 0 < y := hY.trans_le hyLower
  have hrLower : -(Y / 2) ≤ r := neg_le_of_abs_le hr
  have harg : 0 < 1 + r / y := by
    rw [div_eq_mul_inv]
    have hyInv : 0 < y⁻¹ := inv_pos.mpr hyPos
    have hyr : 0 < y + r := by linarith
    have heq : 1 + r * y⁻¹ = (y + r) * y⁻¹ := by
      field_simp [hyPos.ne']
    rw [heq]
    exact mul_pos hyr hyInv
  have hinner : ContDiffAt ℝ ∞ (fun z : ℝ => 1 + r / z) y := by
    exact contDiffAt_const.add
      (contDiffAt_const.div contDiffAt_id hyPos.ne')
  have hphase : ContDiffAt ℝ ∞
      (fun z : ℝ => -Real.log (1 + r / z)) y :=
    ((Real.contDiffAt_log.2 harg.ne').comp y hinner).neg
  have hheight : ContDiffAt ℝ ∞
      (hughesYoungHeightTransform T c u) (-Real.log (1 + r / y)) :=
    (contDiff_hughesYoungHeightTransform hT hc u).contDiffAt
  simpa only [Function.comp_apply] using
    iteratedDeriv_scomp_eq_sum_orderedFinpartition
      (g := hughesYoungHeightTransform T c u)
      (f := fun z : ℝ => -Real.log (1 + r / z))
      (x := y) hheight hphase
      (show (n : ℕ∞ω) ≤ ∞ from mod_cast le_top)

/-- The physical derivative scale distributes exactly over the blocks of an
ordered finite partition. -/
theorem OrderedFinpartition.pow_mul_norm_prod_eq
    {n : ℕ} (p : OrderedFinpartition n) (y : ℝ)
    (a : Fin p.length → ℝ) :
    |y| ^ n * ‖∏ j, a j‖ =
      ∏ j, (|y| ^ p.partSize j * ‖a j‖) := by
  have hpow : ∏ j, |y| ^ p.partSize j = |y| ^ n := by
    rw [Finset.prod_pow_eq_pow_sum,
      RiemannZeta.GuthMaynard.OrderedFinpartition.sum_partSize p]
  rw [norm_prod, ← hpow, Finset.prod_mul_distrib]

/-- Product form of the shifted logarithmic phase bound for a single
Faà di Bruno partition. -/
theorem norm_hughesYoung_shift_phase_partition_le
    {n : ℕ} (p : OrderedFinpartition n) {Y y r : ℝ} (hY : 0 < Y)
    (hyLower : Y ≤ y) (hyUpper : y ≤ 2 * Y)
    (hr : |r| ≤ Y / 2) :
    |y| ^ n * ‖∏ j, iteratedDeriv (p.partSize j)
        (fun z : ℝ => -Real.log (1 + r / z)) y‖ ≤
      (∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j)) *
        (|r| / Y) ^ p.length := by
  rw [RiemannZeta.GuthMaynard.OrderedFinpartition.pow_mul_norm_prod_eq p]
  calc
    ∏ j, (|y| ^ p.partSize j *
          ‖iteratedDeriv (p.partSize j)
            (fun z : ℝ => -Real.log (1 + r / z)) y‖) ≤
        ∏ j, (hughesYoungShiftPhaseDerivativeConstant (p.partSize j) *
          (|r| / Y)) := by
      apply Finset.prod_le_prod
      · intro j _hj
        positivity
      · intro j _hj
        exact norm_iteratedDeriv_neg_log_one_add_shift_div_le
          (p.partSize_pos j) hY hyLower hyUpper hr
    _ = (∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j)) *
        ∏ _j : Fin p.length, (|r| / Y) := Finset.prod_mul_distrib
    _ = (∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j)) *
        (|r| / Y) ^ p.length := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The Hughes--Young shift-range inequality converts every retained
Faà di Bruno block into one power of the common equation-(2) parameter. -/
theorem four_mul_height_pow_mul_shift_ratio_pow_le
    {T R P : ℝ} {k n : ℕ} (hT : 0 ≤ T) (hR : 0 ≤ R)
    (hP : 1 ≤ P) (hTR : T * R ≤ P) (hkn : k ≤ n) :
    (4 * T) ^ k * R ^ k ≤ 4 ^ k * P ^ n := by
  have hTR0 : 0 ≤ T * R := mul_nonneg hT hR
  have hkpow : (T * R) ^ k ≤ P ^ k :=
    pow_le_pow_left₀ hTR0 hTR k
  have hmono : P ^ k ≤ P ^ n := pow_le_pow_right₀ hP hkn
  calc
    (4 * T) ^ k * R ^ k = 4 ^ k * (T * R) ^ k := by ring
    _ ≤ 4 ^ k * P ^ k := by gcongr
    _ ≤ 4 ^ k * P ^ n := by gcongr

/-- A single Faà di Bruno summand satisfies the uniform Hughes--Young
equation-(2) profile once the height-transform derivatives are bounded by a
common envelope `A`. -/
theorem norm_hughesYoung_height_shift_partition_le
    {T c u Y y r P A : ℝ} {n : ℕ} (p : OrderedFinpartition n)
    (hT : 1 ≤ T) (hY : 0 < Y) (hyLower : Y ≤ y) (hyUpper : y ≤ 2 * Y)
    (hr : |r| ≤ Y / 2) (hP : 1 ≤ P) (hTR : T * (|r| / Y) ≤ P)
    (hA : 0 ≤ A)
    (hheight : ∀ (j : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv j (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ j * A)) :
    |y| ^ n * ‖(1 / (T : ℂ)) *
        ((∏ j, iteratedDeriv (p.partSize j)
          (fun z : ℝ => -Real.log (1 + r / z)) y) •
          iteratedDeriv p.length (hughesYoungHeightTransform T c u)
            (-Real.log (1 + r / y)))‖ ≤
      ((15 / 4 : ℝ) * 4 ^ p.length *
        ∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j)) *
        A * P ^ n := by
  let phaseProduct : ℝ := ∏ j, iteratedDeriv (p.partSize j)
    (fun z : ℝ => -Real.log (1 + r / z)) y
  let heightDerivative : ℂ :=
    iteratedDeriv p.length (hughesYoungHeightTransform T c u)
      (-Real.log (1 + r / y))
  have hscale : (1 / (T : ℂ)) * (phaseProduct • heightDerivative) =
      phaseProduct • ((1 / (T : ℂ)) * heightDerivative) := by
    exact Algebra.mul_smul_comm phaseProduct (1 / (T : ℂ)) heightDerivative
  have hphase : |y| ^ n * ‖phaseProduct‖ ≤
      (∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j)) *
        (|r| / Y) ^ p.length := by
    exact norm_hughesYoung_shift_phase_partition_le
      p hY hyLower hyUpper hr
  have hheight' : ‖(1 / (T : ℂ)) * heightDerivative‖ ≤
      (15 / 4 : ℝ) * ((4 * T) ^ p.length * A) :=
    hheight p.length (-Real.log (1 + r / y))
  have hconstants : 0 ≤
      ∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j) := by
    apply Finset.prod_nonneg
    intro j _hj
    exact (hughesYoungShiftPhaseDerivativeConstant_pos
      (p.partSize_pos j)).le
  have hscalePow : (4 * T) ^ p.length * (|r| / Y) ^ p.length ≤
      4 ^ p.length * P ^ n :=
    four_mul_height_pow_mul_shift_ratio_pow_le
      (le_trans (by norm_num) hT) (div_nonneg (abs_nonneg _) hY.le)
      hP hTR p.length_le
  rw [hscale, norm_smul]
  change |y| ^ n * (‖phaseProduct‖ *
    ‖(1 / (T : ℂ)) * heightDerivative‖) ≤ _
  calc
    |y| ^ n * (‖phaseProduct‖ *
        ‖(1 / (T : ℂ)) * heightDerivative‖) =
        (|y| ^ n * ‖phaseProduct‖) *
          ‖(1 / (T : ℂ)) * heightDerivative‖ := by ring
    _ ≤ ((∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j)) *
          (|r| / Y) ^ p.length) *
        ((15 / 4 : ℝ) * ((4 * T) ^ p.length * A)) := by
      exact mul_le_mul hphase hheight' (norm_nonneg _) (by positivity)
    _ = ((15 / 4 : ℝ) *
          (∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j)) * A) *
        ((4 * T) ^ p.length * (|r| / Y) ^ p.length) := by ring
    _ ≤ ((15 / 4 : ℝ) *
          (∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j)) * A) *
        (4 ^ p.length * P ^ n) := by
      exact mul_le_mul_of_nonneg_left hscalePow (by positivity)
    _ = ((15 / 4 : ℝ) * 4 ^ p.length *
          ∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j)) *
        A * P ^ n := by ring

/-- Uniform all-orders bound for the full shifted height transform.  Unlike a
compactness argument, the constant depends only on the derivative order; all
height, shift, contour, and Mellin-ordinate dependence is explicit. -/
theorem norm_iteratedDeriv_hughesYoung_height_shift_le
    {T c u Y y r P A : ℝ} {n : ℕ}
    (hT : 1 ≤ T) (hc : 0 < c) (hY : 0 < Y)
    (hyLower : Y ≤ y) (hyUpper : y ≤ 2 * Y)
    (hr : |r| ≤ Y / 2) (hP : 1 ≤ P) (hTR : T * (|r| / Y) ≤ P)
    (hA : 0 ≤ A)
    (hheight : ∀ (j : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv j (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ j * A)) :
    |y| ^ n * ‖(1 / (T : ℂ)) *
        iteratedDeriv n
          (fun z : ℝ =>
            hughesYoungHeightTransform T c u (-Real.log (1 + r / z))) y‖ ≤
      hughesYoungShiftCompositionConstant n * A * P ^ n := by
  have hexact := iteratedDeriv_hughesYoungHeightTransform_comp_shift_eq
    (u := u) (lt_of_lt_of_le zero_lt_one hT) hc hY hyLower hr n
  rw [hexact, Finset.mul_sum]
  calc
    |y| ^ n * ‖∑ p : OrderedFinpartition n,
        (1 / (T : ℂ)) *
          ((∏ j, iteratedDeriv (p.partSize j)
            (fun z : ℝ => -Real.log (1 + r / z)) y) •
            iteratedDeriv p.length (hughesYoungHeightTransform T c u)
              (-Real.log (1 + r / y)))‖ ≤
        |y| ^ n * ∑ p : OrderedFinpartition n,
          ‖(1 / (T : ℂ)) *
            ((∏ j, iteratedDeriv (p.partSize j)
              (fun z : ℝ => -Real.log (1 + r / z)) y) •
              iteratedDeriv p.length (hughesYoungHeightTransform T c u)
                (-Real.log (1 + r / y)))‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = ∑ p : OrderedFinpartition n,
        |y| ^ n * ‖(1 / (T : ℂ)) *
          ((∏ j, iteratedDeriv (p.partSize j)
            (fun z : ℝ => -Real.log (1 + r / z)) y) •
            iteratedDeriv p.length (hughesYoungHeightTransform T c u)
              (-Real.log (1 + r / y)))‖ := by
      rw [Finset.mul_sum]
    _ ≤ ∑ p : OrderedFinpartition n,
        (((15 / 4 : ℝ) * 4 ^ p.length *
          ∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j)) *
          A * P ^ n) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact norm_hughesYoung_height_shift_partition_le p hT hY
        hyLower hyUpper hr hP hTR hA hheight
    _ = (∑ p : OrderedFinpartition n,
        (15 / 4 : ℝ) * 4 ^ p.length *
          ∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j)) *
        A * P ^ n := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ hughesYoungShiftCompositionConstant n * A * P ^ n := by
      have hsum : ∑ p : OrderedFinpartition n,
          (15 / 4 : ℝ) * 4 ^ p.length *
            ∏ j, hughesYoungShiftPhaseDerivativeConstant (p.partSize j) ≤
          hughesYoungShiftCompositionConstant n := by
        unfold hughesYoungShiftCompositionConstant
        linarith
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hsum hA) (by positivity)

/-- Source-uniform Hughes--Young equation-(70) derivative profile for the
height-dependent logarithmic shift.  The witness `C` is universal; in
particular it is independent of `T`, the shift, the dyadic scale, the Mellin
ordinate, and the derivative order. -/
theorem exists_norm_iteratedDeriv_hughesYoung_height_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (T u c Y y r P : ℝ),
      1 ≤ T → 0 < c → c ≤ 1 → 0 < Y → Y ≤ y → y ≤ 2 * Y →
      |r| ≤ Y / 2 → 1 ≤ P → T * (|r| / Y) ≤ P →
      ∀ n : ℕ,
      |y| ^ n * ‖(1 / (T : ℂ)) *
          iteratedDeriv n
            (fun z : ℝ =>
              hughesYoungHeightTransform T c u (-Real.log (1 + r / z))) y‖ ≤
        hughesYoungShiftCompositionConstant n *
          (c⁻¹ * T ^ (4 * C * c) *
            (Real.exp
              (100 * c ^ 2 - 84 * u ^ 2 +
                4 * C * c * Real.log (6 * (|u| + 1))) *
              (25 + 8 * u ^ 2) ^ 8)) * P ^ n := by
  obtain ⟨C, hC, hheight⟩ :=
    exists_norm_one_div_mul_iteratedDeriv_hughesYoungHeightTransform_le
  refine ⟨C, hC, ?_⟩
  intro T u c Y y r P hT hc hc1 hY hyLower hyUpper hr hP hTR n
  let A : ℝ := c⁻¹ * T ^ (4 * C * c) *
    (Real.exp
      (100 * c ^ 2 - 84 * u ^ 2 +
        4 * C * c * Real.log (6 * (|u| + 1))) *
      (25 + 8 * u ^ 2) ^ 8)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  exact norm_iteratedDeriv_hughesYoung_height_shift_le hT hc hY
    hyLower hyUpper hr hP hTR hA
    (fun j xi => hheight T u c hT hc hc1 j xi)

/-! ## Assembly of the fixed-shift DFI source weight -/

/-- The variable-dependent part of the cleaned Hughes--Young weight after
the arithmetic scalar has been removed. -/
noncomputable def hughesYoungDFICore
    (T c u X Y : ℝ) (h k : ℕ) (r : ℤ) (x y : ℝ) : ℂ :=
  let s : ℂ := (1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)
  hughesYoungLocalizedOneFactor X h s x *
    (hughesYoungLocalizedOneFactor Y k s y *
      ((1 / (T : ℂ)) *
        hughesYoungHeightTransform T c u
          (-Real.log (1 + (r : ℝ) / y))))

/-- Exact scalar separation of equation (70). -/
theorem hughesYoungCleanedShiftWeight_eq_staticScalar_mul_dfiCore
    (T c u X Y : ℝ) (h k : ℕ) (r : ℤ) (x y : ℝ) :
    hughesYoungCleanedShiftWeight T c u X Y h k r x y =
      hughesYoungLocalizedStaticScalar T h k *
        hughesYoungDFICore T c u X Y h k r x y := by
  unfold hughesYoungCleanedShiftWeight
  rw [show hughesYoungLocalizedStaticWeight T c u X Y h k x y =
      hughesYoungLocalizedStaticScalar T h k *
        hughesYoungLocalizedLogKernel X Y h k
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) x y from
    hughesYoungLocalizedStaticWeight_eq_scalar_mul_kernel
      T c u X Y h k x y]
  unfold hughesYoungDFICore
    hughesYoungLocalizedLogKernel hughesYoungLocalizedOneFactor
  dsimp only
  ring

/-- The `y`-dependent half of the DFI core. -/
noncomputable def hughesYoungDFICoreY
    (T c u Y : ℝ) (k : ℕ) (r : ℤ) (y : ℝ) : ℂ :=
  let s : ℂ := (1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)
  hughesYoungLocalizedOneFactor Y k s y *
    ((1 / (T : ℂ)) *
      hughesYoungHeightTransform T c u
        (-Real.log (1 + (r : ℝ) / y)))

theorem hughesYoungDFICore_eq_separated
    (T c u X Y : ℝ) (h k : ℕ) (r : ℤ) (x y : ℝ) :
    hughesYoungDFICore T c u X Y h k r x y =
      hughesYoungLocalizedOneFactor X h
          ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) x *
        hughesYoungDFICoreY T c u Y k r y := by
  rfl

theorem contDiff_hughesYoungDFICoreY
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {Y : ℝ} (hY : 0 < Y) {k : ℕ} (hk : 0 < k) (r : ℤ)
    (hr : |(r : ℝ)| < Y) :
    ContDiff ℝ ∞ (hughesYoungDFICoreY T c u Y k r) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y < Y
  · have hnhds : Set.Iio Y ∈ nhds y := Iio_mem_nhds hy
    have hzero : hughesYoungDFICoreY T c u Y k r =ᶠ[nhds y]
        (fun _ => 0) := by
      filter_upwards [hnhds] with z hz
      unfold hughesYoungDFICoreY hughesYoungLocalizedOneFactor
      have hcut : hughesYoungDyadicCutoffAt Y z = 0 :=
        hughesYoungDyadicCutoff_eq_zero_of_le_one
          ((div_le_one hY).2 hz.le)
      rw [hcut]
      simp
    exact contDiffAt_const.congr_of_eventuallyEq hzero
  · have hyLower : Y ≤ y := le_of_not_gt hy
    have hyPos : 0 < y := hY.trans_le hyLower
    have hrLower : -Y < (r : ℝ) := by
      have hneg : -(Y : ℝ) < -|(r : ℝ)| := neg_lt_neg hr
      exact hneg.trans_le (neg_abs_le (r : ℝ))
    have hsum : 0 < y + (r : ℝ) := by linarith
    have harg : 0 < 1 + (r : ℝ) / y := by
      rw [one_add_div hyPos.ne']
      exact div_pos hsum hyPos
    have hinner : ContDiffAt ℝ ∞
        (fun z : ℝ => 1 + (r : ℝ) / z) y :=
      contDiffAt_const.add (contDiffAt_const.div contDiff_id.contDiffAt hyPos.ne')
    have hlog : ContDiffAt ℝ ∞
        (fun z : ℝ => -Real.log (1 + (r : ℝ) / z)) y :=
      ((Real.contDiffAt_log.2 harg.ne').comp y hinner).neg
    have hheight : ContDiffAt ℝ ∞
        (fun z : ℝ => hughesYoungHeightTransform T c u
          (-Real.log (1 + (r : ℝ) / z))) y :=
      (contDiff_hughesYoungHeightTransform hT hc u).contDiffAt.comp y hlog
    unfold hughesYoungDFICoreY
    exact (contDiff_hughesYoungLocalizedOneFactor hY
        (by exact_mod_cast hk) _).contDiffAt.mul
      (contDiffAt_const.mul hheight)

/-- Exact Leibniz expansion of the `y`-dependent half of the DFI core. -/
theorem iteratedDeriv_hughesYoungDFICoreY
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {Y : ℝ} (hY : 0 < Y) {k : ℕ} (hk : 0 < k) (r : ℤ)
    (hr : |(r : ℝ)| < Y) (j : ℕ) {y : ℝ} (hyLower : Y ≤ y) :
    iteratedDeriv j (hughesYoungDFICoreY T c u Y k r) y =
      ∑ q ∈ Finset.range (j + 1),
        (j.choose q : ℂ) *
          iteratedDeriv q
            (hughesYoungLocalizedOneFactor Y k
              ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y *
          ((1 / (T : ℂ)) *
            iteratedDeriv (j - q)
              (fun z : ℝ => hughesYoungHeightTransform T c u
                (-Real.log (1 + (r : ℝ) / z))) y) := by
  let s : ℂ := (1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)
  let H : ℝ → ℂ := fun z => hughesYoungHeightTransform T c u
    (-Real.log (1 + (r : ℝ) / z))
  have hyPos : 0 < y := hY.trans_le hyLower
  have hrLower : -Y < (r : ℝ) := by
    have hneg : -(Y : ℝ) < -|(r : ℝ)| := neg_lt_neg hr
    exact hneg.trans_le (neg_abs_le (r : ℝ))
  have hsum : 0 < y + (r : ℝ) := by linarith
  have harg : 0 < 1 + (r : ℝ) / y := by
    rw [one_add_div hyPos.ne']
    exact div_pos hsum hyPos
  have hH : ContDiffAt ℝ ∞ H y :=
    (contDiff_hughesYoungHeightTransform hT hc u).contDiffAt.comp y
      (((Real.contDiffAt_log.2 harg.ne').comp y
        (contDiffAt_const.add
          (contDiffAt_const.div contDiff_id.contDiffAt hyPos.ne'))).neg)
  have hfactor : ContDiffAt ℝ j
      (hughesYoungLocalizedOneFactor Y k s) y :=
    (contDiff_hughesYoungLocalizedOneFactor hY
      (by exact_mod_cast hk) s).contDiffAt.of_le (by exact_mod_cast le_top)
  have hscaled : ContDiffAt ℝ j (fun z => (1 / (T : ℂ)) * H z) y :=
    (contDiffAt_const.mul hH).of_le (by exact_mod_cast le_top)
  change iteratedDeriv j
      ((hughesYoungLocalizedOneFactor Y k s) *
        fun z => (1 / (T : ℂ)) * H z) y = _
  rw [iteratedDeriv_mul hfactor hscaled]
  apply Finset.sum_congr rfl
  intro q _hq
  have horder : ((j - q : ℕ) : ℕ∞ω) ≤ ∞ := by
    apply WithTop.coe_le_coe.mpr
    exact le_top
  have hHq : ContDiffAt ℝ ((j - q : ℕ) : ℕ∞ω) H y :=
    hH.of_le horder
  rw [iteratedDeriv_const_mul (1 / (T : ℂ)) hHq]

/-- Order-dependent coefficient for the full `y`-factor of the
Hughes--Young/DFI source weight.  It is the Leibniz convolution of the
localized Mellin-factor profile with the shifted-height profile. -/
noncomputable def hughesYoungCoreYDerivativeProfile
    (Ccut : ℕ → ℝ) (u : ℝ) (j : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (j + 1),
    (j.choose q : ℝ) *
      hughesYoungOneFactorDerivativeProfile Ccut u q *
      hughesYoungShiftCompositionConstant (j - q)

theorem hughesYoungCoreYDerivativeProfile_pos
    (Ccut : ℕ → ℝ) (hcut : ∀ n, 0 < Ccut n) (u : ℝ) (j : ℕ) :
    0 < hughesYoungCoreYDerivativeProfile Ccut u j := by
  unfold hughesYoungCoreYDerivativeProfile
  apply Finset.sum_pos'
  · intro q hq
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (hughesYoungOneFactorDerivativeProfile_pos Ccut hcut u q).le)
      (le_trans (by norm_num)
        (one_le_hughesYoungShiftCompositionConstant (j - q)))
  · refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.choose_self, Nat.sub_self]
    norm_num
    exact mul_pos
      (hughesYoungOneFactorDerivativeProfile_pos Ccut hcut u j)
      (lt_of_lt_of_le zero_lt_one
        (one_le_hughesYoungShiftCompositionConstant 0))

/-- The complete `y`-factor has a uniform DFI derivative profile once the
height transform is supplied with its explicit Hughes--Young envelope. -/
theorem abs_pow_mul_norm_iteratedDeriv_hughesYoungDFICoreY_le
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (X : ℝ), 0 < X → ∀ x : ℝ,
      |x| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt X) x‖ ≤ Ccut n)
    {T c u Y y P A : ℝ} {k : ℕ} {r : ℤ} (j : ℕ)
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hY : 0 < Y) (hyLower : Y ≤ y) (hyUpper : y ≤ 2 * Y)
    (hk : 0 < k) (hkUpper : (k : ℝ) ≤ 2 * Y)
    (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 ≤ A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    |y| ^ j * ‖iteratedDeriv j (hughesYoungDFICoreY T c u Y k r) y‖ ≤
      hughesYoungCoreYDerivativeProfile Ccut u j * A * P ^ j := by
  have hrStrict : |(r : ℝ)| < Y := by linarith
  rw [iteratedDeriv_hughesYoungDFICoreY
    (lt_of_lt_of_le zero_lt_one hT) hc u hY hk r hrStrict j hyLower]
  calc
    |y| ^ j * ‖∑ q ∈ Finset.range (j + 1),
        (j.choose q : ℂ) *
          iteratedDeriv q
            (hughesYoungLocalizedOneFactor Y k
              ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y *
          ((1 / (T : ℂ)) *
            iteratedDeriv (j - q)
              (fun z : ℝ => hughesYoungHeightTransform T c u
                (-Real.log (1 + (r : ℝ) / z))) y)‖ ≤
        ∑ q ∈ Finset.range (j + 1), |y| ^ j *
          ‖(j.choose q : ℂ) *
            iteratedDeriv q
              (hughesYoungLocalizedOneFactor Y k
                ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y *
            ((1 / (T : ℂ)) *
              iteratedDeriv (j - q)
                (fun z : ℝ => hughesYoungHeightTransform T c u
                  (-Real.log (1 + (r : ℝ) / z))) y)‖ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _)
        (pow_nonneg (abs_nonneg y) j)
    _ ≤ ∑ q ∈ Finset.range (j + 1),
        ((j.choose q : ℝ) *
          hughesYoungOneFactorDerivativeProfile Ccut u q *
          hughesYoungShiftCompositionConstant (j - q)) * A * P ^ j := by
      apply Finset.sum_le_sum
      intro q hq
      have hqj : q ≤ j := by
        have : q < j + 1 := Finset.mem_range.mp hq
        omega
      have hone :=
        abs_pow_mul_norm_iteratedDeriv_hughesYoungLocalizedOneFactor_profile_le
          (u := u) Ccut hcut hY hyLower (by exact_mod_cast hk) hkUpper hc hc1 q
      have hshift := norm_iteratedDeriv_hughesYoung_height_shift_le
        (n := j - q) hT hc hY hyLower hyUpper hr hP hTR hA hheight
      have hpow : P ^ (j - q) ≤ P ^ j :=
        pow_le_pow_right₀ hP (Nat.sub_le j q)
      have hnormeq :
          ‖(j.choose q : ℂ) *
              iteratedDeriv q
                (hughesYoungLocalizedOneFactor Y k
                  ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y *
              ((1 / (T : ℂ)) *
                iteratedDeriv (j - q)
                  (fun z : ℝ => hughesYoungHeightTransform T c u
                    (-Real.log (1 + (r : ℝ) / z))) y)‖ =
            (j.choose q : ℝ) *
            ‖iteratedDeriv q
              (hughesYoungLocalizedOneFactor Y k
                ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y‖ *
            ‖(1 / (T : ℂ)) *
              iteratedDeriv (j - q)
                (fun z : ℝ => hughesYoungHeightTransform T c u
                  (-Real.log (1 + (r : ℝ) / z))) y‖ := by
        simp only [norm_mul, Complex.norm_natCast]
      rw [hnormeq]
      have hfactorProfileNonneg :
          0 ≤ hughesYoungOneFactorDerivativeProfile Ccut u q :=
        (hughesYoungOneFactorDerivativeProfile_pos Ccut
          (fun n => (hcut n).1) u q).le
      have hshiftProfileNonneg :
          0 ≤ hughesYoungShiftCompositionConstant (j - q) :=
        le_trans (by norm_num)
          (one_le_hughesYoungShiftCompositionConstant (j - q))
      have hypow : |y| ^ j = |y| ^ q * |y| ^ (j - q) := by
        rw [← pow_add, Nat.add_sub_of_le hqj]
      rw [hypow]
      calc
        (|y| ^ q * |y| ^ (j - q)) *
            ((j.choose q : ℝ) *
              ‖iteratedDeriv q
                (hughesYoungLocalizedOneFactor Y k
                  ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y‖ *
              ‖(1 / (T : ℂ)) *
                iteratedDeriv (j - q)
                  (fun z : ℝ => hughesYoungHeightTransform T c u
                    (-Real.log (1 + (r : ℝ) / z))) y‖) =
            (j.choose q : ℝ) *
              (|y| ^ q * ‖iteratedDeriv q
                (hughesYoungLocalizedOneFactor Y k
                  ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) y‖) *
              (|y| ^ (j - q) *
                ‖(1 / (T : ℂ)) *
                  iteratedDeriv (j - q)
                    (fun z : ℝ => hughesYoungHeightTransform T c u
                      (-Real.log (1 + (r : ℝ) / z))) y‖) := by ring
        _ ≤ (j.choose q : ℝ) *
              hughesYoungOneFactorDerivativeProfile Ccut u q *
              (hughesYoungShiftCompositionConstant (j - q) * A *
                P ^ (j - q)) := by gcongr
        _ = ((j.choose q : ℝ) *
              hughesYoungOneFactorDerivativeProfile Ccut u q *
              hughesYoungShiftCompositionConstant (j - q)) * A *
                P ^ (j - q) := by ring
        _ ≤ ((j.choose q : ℝ) *
              hughesYoungOneFactorDerivativeProfile Ccut u q *
              hughesYoungShiftCompositionConstant (j - q)) * A * P ^ j := by
          have hnonneg : 0 ≤ (j.choose q : ℝ) *
              hughesYoungOneFactorDerivativeProfile Ccut u q *
              hughesYoungShiftCompositionConstant (j - q) * A := by
            exact mul_nonneg
              (mul_nonneg (mul_nonneg (by positivity) hfactorProfileNonneg)
                hshiftProfileNonneg) hA
          exact mul_le_mul_of_nonneg_left hpow hnonneg
    _ = hughesYoungCoreYDerivativeProfile Ccut u j * A * P ^ j := by
      unfold hughesYoungCoreYDerivativeProfile
      rw [Finset.sum_mul, Finset.sum_mul]

theorem contDiff_uncurry_hughesYoungDFICore
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ)
    (hr : |(r : ℝ)| < Y) :
    ContDiff ℝ ∞ (Function.uncurry
      (hughesYoungDFICore T c u X Y h k r)) := by
  rw [show Function.uncurry (hughesYoungDFICore T c u X Y h k r) =
      fun p : ℝ × ℝ =>
        hughesYoungLocalizedOneFactor X h
            ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) p.1 *
          hughesYoungDFICoreY T c u Y k r p.2 by
    funext p
    exact hughesYoungDFICore_eq_separated T c u X Y h k r p.1 p.2]
  exact ((contDiff_hughesYoungLocalizedOneFactor hX
      (by exact_mod_cast hh) _).comp contDiff_fst).mul
    ((contDiff_hughesYoungDFICoreY hT hc u hY hk r hr).comp contDiff_snd)

/-- Exact mixed derivative of the fixed-shift DFI core. -/
theorem dfiMixedDeriv_hughesYoungDFICore
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (u : ℝ)
    {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (r : ℤ)
    (hr : |(r : ℝ)| < Y) (i j : ℕ) (x y : ℝ) :
    dfiMixedDeriv i j (hughesYoungDFICore T c u X Y h k r) x y =
      iteratedDeriv i
          (hughesYoungLocalizedOneFactor X h
            ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) x *
        iteratedDeriv j (hughesYoungDFICoreY T c u Y k r) y := by
  rw [show hughesYoungDFICore T c u X Y h k r =
      fun x' y' =>
        hughesYoungLocalizedOneFactor X h
            ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I)) x' *
          hughesYoungDFICoreY T c u Y k r y' by
    funext x' y'
    exact hughesYoungDFICore_eq_separated T c u X Y h k r x' y']
  exact dfiMixedDeriv_separated_product
    (contDiff_hughesYoungLocalizedOneFactor hX (by exact_mod_cast hh) _)
    (contDiff_hughesYoungDFICoreY hT hc u hY hk r hr) i j x y

/-- The fixed-shift Hughes--Young core satisfies the weighted mixed
derivative estimate that feeds DFI equation (2).  The only scale loss is
`P^(i+j)`; all dependence on the derivative orders and Mellin ordinate is
isolated in the two explicit profiles. -/
theorem abs_pow_mul_abs_pow_mul_norm_dfiMixedDeriv_hughesYoungDFICore_le
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (Z : ℝ), 0 < Z → ∀ z : ℝ,
      |z| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt Z) z‖ ≤ Ccut n)
    {T c u X Y x y P A : ℝ} {h k : ℕ} {r : ℤ} (i j : ℕ)
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 0 < X) (hxLower : X ≤ x)
    (hY : 0 < Y) (hyLower : Y ≤ y) (hyUpper : y ≤ 2 * Y)
    (hh : 0 < h) (hhUpper : (h : ℝ) ≤ 2 * X)
    (hk : 0 < k) (hkUpper : (k : ℝ) ≤ 2 * Y)
    (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 ≤ A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    |x| ^ i * |y| ^ j *
        ‖dfiMixedDeriv i j (hughesYoungDFICore T c u X Y h k r) x y‖ ≤
      hughesYoungOneFactorDerivativeProfile Ccut u i *
        hughesYoungCoreYDerivativeProfile Ccut u j * A * P ^ (i + j) := by
  have hrStrict : |(r : ℝ)| < Y := by linarith
  rw [dfiMixedDeriv_hughesYoungDFICore
    (lt_of_lt_of_le zero_lt_one hT) hc u hX hY hh hk r hrStrict i j x y,
    norm_mul]
  have hxBound :=
    abs_pow_mul_norm_iteratedDeriv_hughesYoungLocalizedOneFactor_profile_le
      (u := u) Ccut hcut hX hxLower (by exact_mod_cast hh) hhUpper hc hc1 i
  have hyBound := abs_pow_mul_norm_iteratedDeriv_hughesYoungDFICoreY_le
    Ccut hcut j hT hc hc1 hY hyLower hyUpper hk hkUpper hr hP hTR hA hheight
  have hxProfileNonneg :
      0 ≤ hughesYoungOneFactorDerivativeProfile Ccut u i :=
    (hughesYoungOneFactorDerivativeProfile_pos Ccut
      (fun n => (hcut n).1) u i).le
  have hyProfileNonneg :
      0 ≤ hughesYoungCoreYDerivativeProfile Ccut u j :=
    (hughesYoungCoreYDerivativeProfile_pos Ccut
      (fun n => (hcut n).1) u j).le
  have hpow : P ^ j ≤ P ^ (i + j) :=
    pow_le_pow_right₀ hP (Nat.le_add_left j i)
  calc
    |x| ^ i * |y| ^ j *
          (‖iteratedDeriv i
              (hughesYoungLocalizedOneFactor X h
                ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) x‖ *
            ‖iteratedDeriv j (hughesYoungDFICoreY T c u Y k r) y‖) =
        (|x| ^ i *
            ‖iteratedDeriv i
              (hughesYoungLocalizedOneFactor X h
                ((1 / 2 : ℂ) + ((c : ℂ) + (u : ℂ) * I))) x‖) *
          (|y| ^ j *
            ‖iteratedDeriv j (hughesYoungDFICoreY T c u Y k r) y‖) := by ring
    _ ≤ hughesYoungOneFactorDerivativeProfile Ccut u i *
          (hughesYoungCoreYDerivativeProfile Ccut u j * A * P ^ j) := by
      exact mul_le_mul hxBound hyBound (by positivity) hxProfileNonneg
    _ = (hughesYoungOneFactorDerivativeProfile Ccut u i *
          hughesYoungCoreYDerivativeProfile Ccut u j * A) * P ^ j := by ring
    _ ≤ (hughesYoungOneFactorDerivativeProfile Ccut u i *
          hughesYoungCoreYDerivativeProfile Ccut u j * A) * P ^ (i + j) := by
      exact mul_le_mul_of_nonneg_left hpow
        (mul_nonneg (mul_nonneg hxProfileNonneg hyProfileNonneg) hA)
    _ = hughesYoungOneFactorDerivativeProfile Ccut u i *
        hughesYoungCoreYDerivativeProfile Ccut u j * A * P ^ (i + j) := by ring

/-- The variable core is supported in the exact dyadic rectangle used by
DFI.  The height transform and logarithmic Mellin factors do not enlarge the
support supplied by the two cutoff factors. -/
theorem support_uncurry_hughesYoungDFICore_subset
    {T c u X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (r : ℤ) :
    Function.support (Function.uncurry
      (hughesYoungDFICore T c u X Y h k r)) ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
  intro p hp
  have hxcut : hughesYoungDyadicCutoffAt X p.1 ≠ 0 := by
    intro hz
    apply hp
    unfold Function.uncurry hughesYoungDFICore
      hughesYoungLocalizedOneFactor
    rw [hz]
    norm_num
  have hycut : hughesYoungDyadicCutoffAt Y p.2 ≠ 0 := by
    intro hz
    apply hp
    unfold Function.uncurry hughesYoungDFICore
      hughesYoungLocalizedOneFactor
    simp [hz]
  exact ⟨support_hughesYoungDyadicCutoffAt_subset hX hxcut,
    support_hughesYoungDyadicCutoffAt_subset hY hycut⟩

theorem hughesYoungDFICore_localizedBox
    {T c u X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (r : ℤ) :
    DFILocalizedBox (hughesYoungDFICore T c u X Y h k r) X Y :=
  ⟨support_uncurry_hughesYoungDFICore_subset hX hY h k r⟩

/-- Explicit equation-(2) profile of the normalized fixed-shift core.  The
factor `9` exactly compensates for the two DFI decay weights on the dyadic
box, since each reciprocal is at least `1/3`. -/
noncomputable def hughesYoungDFICoreDerivativeProfile
    (Ccut : ℕ → ℝ) (u A : ℝ) (i j : ℕ) : ℝ :=
  9 * hughesYoungOneFactorDerivativeProfile Ccut u i *
    hughesYoungCoreYDerivativeProfile Ccut u j * A

theorem hughesYoungDFICoreDerivativeProfile_pos
    (Ccut : ℕ → ℝ) (hcut : ∀ n, 0 < Ccut n)
    (u : ℝ) {A : ℝ} (hA : 0 < A) (i j : ℕ) :
    0 < hughesYoungDFICoreDerivativeProfile Ccut u A i j := by
  unfold hughesYoungDFICoreDerivativeProfile
  exact mul_pos
    (mul_pos (mul_pos (by norm_num)
      (hughesYoungOneFactorDerivativeProfile_pos Ccut hcut u i))
      (hughesYoungCoreYDerivativeProfile_pos Ccut hcut u j)) hA

/-! ### Gaussian normalization of the Mellin-ordinate profiles -/

/-- An explicit constant dominating `(x + 1)^n / exp x` for nonnegative
`x`, obtained term-by-term from the exponential series. -/
noncomputable def hughesYoungGaussianPowerConstant (n : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (n + 1),
    (n.choose q : ℝ) * (q.factorial : ℝ)

theorem hughesYoungGaussianPowerConstant_pos (n : ℕ) :
    0 < hughesYoungGaussianPowerConstant n := by
  unfold hughesYoungGaussianPowerConstant
  apply Finset.sum_pos'
  · intro q hq
    positivity
  · refine ⟨0, Finset.mem_range.mpr (by omega), ?_⟩
    simp

theorem pow_add_one_le_gaussianPowerConstant_mul_exp
    {x : ℝ} (hx : 0 ≤ x) (n : ℕ) :
    (x + 1) ^ n ≤ hughesYoungGaussianPowerConstant n * Real.exp x := by
  rw [add_pow]
  simp only [one_pow, mul_one]
  calc
    ∑ q ∈ Finset.range (n + 1), x ^ q * (n.choose q : ℝ) ≤
        ∑ q ∈ Finset.range (n + 1),
          (n.choose q : ℝ) * ((q.factorial : ℝ) * Real.exp x) := by
      apply Finset.sum_le_sum
      intro q hq
      have hfac : 0 < (q.factorial : ℝ) := by positivity
      have hseries := Real.pow_div_factorial_le_exp x hx q
      have hqpow : x ^ q ≤ (q.factorial : ℝ) * Real.exp x := by
        have := (div_le_iff₀ hfac).mp hseries
        nlinarith
      calc
        x ^ q * (n.choose q : ℝ) ≤
            ((q.factorial : ℝ) * Real.exp x) * (n.choose q : ℝ) :=
          mul_le_mul_of_nonneg_right hqpow (by positivity)
        _ = (n.choose q : ℝ) *
            ((q.factorial : ℝ) * Real.exp x) := by ring
    _ = hughesYoungGaussianPowerConstant n * Real.exp x := by
      unfold hughesYoungGaussianPowerConstant
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      ring

theorem abs_add_le_mul_sq_add_one
    (u a : ℝ) (ha : 0 ≤ a) :
    |u| + a ≤ (a + 1) * (u ^ 2 + 1) := by
  have habs : |u| ≤ u ^ 2 + 1 := by
    nlinarith [sq_nonneg (|u| - 1), sq_abs u]
  have hcross : 0 ≤ a * u ^ 2 := mul_nonneg ha (sq_nonneg u)
  nlinarith

theorem abs_add_pow_le_gaussian
    (u a : ℝ) (ha : 0 ≤ a) (n : ℕ) :
    (|u| + a) ^ n ≤
      (a + 1) ^ n * hughesYoungGaussianPowerConstant n * Real.exp (u ^ 2) := by
  have hbase := abs_add_le_mul_sq_add_one u a ha
  have hpow := pow_le_pow_left₀ (by positivity) hbase n
  have hgauss := pow_add_one_le_gaussianPowerConstant_mul_exp
    (sq_nonneg u) n
  calc
    (|u| + a) ^ n ≤ ((a + 1) * (u ^ 2 + 1)) ^ n := hpow
    _ = (a + 1) ^ n * (u ^ 2 + 1) ^ n := by rw [mul_pow]
    _ ≤ (a + 1) ^ n *
        (hughesYoungGaussianPowerConstant n * Real.exp (u ^ 2)) := by
      exact mul_le_mul_of_nonneg_left hgauss (pow_nonneg (by positivity) _)
    _ = (a + 1) ^ n * hughesYoungGaussianPowerConstant n *
        Real.exp (u ^ 2) := by ring

/-- A Mellin-ordinate-independent majorant for the one-factor derivative
profile after removing one Gaussian `exp (u^2)`. -/
noncomputable def hughesYoungGaussianOneFactorProfile
    (Ccut : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (n + 1),
    (n.choose q : ℝ) * Ccut q *
      (((3 : ℝ) + ((n - q : ℕ) : ℝ)) ^ (n - q) *
        hughesYoungGaussianPowerConstant (n - q) *
        2 ^ (3 / 2 : ℝ))

theorem hughesYoungGaussianOneFactorProfile_pos
    (Ccut : ℕ → ℝ) (hcut : ∀ n, 0 < Ccut n) (n : ℕ) :
    0 < hughesYoungGaussianOneFactorProfile Ccut n := by
  unfold hughesYoungGaussianOneFactorProfile
  apply Finset.sum_pos'
  · intro q hq
    exact mul_nonneg
      (mul_nonneg (by positivity) (hcut q).le)
      (mul_nonneg
        (mul_nonneg (pow_nonneg (by positivity) _)
          (hughesYoungGaussianPowerConstant_pos (n - q)).le)
        (Real.rpow_nonneg (by norm_num) _))
  · refine ⟨n, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.choose_self, Nat.sub_self]
    norm_num
    exact mul_pos (hcut n)
      (mul_pos (hughesYoungGaussianPowerConstant_pos 0)
        (Real.rpow_pos_of_pos (by norm_num) _))

theorem hughesYoungOneFactorDerivativeProfile_le_gaussian
    (Ccut : ℕ → ℝ) (hcut : ∀ n, 0 < Ccut n)
    (u : ℝ) (n : ℕ) :
    hughesYoungOneFactorDerivativeProfile Ccut u n ≤
      hughesYoungGaussianOneFactorProfile Ccut n * Real.exp (u ^ 2) := by
  unfold hughesYoungOneFactorDerivativeProfile
  calc
    ∑ q ∈ Finset.range (n + 1),
        (n.choose q : ℝ) * Ccut q *
          ((|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
            2 ^ (3 / 2 : ℝ)) ≤
      ∑ q ∈ Finset.range (n + 1),
        ((n.choose q : ℝ) * Ccut q *
          (((3 : ℝ) + ((n - q : ℕ) : ℝ)) ^ (n - q) *
            hughesYoungGaussianPowerConstant (n - q) *
            2 ^ (3 / 2 : ℝ))) * Real.exp (u ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      have hpoly := abs_add_pow_le_gaussian u
        (2 + ((n - q : ℕ) : ℝ)) (by positivity) (n - q)
      have hpoly' :
          (|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) ≤
            ((2 + ((n - q : ℕ) : ℝ)) + 1) ^ (n - q) *
              hughesYoungGaussianPowerConstant (n - q) * Real.exp (u ^ 2) := by
        simpa only [add_assoc] using hpoly
      have hcoeff : 0 ≤ (n.choose q : ℝ) * Ccut q :=
        mul_nonneg (by positivity) (hcut q).le
      calc
        (n.choose q : ℝ) * Ccut q *
            ((|u| + 2 + ((n - q : ℕ) : ℝ)) ^ (n - q) *
              2 ^ (3 / 2 : ℝ)) ≤
          (n.choose q : ℝ) * Ccut q *
            ((((2 + ((n - q : ℕ) : ℝ)) + 1) ^ (n - q) *
              hughesYoungGaussianPowerConstant (n - q) * Real.exp (u ^ 2)) *
              2 ^ (3 / 2 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right hpoly'
                (Real.rpow_nonneg (by norm_num) _)) hcoeff
        _ = ((n.choose q : ℝ) * Ccut q *
          (((3 : ℝ) + ((n - q : ℕ) : ℝ)) ^ (n - q) *
            hughesYoungGaussianPowerConstant (n - q) *
            2 ^ (3 / 2 : ℝ))) * Real.exp (u ^ 2) := by ring
    _ = hughesYoungGaussianOneFactorProfile Ccut n * Real.exp (u ^ 2) := by
      unfold hughesYoungGaussianOneFactorProfile
      rw [Finset.sum_mul]

/-- The corresponding fixed majorant for the complete `y`-factor. -/
noncomputable def hughesYoungGaussianCoreYProfile
    (Ccut : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ q ∈ Finset.range (j + 1),
    (j.choose q : ℝ) * hughesYoungGaussianOneFactorProfile Ccut q *
      hughesYoungShiftCompositionConstant (j - q)

theorem hughesYoungGaussianCoreYProfile_pos
    (Ccut : ℕ → ℝ) (hcut : ∀ n, 0 < Ccut n) (j : ℕ) :
    0 < hughesYoungGaussianCoreYProfile Ccut j := by
  unfold hughesYoungGaussianCoreYProfile
  apply Finset.sum_pos'
  · intro q hq
    exact mul_nonneg
      (mul_nonneg (by positivity)
        (hughesYoungGaussianOneFactorProfile_pos Ccut hcut q).le)
      (le_trans (by norm_num)
        (one_le_hughesYoungShiftCompositionConstant (j - q)))
  · refine ⟨j, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Nat.choose_self, Nat.sub_self]
    norm_num
    exact mul_pos (hughesYoungGaussianOneFactorProfile_pos Ccut hcut j)
      (lt_of_lt_of_le zero_lt_one
        (one_le_hughesYoungShiftCompositionConstant 0))

theorem hughesYoungCoreYDerivativeProfile_le_gaussian
    (Ccut : ℕ → ℝ) (hcut : ∀ n, 0 < Ccut n)
    (u : ℝ) (j : ℕ) :
    hughesYoungCoreYDerivativeProfile Ccut u j ≤
      hughesYoungGaussianCoreYProfile Ccut j * Real.exp (u ^ 2) := by
  unfold hughesYoungCoreYDerivativeProfile
  calc
    ∑ q ∈ Finset.range (j + 1),
        (j.choose q : ℝ) *
          hughesYoungOneFactorDerivativeProfile Ccut u q *
          hughesYoungShiftCompositionConstant (j - q) ≤
      ∑ q ∈ Finset.range (j + 1),
        ((j.choose q : ℝ) *
          hughesYoungGaussianOneFactorProfile Ccut q *
          hughesYoungShiftCompositionConstant (j - q)) *
            Real.exp (u ^ 2) := by
      apply Finset.sum_le_sum
      intro q hq
      have hone := hughesYoungOneFactorDerivativeProfile_le_gaussian
        Ccut hcut u q
      have hchoose : 0 ≤ (j.choose q : ℝ) := by positivity
      have hshift : 0 ≤ hughesYoungShiftCompositionConstant (j - q) :=
        le_trans (by norm_num)
          (one_le_hughesYoungShiftCompositionConstant (j - q))
      calc
        (j.choose q : ℝ) *
            hughesYoungOneFactorDerivativeProfile Ccut u q *
            hughesYoungShiftCompositionConstant (j - q) ≤
          (j.choose q : ℝ) *
            (hughesYoungGaussianOneFactorProfile Ccut q * Real.exp (u ^ 2)) *
            hughesYoungShiftCompositionConstant (j - q) := by gcongr
        _ = ((j.choose q : ℝ) *
            hughesYoungGaussianOneFactorProfile Ccut q *
            hughesYoungShiftCompositionConstant (j - q)) *
              Real.exp (u ^ 2) := by ring
    _ = hughesYoungGaussianCoreYProfile Ccut j * Real.exp (u ^ 2) := by
      unfold hughesYoungGaussianCoreYProfile
      rw [Finset.sum_mul]

theorem hughesYoungDFICore_equation2Profile
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (Z : ℝ), 0 < Z → ∀ z : ℝ,
      |z| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt Z) z‖ ≤ Ccut n)
    {T c u X Y P A : ℝ} {h k : ℕ} {r : ℤ}
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hh : 0 < h) (hhUpper : (h : ℝ) ≤ 2 * X)
    (hk : 0 < k) (hkUpper : (k : ℝ) ≤ 2 * Y)
    (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 < A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    DFIEquation2Profile (hughesYoungDFICore T c u X Y h k r) P X Y
      (hughesYoungDFICoreDerivativeProfile Ccut u A) := by
  refine ⟨fun i j => hughesYoungDFICoreDerivativeProfile_pos Ccut
    (fun n => (hcut n).1) u hA i j, ?_⟩
  intro i j x y hx hy
  by_cases hd : dfiMixedDeriv i j
      (hughesYoungDFICore T c u X Y h k r) x y = 0
  · rw [hd, norm_zero, mul_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (hughesYoungDFICoreDerivativeProfile_pos Ccut
            (fun n => (hcut n).1) u hA i j).le
          (inv_nonneg.mpr (le_of_lt
            (show 0 < 1 + x / X by positivity))))
        (inv_nonneg.mpr (le_of_lt
          (show 0 < 1 + y / Y by positivity))))
      (pow_nonneg (zero_le_one.trans hP) _)
  · have hsmooth := contDiff_uncurry_hughesYoungDFICore
      (lt_of_lt_of_le zero_lt_one hT) hc u
      (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) hh hk r (by linarith)
    have hmem : (x, y) ∈ Function.support
        (Function.uncurry (dfiMixedDeriv i j
          (hughesYoungDFICore T c u X Y h k r))) := by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hd
    have htsupport : tsupport (Function.uncurry
        (hughesYoungDFICore T c u X Y h k r)) ⊆
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
      closure_minimal
        (support_uncurry_hughesYoungDFICore_subset
          (lt_of_lt_of_le zero_lt_one hX)
          (lt_of_lt_of_le zero_lt_one hY) h k r)
        (isClosed_Icc.prod isClosed_Icc)
    have hxy := htsupport
      (support_dfiMixedDeriv_subset_tsupport hsmooth i j hmem)
    have hraw :=
      abs_pow_mul_abs_pow_mul_norm_dfiMixedDeriv_hughesYoungDFICore_le
        Ccut hcut i j hT hc hc1
        (lt_of_lt_of_le zero_lt_one hX) hxy.1.1
        (lt_of_lt_of_le zero_lt_one hY) hxy.2.1 hxy.2.2
        hh hhUpper hk hkUpper hr hP hTR hA.le hheight
    have hxDiv : x / X ≤ 2 :=
      (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hX)).2 hxy.1.2
    have hyDiv : y / Y ≤ 2 :=
      (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hY)).2 hxy.2.2
    have hxDenPos : 0 < 1 + x / X := by positivity
    have hyDenPos : 0 < 1 + y / Y := by positivity
    have hxInv : (3 : ℝ)⁻¹ ≤ (1 + x / X)⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le hxDenPos (by linarith : 1 + x / X ≤ 3)
    have hyInv : (3 : ℝ)⁻¹ ≤ (1 + y / Y)⁻¹ := by
      simpa only [one_div] using
        one_div_le_one_div_of_le hyDenPos (by linarith : 1 + y / Y ≤ 3)
    have hprofileNonneg :
        0 ≤ hughesYoungDFICoreDerivativeProfile Ccut u A i j :=
      (hughesYoungDFICoreDerivativeProfile_pos Ccut
        (fun n => (hcut n).1) u hA i j).le
    calc
      |x| ^ i * |y| ^ j *
          ‖dfiMixedDeriv i j
            (hughesYoungDFICore T c u X Y h k r) x y‖ ≤
          hughesYoungOneFactorDerivativeProfile Ccut u i *
            hughesYoungCoreYDerivativeProfile Ccut u j * A *
              P ^ (i + j) := hraw
      _ = hughesYoungDFICoreDerivativeProfile Ccut u A i j *
          (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ * P ^ (i + j) := by
        unfold hughesYoungDFICoreDerivativeProfile
        ring
      _ ≤ hughesYoungDFICoreDerivativeProfile Ccut u A i j *
          (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j) := by
        gcongr

theorem hughesYoungDFICore_equation2
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (Z : ℝ), 0 < Z → ∀ z : ℝ,
      |z| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt Z) z‖ ≤ Ccut n)
    {T c u X Y P A : ℝ} {h k : ℕ} {r : ℤ}
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hh : 0 < h) (hhUpper : (h : ℝ) ≤ 2 * X)
    (hk : 0 < k) (hkUpper : (k : ℝ) ≤ 2 * Y)
    (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 < A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    DFIEquation2 (hughesYoungDFICore T c u X Y h k r) P X Y := by
  have hprofile := hughesYoungDFICore_equation2Profile Ccut hcut
    hT hc hc1 hX hY hh hhUpper hk hkUpper hr hP hTR hA hheight
  refine
    { one_le_P := hP
      one_le_X := hX
      one_le_Y := hY
      smooth := contDiff_uncurry_hughesYoungDFICore
        (lt_of_lt_of_le zero_lt_one hT) hc u
        (lt_of_lt_of_le zero_lt_one hX)
        (lt_of_lt_of_le zero_lt_one hY) hh hk r (by linarith)
      compactSupport := HasCompactSupport.of_support_subset_isCompact
        (isCompact_Icc.prod isCompact_Icc)
        (support_uncurry_hughesYoungDFICore_subset
          (lt_of_lt_of_le zero_lt_one hX)
          (lt_of_lt_of_le zero_lt_one hY) h k r)
      support_pos := ?_
      derivativeBound := ?_ }
  · intro p hp
    have hxy := support_uncurry_hughesYoungDFICore_subset
      (lt_of_lt_of_le zero_lt_one hX)
      (lt_of_lt_of_le zero_lt_one hY) h k r hp
    exact ⟨(lt_of_lt_of_le zero_lt_one hX).trans_le hxy.1.1,
      (lt_of_lt_of_le zero_lt_one hY).trans_le hxy.2.1⟩
  · intro i j
    refine ⟨hughesYoungDFICoreDerivativeProfile Ccut u A i j,
      hprofile.positive i j, ?_⟩
    exact hprofile.bound i j

/-! ### A source-uniform normalized DFI family -/

/-- Gaussian normalization which absorbs both Mellin-factor derivative
profiles together with the explicit height-transform envelope. -/
noncomputable def hughesYoungDFINormalization (u A : ℝ) : ℝ :=
  A * Real.exp (2 * u ^ 2)

theorem hughesYoungDFINormalization_pos (u : ℝ) {A : ℝ} (hA : 0 < A) :
    0 < hughesYoungDFINormalization u A := by
  unfold hughesYoungDFINormalization
  positivity

/-- The fixed-shift DFI core after removal of its full explicit
Mellin/height envelope. -/
noncomputable def hughesYoungNormalizedDFICore
    (T c u X Y A : ℝ) (h k : ℕ) (r : ℤ) : ℝ → ℝ → ℂ :=
  dfiComplexScaleWeight
    (((hughesYoungDFINormalization u A : ℝ) : ℂ)⁻¹)
    (hughesYoungDFICore T c u X Y h k r)

theorem hughesYoungDFICore_eq_normalization_mul_normalized
    {u A : ℝ} (hA : 0 < A) (T c X Y : ℝ) (h k : ℕ) (r : ℤ) :
    hughesYoungDFICore T c u X Y h k r =
      dfiComplexScaleWeight ((hughesYoungDFINormalization u A : ℝ) : ℂ)
        (hughesYoungNormalizedDFICore T c u X Y A h k r) := by
  funext x y
  unfold hughesYoungNormalizedDFICore dfiComplexScaleWeight
  have hS := hughesYoungDFINormalization_pos u hA
  field_simp [hS.ne']

noncomputable def hughesYoungUniformDFIProfile
    (Ccut : ℕ → ℝ) (i j : ℕ) : ℝ :=
  9 * hughesYoungGaussianOneFactorProfile Ccut i *
    hughesYoungGaussianCoreYProfile Ccut j

theorem hughesYoungUniformDFIProfile_pos
    (Ccut : ℕ → ℝ) (hcut : ∀ n, 0 < Ccut n) (i j : ℕ) :
    0 < hughesYoungUniformDFIProfile Ccut i j := by
  unfold hughesYoungUniformDFIProfile
  exact mul_pos
    (mul_pos (by norm_num)
      (hughesYoungGaussianOneFactorProfile_pos Ccut hcut i))
    (hughesYoungGaussianCoreYProfile_pos Ccut hcut j)

theorem support_uncurry_hughesYoungNormalizedDFICore_subset
    {T c u X Y A : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (r : ℤ) :
    Function.support (Function.uncurry
      (hughesYoungNormalizedDFICore T c u X Y A h k r)) ⊆
        Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) := by
  intro p hp
  apply support_uncurry_hughesYoungDFICore_subset
    (T := T) (c := c) (u := u) hX hY h k r
  intro hz
  change hughesYoungDFICore T c u X Y h k r p.1 p.2 = 0 at hz
  apply hp
  unfold hughesYoungNormalizedDFICore dfiComplexScaleWeight Function.uncurry
  simp [hz]

theorem hughesYoungNormalizedDFICore_localizedBox
    {T c u X Y A : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (h k : ℕ) (r : ℤ) :
    DFILocalizedBox
      (hughesYoungNormalizedDFICore T c u X Y A h k r) X Y :=
  ⟨support_uncurry_hughesYoungNormalizedDFICore_subset hX hY h k r⟩

/-- After Gaussian normalization, the raw weighted mixed derivatives are
bounded by a profile independent of `T,c,u,X,Y,h,k,r`. -/
theorem abs_pow_mul_abs_pow_mul_norm_dfiMixedDeriv_hughesYoungNormalizedDFICore_le
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (Z : ℝ), 0 < Z → ∀ z : ℝ,
      |z| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt Z) z‖ ≤ Ccut n)
    {T c u X Y x y P A : ℝ} {h k : ℕ} {r : ℤ} (i j : ℕ)
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 0 < X) (hxLower : X ≤ x)
    (hY : 0 < Y) (hyLower : Y ≤ y) (hyUpper : y ≤ 2 * Y)
    (hh : 0 < h) (hhUpper : (h : ℝ) ≤ 2 * X)
    (hk : 0 < k) (hkUpper : (k : ℝ) ≤ 2 * Y)
    (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 < A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    |x| ^ i * |y| ^ j *
        ‖dfiMixedDeriv i j
          (hughesYoungNormalizedDFICore T c u X Y A h k r) x y‖ ≤
      hughesYoungGaussianOneFactorProfile Ccut i *
        hughesYoungGaussianCoreYProfile Ccut j * P ^ (i + j) := by
  let S : ℝ := hughesYoungDFINormalization u A
  have hS : 0 < S := hughesYoungDFINormalization_pos u hA
  have hrStrict : |(r : ℝ)| < Y := by linarith
  have hsmooth := contDiff_uncurry_hughesYoungDFICore
    (lt_of_lt_of_le zero_lt_one hT) hc u hX hY hh hk r hrStrict
  have hraw :=
    abs_pow_mul_abs_pow_mul_norm_dfiMixedDeriv_hughesYoungDFICore_le
      Ccut hcut i j hT hc hc1 hX hxLower hY hyLower hyUpper
      hh hhUpper hk hkUpper hr hP hTR hA.le hheight
  have hxGauss := hughesYoungOneFactorDerivativeProfile_le_gaussian
    Ccut (fun n => (hcut n).1) u i
  have hyGauss := hughesYoungCoreYDerivativeProfile_le_gaussian
    Ccut (fun n => (hcut n).1) u j
  have hprofiles :
      hughesYoungOneFactorDerivativeProfile Ccut u i *
          hughesYoungCoreYDerivativeProfile Ccut u j ≤
        hughesYoungGaussianOneFactorProfile Ccut i *
          hughesYoungGaussianCoreYProfile Ccut j * Real.exp (2 * u ^ 2) := by
    calc
      hughesYoungOneFactorDerivativeProfile Ccut u i *
          hughesYoungCoreYDerivativeProfile Ccut u j ≤
        (hughesYoungGaussianOneFactorProfile Ccut i * Real.exp (u ^ 2)) *
          (hughesYoungGaussianCoreYProfile Ccut j * Real.exp (u ^ 2)) := by
            exact mul_le_mul hxGauss hyGauss
              (hughesYoungCoreYDerivativeProfile_pos Ccut
                (fun n => (hcut n).1) u j).le
              (mul_nonneg
                (hughesYoungGaussianOneFactorProfile_pos Ccut
                  (fun n => (hcut n).1) i).le
                (Real.exp_pos _).le)
      _ = hughesYoungGaussianOneFactorProfile Ccut i *
          hughesYoungGaussianCoreYProfile Ccut j * Real.exp (2 * u ^ 2) := by
            rw [show 2 * u ^ 2 = u ^ 2 + u ^ 2 by ring, Real.exp_add]
            ring
  change |x| ^ i * |y| ^ j *
      ‖dfiMixedDeriv i j
        (dfiComplexScaleWeight (((S : ℝ) : ℂ)⁻¹)
          (hughesYoungDFICore T c u X Y h k r)) x y‖ ≤ _
  rw [dfiMixedDeriv_scale hsmooth, norm_mul]
  have hnormS : ‖((S : ℂ)⁻¹)‖ = S⁻¹ := by
    rw [norm_inv, norm_real, Real.norm_eq_abs, abs_of_pos hS]
  rw [hnormS]
  calc
    |x| ^ i * |y| ^ j *
        (S⁻¹ * ‖dfiMixedDeriv i j
          (hughesYoungDFICore T c u X Y h k r) x y‖) =
      S⁻¹ * (|x| ^ i * |y| ^ j *
        ‖dfiMixedDeriv i j
          (hughesYoungDFICore T c u X Y h k r) x y‖) := by ring
    _ ≤ S⁻¹ *
        (hughesYoungOneFactorDerivativeProfile Ccut u i *
          hughesYoungCoreYDerivativeProfile Ccut u j * A * P ^ (i + j)) := by
      exact mul_le_mul_of_nonneg_left hraw (inv_nonneg.mpr hS.le)
    _ ≤ S⁻¹ *
        ((hughesYoungGaussianOneFactorProfile Ccut i *
          hughesYoungGaussianCoreYProfile Ccut j * Real.exp (2 * u ^ 2)) *
            A * P ^ (i + j)) := by
      gcongr
    _ = hughesYoungGaussianOneFactorProfile Ccut i *
        hughesYoungGaussianCoreYProfile Ccut j * P ^ (i + j) := by
      dsimp only [S, hughesYoungDFINormalization]
      field_simp [hA.ne', (Real.exp_pos (2 * u ^ 2)).ne']

theorem hughesYoungNormalizedDFICore_equation2
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (Z : ℝ), 0 < Z → ∀ z : ℝ,
      |z| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt Z) z‖ ≤ Ccut n)
    {T c u X Y P A : ℝ} {h k : ℕ} {r : ℤ}
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hh : 0 < h) (hhUpper : (h : ℝ) ≤ 2 * X)
    (hk : 0 < k) (hkUpper : (k : ℝ) ≤ 2 * Y)
    (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 < A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    DFIEquation2
      (hughesYoungNormalizedDFICore T c u X Y A h k r) P X Y := by
  exact (hughesYoungDFICore_equation2 Ccut hcut hT hc hc1 hX hY
    hh hhUpper hk hkUpper hr hP hTR hA hheight).scale
      (((hughesYoungDFINormalization u A : ℝ) : ℂ)⁻¹)

theorem hughesYoungNormalizedDFICore_equation2Profile
    (Ccut : ℕ → ℝ)
    (hcut : ∀ n : ℕ, 0 < Ccut n ∧ ∀ (Z : ℝ), 0 < Z → ∀ z : ℝ,
      |z| ^ n * ‖iteratedDeriv n (hughesYoungDyadicCutoffAt Z) z‖ ≤ Ccut n)
    {T c u X Y P A : ℝ} {h k : ℕ} {r : ℤ}
    (hT : 1 ≤ T) (hc : 0 < c) (hc1 : c ≤ 1)
    (hX : 1 ≤ X) (hY : 1 ≤ Y)
    (hh : 0 < h) (hhUpper : (h : ℝ) ≤ 2 * X)
    (hk : 0 < k) (hkUpper : (k : ℝ) ≤ 2 * Y)
    (hr : |(r : ℝ)| ≤ Y / 2) (hP : 1 ≤ P)
    (hTR : T * (|(r : ℝ)| / Y) ≤ P) (hA : 0 < A)
    (hheight : ∀ (n : ℕ) (xi : ℝ),
      ‖(1 / (T : ℂ)) *
          iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
        (15 / 4 : ℝ) * ((4 * T) ^ n * A)) :
    DFIEquation2Profile
      (hughesYoungNormalizedDFICore T c u X Y A h k r) P X Y
      (hughesYoungUniformDFIProfile Ccut) := by
  refine ⟨fun i j => hughesYoungUniformDFIProfile_pos Ccut
    (fun n => (hcut n).1) i j, ?_⟩
  intro i j x y hx hy
  by_cases hd : dfiMixedDeriv i j
      (hughesYoungNormalizedDFICore T c u X Y A h k r) x y = 0
  · rw [hd, norm_zero, mul_zero]
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (hughesYoungUniformDFIProfile_pos Ccut
            (fun n => (hcut n).1) i j).le
          (inv_nonneg.mpr (le_of_lt
            (show 0 < 1 + x / X by positivity))))
        (inv_nonneg.mpr (le_of_lt
          (show 0 < 1 + y / Y by positivity))))
      (pow_nonneg (zero_le_one.trans hP) _)
  · have heq2 := hughesYoungNormalizedDFICore_equation2 Ccut hcut
      hT hc hc1 hX hY hh hhUpper hk hkUpper hr hP hTR hA hheight
    have hmem : (x, y) ∈ Function.support
        (Function.uncurry (dfiMixedDeriv i j
          (hughesYoungNormalizedDFICore T c u X Y A h k r))) := by
      simpa only [Function.mem_support, Function.uncurry_apply_pair] using hd
    have htsupport : tsupport (Function.uncurry
        (hughesYoungNormalizedDFICore T c u X Y A h k r)) ⊆
          Set.Icc X (2 * X) ×ˢ Set.Icc Y (2 * Y) :=
      closure_minimal
        (support_uncurry_hughesYoungNormalizedDFICore_subset
          (lt_of_lt_of_le zero_lt_one hX)
          (lt_of_lt_of_le zero_lt_one hY) h k r)
        (isClosed_Icc.prod isClosed_Icc)
    have hxy := htsupport
      (support_dfiMixedDeriv_subset_tsupport heq2.smooth i j hmem)
    have hraw :=
      abs_pow_mul_abs_pow_mul_norm_dfiMixedDeriv_hughesYoungNormalizedDFICore_le
        Ccut hcut i j hT hc hc1
        (lt_of_lt_of_le zero_lt_one hX) hxy.1.1
        (lt_of_lt_of_le zero_lt_one hY) hxy.2.1 hxy.2.2
        hh hhUpper hk hkUpper hr hP hTR hA hheight
    have hxDenPos : 0 < 1 + x / X := by positivity
    have hyDenPos : 0 < 1 + y / Y := by positivity
    have hxInv : (3 : ℝ)⁻¹ ≤ (1 + x / X)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hxDenPos
        (by
          have := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hX)).2 hxy.1.2
          linarith : 1 + x / X ≤ 3)
    have hyInv : (3 : ℝ)⁻¹ ≤ (1 + y / Y)⁻¹ := by
      simpa only [one_div] using one_div_le_one_div_of_le hyDenPos
        (by
          have := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hY)).2 hxy.2.2
          linarith : 1 + y / Y ≤ 3)
    have hprofileNonneg :
        0 ≤ hughesYoungUniformDFIProfile Ccut i j :=
      (hughesYoungUniformDFIProfile_pos Ccut
        (fun n => (hcut n).1) i j).le
    calc
      |x| ^ i * |y| ^ j *
          ‖dfiMixedDeriv i j
            (hughesYoungNormalizedDFICore T c u X Y A h k r) x y‖ ≤
        hughesYoungGaussianOneFactorProfile Ccut i *
          hughesYoungGaussianCoreYProfile Ccut j * P ^ (i + j) := hraw
      _ = hughesYoungUniformDFIProfile Ccut i j *
          (3 : ℝ)⁻¹ * (3 : ℝ)⁻¹ * P ^ (i + j) := by
        unfold hughesYoungUniformDFIProfile
        ring
      _ ≤ hughesYoungUniformDFIProfile Ccut i j *
          (1 + x / X)⁻¹ * (1 + y / Y)⁻¹ * P ^ (i + j) := by
        gcongr

/-! ## Uniform application of the signed DFI theorem

The normalization above is useful only if the constant supplied by DFI is
chosen before the Hughes--Young height, Mellin ordinate, dyadic box, and
shift.  This theorem makes that quantifier order explicit. -/

/-- A single DFI error constant works for the entire normalized
Hughes--Young source family.  In particular, `C` is independent of `u`, so
this estimate may subsequently be integrated on the Hughes--Young Mellin
contour. -/
theorem exists_uniform_norm_hughesYoungNormalizedDFICore_dfiError
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U Q : ℝ} {h k : ℕ} {r : ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      |(r : ℝ)| ≤ Y / 2 → 1 ≤ P →
      T * (|(r : ℝ)| / Y) ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b M N : ℕ), 0 < a → 0 < b → r ≠ 0 → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y →
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) →
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y) →
      ‖dfiDyadicShiftedDivisorSum
          (hughesYoungNormalizedDFICore T c u X Y A h k r)
          a b M N r -
        dfiSignedCentralSeries a b r
          (hughesYoungNormalizedDFICore T c u X Y A h k r)‖ ≤
        C * dfiTheorem1ErrorScale P X Y ε := by
  obtain ⟨Ccut, hCcut⟩ :=
    exists_uniform_hughesYoungDyadicCutoffAt_derivativeProfile
  obtain ⟨Cφ, hCφ⟩ := exists_dfiUniformRedundantCutoff_profile
  obtain ⟨Cw, hCw⟩ := exists_dfiUniformDeltaWeight_profile
  obtain ⟨E, hE⟩ := exists_dfiUniformDeltaWeight_quotient_profile
  obtain ⟨C, hC, hBound⟩ :=
    exists_uniform_norm_dfiDyadicShiftedDivisorSum_sub_signedCentralSeries_le_theorem1ErrorScale
      Cw E (hughesYoungUniformDFIProfile Ccut)
        (fun i j => hughesYoungUniformDFIProfile Ccut j i)
        Cφ Cw ε hε0 hε4
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U Q h k r hT hc hc1 hX hY hh hhX hk hkY
    hr hP hTR hA hheight hscale hQ hU hQsq a b M N ha hb hr0 hab
    hM hN haX hbY hrPos hrNeg
  have hf := hughesYoungNormalizedDFICore_equation2 Ccut hCcut
    hT hc hc1 hX hY hh hhX hk hkY hr hP hTR hA hheight
  have hfC := hughesYoungNormalizedDFICore_equation2Profile Ccut hCcut
    hT hc hc1 hX hY hh hhX hk hkY hr hP hTR hA hheight
  have hbox := hughesYoungNormalizedDFICore_localizedBox
    (T := T) (c := c) (u := u) (A := A) (X := X) (Y := Y)
    (lt_of_lt_of_le zero_lt_one hX)
    (lt_of_lt_of_le zero_lt_one hY) h k r
  have hU0 : 0 < U := by rw [hU]; positivity
  let φ : ℝ → ℂ := dfiUniformRedundantCutoff U
  let hφ : DFIRedundantCutoff φ U := dfiUniformRedundantCutoff_spec U hU0
  let w : DFIDeltaWeight Q := dfiUniformDeltaWeight Q hQ
  exact hBound hf hfC hbox hf.swap (hfC.swap hf) hbox.swap hφ
    (hCφ U hU0) hscale (hCw Q hQ) (hCw Q hQ) (hE Q hQ)
    (by linarith) hU hQsq a b M N r ha hb hr0 hab hM hN haX hbY
    hrPos hrNeg

/-- DFI's signed error estimate restored to the literal cleaned
Hughes--Young equation-(70) weight.  The only parameter-dependent factor is
the explicit scalar and Gaussian normalization already present in that
source weight; the existential constant remains universal. -/
theorem exists_uniform_norm_hughesYoungCleanedShiftWeight_dfiError
    (ε : ℝ) (hε0 : 0 < ε) (hε4 : ε < 4) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {T c u X Y P A U Q : ℝ} {h k : ℕ} {r : ℤ},
      1 ≤ T → 0 < c → c ≤ 1 →
      1 ≤ X → 1 ≤ Y →
      0 < h → (h : ℝ) ≤ 2 * X →
      0 < k → (k : ℝ) ≤ 2 * Y →
      |(r : ℝ)| ≤ Y / 2 → 1 ≤ P →
      T * (|(r : ℝ)| / Y) ≤ P → 0 < A →
      (∀ (n : ℕ) (xi : ℝ),
        ‖(1 / (T : ℂ)) *
            iteratedDeriv n (hughesYoungHeightTransform T c u) xi‖ ≤
          (15 / 4 : ℝ) * ((4 * T) ^ n * A)) →
      U ≤ P⁻¹ * min X Y → 8 ≤ Q → U = Q ^ 2 →
      Q ^ 2 = P⁻¹ * (X + Y)⁻¹ * (X * Y) →
      ∀ (a b M N : ℕ), 0 < a → 0 < b → r ≠ 0 → a.Coprime b →
      2 * X / a ≤ M → 2 * Y / b ≤ N →
      (a : ℝ) ≤ 2 * X → (b : ℝ) ≤ 2 * Y →
      (0 ≤ r → (r.natAbs : ℝ) ≤ 2 * X) →
      (r < 0 → (r.natAbs : ℝ) ≤ 2 * Y) →
      ‖dfiDyadicShiftedDivisorSum
          (hughesYoungCleanedShiftWeight T c u X Y h k r)
          a b M N r -
        dfiSignedCentralSeries a b r
          (hughesYoungCleanedShiftWeight T c u X Y h k r)‖ ≤
        ‖hughesYoungLocalizedStaticScalar T h k‖ *
          hughesYoungDFINormalization u A *
          (C * dfiTheorem1ErrorScale P X Y ε) := by
  obtain ⟨C, hC, hBound⟩ :=
    exists_uniform_norm_hughesYoungNormalizedDFICore_dfiError ε hε0 hε4
  refine ⟨C, hC, ?_⟩
  intro T c u X Y P A U Q h k r hT hc hc1 hX hY hh hhX hk hkY
    hr hP hTR hA hheight hscale hQ hU hQsq a b M N ha hb hr0 hab
    hM hN haX hbY hrPos hrNeg
  let S : ℝ := hughesYoungDFINormalization u A
  let z : ℂ := hughesYoungLocalizedStaticScalar T h k * (S : ℂ)
  have hS : 0 < S := hughesYoungDFINormalization_pos u hA
  have hnormalized := hBound hT hc hc1 hX hY hh hhX hk hkY hr hP
    hTR hA hheight hscale hQ hU hQsq a b M N ha hb hr0 hab hM hN
    haX hbY hrPos hrNeg
  have hweight :
      hughesYoungCleanedShiftWeight T c u X Y h k r =
        dfiComplexScaleWeight z
          (hughesYoungNormalizedDFICore T c u X Y A h k r) := by
    funext x y
    rw [hughesYoungCleanedShiftWeight_eq_staticScalar_mul_dfiCore]
    rw [hughesYoungDFICore_eq_normalization_mul_normalized
      hA T c X Y h k r]
    unfold dfiComplexScaleWeight
    dsimp only [z, S]
    ring
  rw [hweight]
  have hscaled := norm_dfiSignedDiscrepancy_scale_le z
    (hughesYoungNormalizedDFICore T c u X Y A h k r)
    a b M N r hnormalized
  have hnormz : ‖z‖ =
      ‖hughesYoungLocalizedStaticScalar T h k‖ * S := by
    dsimp only [z]
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hS]
  rw [hnormz] at hscaled
  exact hscaled

/-! ## A quantitative right contour

For the upper-bound consumer we may keep the absolutely convergent contour
at `Re w = 2`.  At that integral displacement Deligne's Gamma recurrence is
exact, so the otherwise delicate horizontal Gamma comparison is reduced to
the already proved critical-line symmetric pair estimate and elementary
quadratic factors.
-/

/-- The paired Gamma quotient on the right contour `Re w = 2`. -/
noncomputable def hughesYoungGammaRatioTwo (t u : ℝ) : ℂ :=
  let w : ℂ := (2 : ℂ) + (u : ℂ) * I
  let s₁ := afeCriticalPoint t + w
  let s₂ := afeCriticalPoint (-t) + w
  Complex.Gammaℝ s₁ ^ 2 * Complex.Gammaℝ s₂ ^ 2 /
    afeGammaNormalization t

theorem hughesYoungGammaRatioTwo_eq (t u : ℝ) :
    hughesYoungGammaRatioTwo t u =
      hughesYoungGammaRatio t u *
        ((afeCriticalPoint t + (u : ℂ) * I) ^ 2 *
          (afeCriticalPoint (-t) + (u : ℂ) * I) ^ 2) /
        (16 * (Real.pi : ℂ) ^ 4) := by
  let s₁ : ℂ := afeCriticalPoint t + (u : ℂ) * I
  let s₂ : ℂ := afeCriticalPoint (-t) + (u : ℂ) * I
  have hs₁ : s₁ ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s₁, afeCriticalPoint] at hre
  have hs₂ : s₂ ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [s₂, afeCriticalPoint] at hre
  have harg₁ : afeCriticalPoint t + ((2 : ℂ) + (u : ℂ) * I) = s₁ + 2 := by
    simp only [s₁]
    ring
  have harg₂ : afeCriticalPoint (-t) + ((2 : ℂ) + (u : ℂ) * I) = s₂ + 2 := by
    simp only [s₂]
    ring
  rw [hughesYoungGammaRatioTwo, hughesYoungGammaRatio]
  rw [harg₁, harg₂, Complex.Gammaℝ_add_two hs₁,
    Complex.Gammaℝ_add_two hs₂]
  field_simp [Real.pi_ne_zero, afeGammaNormalization_ne_zero]
  ring

/-- The exact Gamma recurrence gives a polynomial-height bound for the
`Re w = 2` paired quotient. -/
theorem norm_hughesYoungGammaRatioTwo_le (t u : ℝ) :
    ‖hughesYoungGammaRatioTwo t u‖ ≤
      Real.exp (16 * u ^ 2) *
        ((25 + 8 * u ^ 2) * ((1 / 4 : ℝ) + t ^ 2)) ^ 2 := by
  let A : ℝ := (1 / 4 : ℝ) + t ^ 2
  let Ap : ℝ := (1 / 4 : ℝ) + (t + u) ^ 2
  let Am : ℝ := (1 / 4 : ℝ) + (-t + u) ^ 2
  let B : ℝ := 25 + 8 * u ^ 2
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hAp : Ap ≤ B * A := by
    dsimp [Ap, B, A]
    nlinarith [sq_nonneg t, sq_nonneg u, sq_nonneg (t - u)]
  have hAm : Am ≤ B * A := by
    dsimp [Am, B, A]
    nlinarith [sq_nonneg t, sq_nonneg u, sq_nonneg (t + u)]
  have hAp0 : 0 ≤ Ap := by dsimp [Ap]; positivity
  have hAm0 : 0 ≤ Am := by dsimp [Am]; positivity
  have hprod : Ap * Am ≤ (B * A) ^ 2 := by
    calc
      Ap * Am ≤ (B * A) * Am := mul_le_mul_of_nonneg_right hAp hAm0
      _ ≤ (B * A) * (B * A) :=
        mul_le_mul_of_nonneg_left hAm (mul_nonneg hB hA.le)
      _ = (B * A) ^ 2 := by ring
  rw [hughesYoungGammaRatioTwo_eq, norm_div, norm_mul, norm_mul,
    norm_pow, norm_pow, norm_mul, norm_pow]
  have hs₁ : ‖afeCriticalPoint t + (u : ℂ) * I‖ ^ 2 = Ap := by
    rw [Complex.sq_norm]
    simp [afeCriticalPoint, Ap, Complex.normSq]
    ring
  have hs₂ : ‖afeCriticalPoint (-t) + (u : ℂ) * I‖ ^ 2 = Am := by
    rw [Complex.sq_norm]
    simp [afeCriticalPoint, Am, Complex.normSq]
    ring
  rw [hs₁, hs₂]
  have hden : 1 ≤ ‖(16 : ℂ)‖ * ‖(Real.pi : ℂ)‖ ^ 4 := by
    rw [Complex.norm_ofNat, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
    have hpi : 3 ≤ Real.pi := Real.pi_gt_three.le
    nlinarith [sq_nonneg (Real.pi ^ 2 - 1)]
  have hfrac : Ap * Am / (‖(16 : ℂ)‖ * ‖(Real.pi : ℂ)‖ ^ 4) ≤
      (B * A) ^ 2 := by
    calc
      Ap * Am / (‖(16 : ℂ)‖ * ‖(Real.pi : ℂ)‖ ^ 4) ≤ Ap * Am := by
        exact div_le_self (mul_nonneg hAp0 hAm0) hden
      _ ≤ (B * A) ^ 2 := hprod
  calc
    ‖hughesYoungGammaRatio t u‖ * (Ap * Am) /
          (‖(16 : ℂ)‖ * ‖(Real.pi : ℂ)‖ ^ 4)
        = ‖hughesYoungGammaRatio t u‖ *
            (Ap * Am / (‖(16 : ℂ)‖ * ‖(Real.pi : ℂ)‖ ^ 4)) := by ring
    _ ≤ Real.exp (16 * u ^ 2) *
          (Ap * Am / (‖(16 : ℂ)‖ * ‖(Real.pi : ℂ)‖ ^ 4)) := by
      exact mul_le_mul_of_nonneg_right (norm_hughesYoungGammaRatio_le t u) (by positivity)
    _ ≤ Real.exp (16 * u ^ 2) * ((B * A) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hfrac (Real.exp_nonneg _)
    _ = Real.exp (16 * u ^ 2) *
        ((25 + 8 * u ^ 2) * ((1 / 4 : ℝ) + t ^ 2)) ^ 2 := by rfl

/-- The pole-canceling polynomial quotient on the absolutely convergent
right line `Re w = 2`. -/
noncomputable def hughesYoungPolynomialRatioTwo (t u : ℝ) : ℂ :=
  let w : ℂ := 2 + (u : ℂ) * I
  let s₁ := afeCriticalPoint t + w
  let s₂ := afeCriticalPoint (-t) + w
  (s₁ * (1 - s₁)) ^ 2 * (s₂ * (1 - s₂)) ^ 2 /
    afePoleNormalization t

/-- The shifted polynomial quotient has uniform polynomial growth in the
Mellin ordinate and no height loss. -/
theorem norm_hughesYoungPolynomialRatioTwo_le (t u : ℝ) :
    ‖hughesYoungPolynomialRatioTwo t u‖ ≤ (25 + 8 * u ^ 2) ^ 4 := by
  let A : ℝ := (1 / 4 : ℝ) + t ^ 2
  let B : ℝ := 25 + 8 * u ^ 2
  let Pp : ℝ := ((25 / 4 : ℝ) + (t + u) ^ 2) *
    ((9 / 4 : ℝ) + (t + u) ^ 2)
  let Pm : ℝ := ((25 / 4 : ℝ) + (-t + u) ^ 2) *
    ((9 / 4 : ℝ) + (-t + u) ^ 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hppUpper : (25 / 4 : ℝ) + (t + u) ^ 2 ≤ B * A := by
    dsimp [B, A]
    nlinarith [sq_nonneg t, sq_nonneg u, sq_nonneg (t - u)]
  have hpmUpper : (25 / 4 : ℝ) + (-t + u) ^ 2 ≤ B * A := by
    dsimp [B, A]
    nlinarith [sq_nonneg t, sq_nonneg u, sq_nonneg (t + u)]
  have hppSmall : (9 / 4 : ℝ) + (t + u) ^ 2 ≤ B * A := by
    linarith
  have hpmSmall : (9 / 4 : ℝ) + (-t + u) ^ 2 ≤ B * A := by
    linarith
  have hPp0 : 0 ≤ Pp := by dsimp [Pp]; positivity
  have hPm0 : 0 ≤ Pm := by dsimp [Pm]; positivity
  have hPp : Pp ≤ (B * A) ^ 2 := by
    dsimp only [Pp]
    calc
      ((25 / 4 : ℝ) + (t + u) ^ 2) * ((9 / 4 : ℝ) + (t + u) ^ 2)
          ≤ (B * A) * ((9 / 4 : ℝ) + (t + u) ^ 2) :=
        mul_le_mul_of_nonneg_right hppUpper (by positivity)
      _ ≤ (B * A) * (B * A) :=
        mul_le_mul_of_nonneg_left hppSmall (mul_nonneg hB hA.le)
      _ = (B * A) ^ 2 := by ring
  have hPm : Pm ≤ (B * A) ^ 2 := by
    dsimp only [Pm]
    calc
      ((25 / 4 : ℝ) + (-t + u) ^ 2) * ((9 / 4 : ℝ) + (-t + u) ^ 2)
          ≤ (B * A) * ((9 / 4 : ℝ) + (-t + u) ^ 2) :=
        mul_le_mul_of_nonneg_right hpmUpper (by positivity)
      _ ≤ (B * A) * (B * A) :=
        mul_le_mul_of_nonneg_left hpmSmall (mul_nonneg hB hA.le)
      _ = (B * A) ^ 2 := by ring
  let s₁ : ℂ := afeCriticalPoint t + (2 : ℂ) + (u : ℂ) * I
  let s₂ : ℂ := afeCriticalPoint (-t) + (2 : ℂ) + (u : ℂ) * I
  have hs₁ : ‖s₁‖ ^ 2 = (25 / 4 : ℝ) + (t + u) ^ 2 := by
    rw [Complex.sq_norm]
    simp [s₁, afeCriticalPoint, Complex.normSq]
    ring
  have hs₁' : ‖1 - s₁‖ ^ 2 = (9 / 4 : ℝ) + (t + u) ^ 2 := by
    rw [Complex.sq_norm]
    simp [s₁, afeCriticalPoint, Complex.normSq]
    ring
  have hs₂ : ‖s₂‖ ^ 2 = (25 / 4 : ℝ) + (-t + u) ^ 2 := by
    rw [Complex.sq_norm]
    simp [s₂, afeCriticalPoint, Complex.normSq]
    ring
  have hs₂' : ‖1 - s₂‖ ^ 2 = (9 / 4 : ℝ) + (-t + u) ^ 2 := by
    rw [Complex.sq_norm]
    simp [s₂, afeCriticalPoint, Complex.normSq]
    ring
  have hnum₁ : ‖(s₁ * (1 - s₁)) ^ 2‖ = Pp := by
    rw [norm_pow, norm_mul, mul_pow, hs₁, hs₁']
  have hnum₂ : ‖(s₂ * (1 - s₂)) ^ 2‖ = Pm := by
    rw [norm_pow, norm_mul, mul_pow, hs₂, hs₂']
  have hden : ‖afePoleNormalization t‖ = A ^ 4 := by
    unfold afePoleNormalization
    have hcritical (v : ℝ) :
        ‖(1 / 2 : ℂ) + (v : ℂ) * I‖ *
            ‖1 - ((1 / 2 : ℂ) + (v : ℂ) * I)‖ =
          (1 / 4 : ℝ) + v ^ 2 := by
      have h₁ : ‖(1 / 2 : ℂ) + (v : ℂ) * I‖ =
          Real.sqrt ((1 / 4 : ℝ) + v ^ 2) := by
        rw [Complex.norm_def]
        congr 1
        simp [Complex.normSq, sq]
        ring
      have h₂ : ‖1 - ((1 / 2 : ℂ) + (v : ℂ) * I)‖ =
          Real.sqrt ((1 / 4 : ℝ) + v ^ 2) := by
        rw [Complex.norm_def]
        congr 1
        simp [Complex.normSq, sq]
        ring
      rw [h₁, h₂, ← sq]
      exact Real.sq_sqrt (by positivity)
    have hcrit : ‖afeCriticalPoint t * (1 - afeCriticalPoint t)‖ = A := by
      rw [norm_mul]
      simpa only [afeCriticalPoint, A] using hcritical t
    have hcritNeg : ‖afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))‖ = A := by
      rw [norm_mul]
      have h := hcritical (-t)
      simpa only [afeCriticalPoint, A, neg_sq] using h
    rw [norm_pow, show afeCriticalPoint t * (1 - afeCriticalPoint t) *
        afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t)) =
      (afeCriticalPoint t * (1 - afeCriticalPoint t)) *
        (afeCriticalPoint (-t) * (1 - afeCriticalPoint (-t))) by ring,
      norm_mul, hcrit, hcritNeg]
    ring
  have hprod : Pp * Pm ≤ (B * A) ^ 4 := by
    calc
      Pp * Pm ≤ (B * A) ^ 2 * Pm := mul_le_mul_of_nonneg_right hPp hPm0
      _ ≤ (B * A) ^ 2 * (B * A) ^ 2 :=
        mul_le_mul_of_nonneg_left hPm (sq_nonneg (B * A))
      _ = (B * A) ^ 4 := by ring
  have hratio : Pp * Pm / A ^ 4 ≤ B ^ 4 := by
    rw [div_le_iff₀ (pow_pos hA 4)]
    calc
      Pp * Pm ≤ (B * A) ^ 4 := hprod
      _ = B ^ 4 * A ^ 4 := by ring
  unfold hughesYoungPolynomialRatioTwo
  dsimp only
  rw [show afeCriticalPoint t + ((2 : ℂ) + (u : ℂ) * I) = s₁ by
        simp only [s₁]; ring,
      show afeCriticalPoint (-t) + ((2 : ℂ) + (u : ℂ) * I) = s₂ by
        simp only [s₂]; ring]
  rw [norm_div, norm_mul, hnum₁, hnum₂, hden]
  exact hratio

/-- Exact factorization of the Hughes--Young right-contour kernel on
`Re w = 2` into its Gaussian, polynomial, and paired-Gamma quotients. -/
theorem hughesYoungRightContourWeight_two_eq (t u : ℝ) :
    hughesYoungRightContourWeight t 2 u =
      (Complex.exp (100 * (((2 : ℂ) + (u : ℂ) * I) ^ 2)) *
        hughesYoungAuxiliaryZero ((2 : ℂ) + (u : ℂ) * I)) *
        hughesYoungPolynomialRatioTwo t u *
        hughesYoungGammaRatioTwo t u /
        ((2 : ℂ) + (u : ℂ) * I) := by
  let w : ℂ := (2 : ℂ) + (u : ℂ) * I
  let s₁ : ℂ := afeCriticalPoint t + w
  let s₂ : ℂ := afeCriticalPoint (-t) + w
  have hw : w ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [w] at hre
  have hfactor (E p₁ p₂ g₁ g₂ PN GN W : ℂ)
      (hPN : PN ≠ 0) (hGN : GN ≠ 0) (hW : W ≠ 0) :
      E * p₁ * p₂ * g₁ * g₂ / PN / W / GN =
        E * ((p₁ * p₂) / PN) * ((g₁ * g₂) / GN) / W := by
    field_simp [hPN, hGN, hW]
  simpa only [hughesYoungRightContourWeight, hughesYoungPolynomialRatioTwo,
      hughesYoungGammaRatioTwo, w, s₁, s₂] using
    hfactor (Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w)
      ((s₁ * (1 - s₁)) ^ 2) ((s₂ * (1 - s₂)) ^ 2)
      (Complex.Gammaℝ s₁ ^ 2) (Complex.Gammaℝ s₂ ^ 2)
      (afePoleNormalization t) (afeGammaNormalization t) w
      (afePoleNormalization_ne_zero t) (afeGammaNormalization_ne_zero t) hw

/-- Explicit Gaussian majorant for the complete right-contour kernel.  The
only remaining height factor is the expected fourth-degree archimedean cost,
which is canceled by the two physical powers supplied by the opened divisor
series. -/
theorem norm_hughesYoungRightContourWeight_two_le (t u : ℝ) :
    ‖hughesYoungRightContourWeight t 2 u‖ ≤
      Real.exp (400 - 84 * u ^ 2) *
        (25 + 8 * u ^ 2) ^ 10 * ((1 / 4 : ℝ) + t ^ 2) ^ 2 := by
  let w : ℂ := (2 : ℂ) + (u : ℂ) * I
  let A : ℝ := (1 / 4 : ℝ) + t ^ 2
  let B : ℝ := 25 + 8 * u ^ 2
  have hwNorm : 1 ≤ ‖w‖ := by
    have hre := Complex.abs_re_le_norm w
    calc
      1 ≤ 2 := by norm_num
      _ ≤ ‖w‖ := by simpa [w] using hre
  have hexp : ‖Complex.exp (100 * w ^ 2)‖ =
      Real.exp (400 - 100 * u ^ 2) := by
    rw [Complex.norm_exp]
    congr 1
    simp [w, pow_two, Complex.mul_re]
    ring
  have hwSq : ‖w‖ ^ 2 = 4 + u ^ 2 := by
    rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg w)]
    simp [w, Complex.normSq]
    ring
  have haux : ‖hughesYoungAuxiliaryZero w‖ ≤ B ^ 4 := by
    unfold hughesYoungAuxiliaryZero
    rw [norm_pow]
    have hbase : ‖1 - 4 * w ^ 2‖ ≤ B := by
      calc
        ‖1 - 4 * w ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖4 * w ^ 2‖ := norm_sub_le _ _
        _ = 1 + 4 * ‖w‖ ^ 2 := by simp [norm_pow]
        _ = 1 + 4 * (4 + u ^ 2) := by rw [hwSq]
        _ ≤ B := by dsimp only [B]; nlinarith [sq_nonneg u]
    gcongr
  have hpoly : ‖hughesYoungPolynomialRatioTwo t u‖ ≤ B ^ 4 := by
    simpa only [B] using norm_hughesYoungPolynomialRatioTwo_le t u
  have hgamma : ‖hughesYoungGammaRatioTwo t u‖ ≤
      Real.exp (16 * u ^ 2) * (B * A) ^ 2 := by
    simpa only [B, A] using norm_hughesYoungGammaRatioTwo_le t u
  have hnum :
      ‖Complex.exp (100 * w ^ 2)‖ *
          ‖hughesYoungAuxiliaryZero w‖ *
          ‖hughesYoungPolynomialRatioTwo t u‖ *
          ‖hughesYoungGammaRatioTwo t u‖ ≤
        Real.exp (400 - 84 * u ^ 2) * B ^ 10 * A ^ 2 := by
    rw [hexp]
    calc
      Real.exp (400 - 100 * u ^ 2) *
            ‖hughesYoungAuxiliaryZero w‖ *
            ‖hughesYoungPolynomialRatioTwo t u‖ *
            ‖hughesYoungGammaRatioTwo t u‖
          ≤ Real.exp (400 - 100 * u ^ 2) * B ^ 4 * B ^ 4 *
              (Real.exp (16 * u ^ 2) * (B * A) ^ 2) := by
            gcongr
      _ = (Real.exp (400 - 100 * u ^ 2) * Real.exp (16 * u ^ 2)) *
            (B ^ 4 * B ^ 4 * (B * A) ^ 2) := by ring
      _ = Real.exp ((400 - 100 * u ^ 2) + 16 * u ^ 2) *
            (B ^ 4 * B ^ 4 * (B * A) ^ 2) := by rw [Real.exp_add]
      _ = Real.exp (400 - 84 * u ^ 2) * B ^ 10 * A ^ 2 := by
            rw [show (400 - 100 * u ^ 2) + 16 * u ^ 2 =
              400 - 84 * u ^ 2 by ring]
            ring
  rw [hughesYoungRightContourWeight_two_eq]
  change ‖(Complex.exp (100 * w ^ 2) * hughesYoungAuxiliaryZero w) *
      hughesYoungPolynomialRatioTwo t u *
      hughesYoungGammaRatioTwo t u / w‖ ≤ _
  rw [norm_div, norm_mul, norm_mul, norm_mul]
  calc
    ‖Complex.exp (100 * w ^ 2)‖ *
          ‖hughesYoungAuxiliaryZero w‖ *
          ‖hughesYoungPolynomialRatioTwo t u‖ *
          ‖hughesYoungGammaRatioTwo t u‖ / ‖w‖
        ≤ ‖Complex.exp (100 * w ^ 2)‖ *
          ‖hughesYoungAuxiliaryZero w‖ *
          ‖hughesYoungPolynomialRatioTwo t u‖ *
          ‖hughesYoungGammaRatioTwo t u‖ := by
            exact div_le_self (by positivity) hwNorm
    _ ≤ Real.exp (400 - 84 * u ^ 2) * B ^ 10 * A ^ 2 := hnum
    _ = Real.exp (400 - 84 * u ^ 2) *
        (25 + 8 * u ^ 2) ^ 10 * ((1 / 4 : ℝ) + t ^ 2) ^ 2 := by rfl

/-- Uniform height-support specialization of the right-contour bound. -/
theorem norm_hughesYoungRightContourWeight_two_le_on_height_support
    {T : ℝ} (hT : 1 ≤ T) {t : ℝ} (ht : t ∈ Set.Icc (T / 4) (4 * T))
    (u : ℝ) :
    ‖hughesYoungRightContourWeight t 2 u‖ ≤
      289 * Real.exp (400 - 84 * u ^ 2) *
        (25 + 8 * u ^ 2) ^ 10 * T ^ 4 := by
  have ht0 : 0 ≤ t := by linarith [ht.1]
  have htUpper : t ≤ 4 * T := ht.2
  have hT0 : 0 ≤ T := le_trans (by norm_num) hT
  have hsq : t ^ 2 ≤ (4 * T) ^ 2 := by
    exact pow_le_pow_left₀ ht0 htUpper 2
  have hA : (1 / 4 : ℝ) + t ^ 2 ≤ 17 * T ^ 2 := by
    have hTone : 1 ≤ T ^ 2 := by nlinarith
    nlinarith
  have hA0 : 0 ≤ (1 / 4 : ℝ) + t ^ 2 := by positivity
  have hA2 := pow_le_pow_left₀ hA0 hA 2
  calc
    ‖hughesYoungRightContourWeight t 2 u‖ ≤
        Real.exp (400 - 84 * u ^ 2) *
          (25 + 8 * u ^ 2) ^ 10 * ((1 / 4 : ℝ) + t ^ 2) ^ 2 :=
      norm_hughesYoungRightContourWeight_two_le t u
    _ ≤ Real.exp (400 - 84 * u ^ 2) *
          (25 + 8 * u ^ 2) ^ 10 * (17 * T ^ 2) ^ 2 := by
      gcongr
    _ = 289 * Real.exp (400 - 84 * u ^ 2) *
          (25 + 8 * u ^ 2) ^ 10 * T ^ 4 := by ring

/-- All logarithmic-frequency derivatives of the height transform on the
absolutely convergent line carry an explicit, uniform Gaussian majorant. -/
theorem norm_iteratedDeriv_hughesYoungHeightTransform_two_le
    {T : ℝ} (hT : 1 ≤ T) (u : ℝ) (j : ℕ) (xi : ℝ) :
    ‖iteratedDeriv j (hughesYoungHeightTransform T 2 u) xi‖ ≤
      (15 * T / 4) * ((4 * T) ^ j *
        (289 * Real.exp (400 - 84 * u ^ 2) *
          (25 + 8 * u ^ 2) ^ 10 * T ^ 4)) := by
  apply norm_iteratedDeriv_hughesYoungHeightTransform_le
    (lt_of_lt_of_le (by norm_num) hT) (by norm_num) u
  intro t ht
  exact norm_hughesYoungRightContourWeight_two_le_on_height_support hT ht u

/-- The explicit ordinate envelope which remains after placing the
Hughes--Young Mellin contour on `Re w = 2`. -/
noncomputable def hughesYoungRightContourEnvelope (T u : ℝ) : ℝ :=
  289 * Real.exp (400 - 84 * u ^ 2) *
    (25 + 8 * u ^ 2) ^ 10 * T ^ 4

theorem hughesYoungRightContourEnvelope_pos
    {T : ℝ} (hT : 0 < T) (u : ℝ) :
    0 < hughesYoungRightContourEnvelope T u := by
  unfold hughesYoungRightContourEnvelope
  positivity

/-- Source-normalized all-orders derivative estimate used in the DFI
consumer.  Dividing by the physical height removes the sole extra factor of
`T` in the Fourier moment bound. -/
theorem norm_one_div_mul_iteratedDeriv_hughesYoungHeightTransform_two_le
    {T : ℝ} (hT : 1 ≤ T) (u : ℝ) (j : ℕ) (xi : ℝ) :
    ‖(1 / (T : ℂ)) *
        iteratedDeriv j (hughesYoungHeightTransform T 2 u) xi‖ ≤
      (15 / 4 : ℝ) * ((4 * T) ^ j *
        hughesYoungRightContourEnvelope T u) := by
  have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hraw := norm_iteratedDeriv_hughesYoungHeightTransform_two_le
    hT u j xi
  rw [norm_mul, norm_div, norm_one, norm_real, Real.norm_eq_abs,
    abs_of_pos hT0]
  calc
    1 / T * ‖iteratedDeriv j (hughesYoungHeightTransform T 2 u) xi‖ ≤
        1 / T * ((15 * T / 4) *
          ((4 * T) ^ j * hughesYoungRightContourEnvelope T u)) := by
      exact mul_le_mul_of_nonneg_left hraw (by positivity)
    _ = (15 / 4 : ℝ) *
        ((4 * T) ^ j * hughesYoungRightContourEnvelope T u) := by
      field_simp [hT0.ne']

end RiemannZeta.GuthMaynard
