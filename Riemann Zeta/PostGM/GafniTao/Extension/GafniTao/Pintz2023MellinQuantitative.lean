import GafniTao.Pintz2023GammaExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Quantitative kernel bounds for Pintz (2023), Lemma 3.4

The zero of `(2N)^w - N^w` at `w = 0` is kept quantitatively: on the
imaginary axis it supplies a factor `|u|`, which cancels the pole of
`Gamma (iu)`.  Away from the origin we combine the elementary bound by two
with the exponential Gamma estimate.
-/

open Complex Set MeasureTheory

namespace GafniTao

noncomputable section

theorem norm_pintz2023MellinPowerDiff_imaginary_le_two
    {N : ℕ} (hN : 0 < N) (u : ℝ) :
    ‖pintz2023MellinPowerDiff N ((u : ℂ) * I)‖ ≤ 2 := by
  unfold pintz2023MellinPowerDiff
  calc
    ‖((2 * N : ℕ) : ℂ) ^ ((u : ℂ) * I) -
        (N : ℂ) ^ ((u : ℂ) * I)‖ ≤
        ‖((2 * N : ℕ) : ℂ) ^ ((u : ℂ) * I)‖ +
          ‖(N : ℂ) ^ ((u : ℂ) * I)‖ := norm_sub_le _ _
    _ = 1 + 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (mul_pos (by norm_num) hN),
        Complex.norm_natCast_cpow_of_pos hN]
      simp
    _ = 2 := by norm_num

private theorem two_cpow_imaginary_eq (u : ℝ) :
    (2 : ℂ) ^ ((u : ℂ) * I) =
      Complex.exp (I * ((Real.log 2 * u : ℝ) : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have hlog : Complex.log (2 : ℂ) = (Real.log 2 : ℂ) :=
    (Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2)).symm
  rw [hlog]
  congr 1
  push_cast
  ring

theorem norm_pintz2023MellinPowerDiff_imaginary_le_log
    {N : ℕ} (hN : 0 < N) (u : ℝ) :
    ‖pintz2023MellinPowerDiff N ((u : ℂ) * I)‖ ≤
      Real.log 2 * |u| := by
  unfold pintz2023MellinPowerDiff
  have hFactor : ((2 * N : ℕ) : ℂ) ^ ((u : ℂ) * I) =
      (2 : ℂ) ^ ((u : ℂ) * I) *
        (N : ℂ) ^ ((u : ℂ) * I) := by
    simpa using Complex.natCast_mul_natCast_cpow 2 N ((u : ℂ) * I)
  rw [hFactor]
  have hRewrite :
      (2 : ℂ) ^ ((u : ℂ) * I) * (N : ℂ) ^ ((u : ℂ) * I) -
          (N : ℂ) ^ ((u : ℂ) * I) =
        ((2 : ℂ) ^ ((u : ℂ) * I) - 1) *
          (N : ℂ) ^ ((u : ℂ) * I) := by ring
  rw [hRewrite]
  rw [norm_mul, two_cpow_imaginary_eq]
  rw [Complex.norm_natCast_cpow_of_pos hN]
  simp only [mul_re, ofReal_re, I_re, ofReal_im, I_im, mul_zero,
    sub_self, Real.rpow_zero, mul_one]
  calc
    ‖Complex.exp (I * ((Real.log 2 * u : ℝ) : ℂ)) - 1‖ ≤
        ‖Real.log 2 * u‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = Real.log 2 * |u| := by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.log_nonneg (by norm_num))]

theorem abs_mul_norm_Gamma_imaginary_le_one
    {u : ℝ} (hu : u ≠ 0) :
    |u| * ‖Complex.Gamma ((u : ℂ) * I)‖ ≤ 1 := by
  have hw : (u : ℂ) * I ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hu) I_ne_zero
  have hRec := Complex.Gamma_add_one ((u : ℂ) * I) hw
  have hGamma :
      ‖Complex.Gamma ((u : ℂ) * I + 1)‖ ≤ 1 := by
    have h := Complex.Gamma.norm_le_Gamma_re
      (z := (u : ℂ) * I + 1) (by norm_num)
    simpa using h
  calc
    |u| * ‖Complex.Gamma ((u : ℂ) * I)‖ =
        ‖(u : ℂ) * I * Complex.Gamma ((u : ℂ) * I)‖ := by
      rw [norm_mul, norm_mul, norm_real, norm_I, mul_one, Real.norm_eq_abs]
    _ = ‖Complex.Gamma ((u : ℂ) * I + 1)‖ := by rw [hRec]
    _ ≤ 1 := hGamma

theorem norm_pintz2023MellinWeight_imaginary_le_log
    {N : ℕ} (hN : 0 < N) {u : ℝ} (hu : u ≠ 0) :
    ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ ≤ Real.log 2 := by
  have hw : (u : ℂ) * I ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hu) I_ne_zero
  rw [pintz2023MellinWeight_eq hw, norm_mul]
  calc
    ‖pintz2023MellinPowerDiff N ((u : ℂ) * I)‖ *
        ‖Complex.Gamma ((u : ℂ) * I)‖ ≤
      (Real.log 2 * |u|) *
        ‖Complex.Gamma ((u : ℂ) * I)‖ := by
          gcongr
          exact norm_pintz2023MellinPowerDiff_imaginary_le_log hN u
    _ = Real.log 2 *
        (|u| * ‖Complex.Gamma ((u : ℂ) * I)‖) := by ring
    _ ≤ Real.log 2 * 1 := by
      gcongr
      exact abs_mul_norm_Gamma_imaginary_le_one hu
    _ = Real.log 2 := by ring

theorem exists_norm_pintz2023MellinWeight_imaginary_tail_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (u : ℝ), 0 < N → 1 ≤ |u| →
      ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ ≤
        C * (|u| + 2) * Real.exp (-(Real.pi * |u|) / 2) := by
  obtain ⟨D, hD, hGamma⟩ := exists_norm_Gamma_imaginary_le_exp
  refine ⟨2 * D, by positivity, ?_⟩
  intro N u hN hu
  have hu0 : u ≠ 0 := abs_pos.mp (zero_lt_one.trans_le hu)
  have hw : (u : ℂ) * I ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr hu0) I_ne_zero
  rw [pintz2023MellinWeight_eq hw, norm_mul]
  calc
    ‖pintz2023MellinPowerDiff N ((u : ℂ) * I)‖ *
        ‖Complex.Gamma ((u : ℂ) * I)‖ ≤
      2 * (D * (|u| + 2) * Real.exp (-(Real.pi * |u|) / 2)) := by
        gcongr
        · exact norm_pintz2023MellinPowerDiff_imaginary_le_two hN u
        · exact hGamma u hu
    _ = (2 * D) * (|u| + 2) *
        Real.exp (-(Real.pi * |u|) / 2) := by ring

set_option maxHeartbeats 800000 in
private theorem integrable_abs_add_two_mul_exp_pi :
    Integrable (fun u : ℝ =>
      (|u| + 2) * Real.exp (-(Real.pi * |u|) / 2)) := by
  let b : ℝ := Real.pi / 2
  let g : ℝ → ℝ := fun u =>
    (|u| + 2) * Real.exp (-(Real.pi * |u|) / 2)
  have hb : 0 < b := by dsimp [b]; positivity
  have hOneRaw := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (1 : ℝ)) (b := b)
    (by norm_num) (by norm_num) hb
  have hZeroRaw := integrableOn_rpow_mul_exp_neg_mul_rpow
    (p := (1 : ℝ)) (s := (0 : ℝ)) (b := b)
    (by norm_num) (by norm_num) hb
  have hOne : IntegrableOn (fun u : ℝ => u * Real.exp (-b * u)) (Ioi 0) := by
    simpa using hOneRaw
  have hZero : IntegrableOn (fun u : ℝ => Real.exp (-b * u)) (Ioi 0) := by
    simpa using hZeroRaw
  have hPos : IntegrableOn g (Ioi 0) := by
    have hSum := hOne.add (hZero.const_mul 2)
    apply hSum.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have huPos : 0 < u := hu
    simpa [g, abs_of_pos huPos, b] using
      (show u * Real.exp (-b * u) + 2 * Real.exp (-b * u) =
          (u + 2) * Real.exp (-(Real.pi * u) / 2) by
        have he : -b * u = -(Real.pi * u) / 2 := by
          dsimp only [b]
          ring
        rw [he]
        ring)
  have hComp : IntegrableOn (fun u : ℝ => g (-u)) (Iio 0) :=
    (show IntegrableOn g (Ioi (-0)) by simpa using hPos).comp_neg_Iio
  have hNegOpen : IntegrableOn g (Iio 0) := by
    apply hComp.congr
    filter_upwards with u
    simp [g]
  have hNeg : IntegrableOn g (Iic 0) :=
    (integrableOn_Iic_iff_integrableOn_Iio).mpr hNegOpen
  rw [← integrableOn_univ]
  have hUnion := integrableOn_union.2 ⟨hNeg, hPos⟩
  simpa only [Iic_union_Ioi, g] using hUnion

set_option maxHeartbeats 800000 in
/-- The `L¹` norm of Pintz's removable Mellin kernel on `Re w = 0` is
bounded independently of the smoothing scale `N`. -/
theorem exists_pintz2023MellinWeight_imaginary_integral_bound :
    ∃ L : ℝ, 0 < L ∧ ∀ N : ℕ, 0 < N →
      Integrable (fun u : ℝ => pintz2023MellinWeight N ((u : ℂ) * I)) ∧
      (∫ u : ℝ, ‖pintz2023MellinWeight N ((u : ℂ) * I)‖) ≤ L := by
  obtain ⟨C, hC, hTail⟩ := exists_norm_pintz2023MellinWeight_imaginary_tail_le
  let g : ℝ → ℝ := fun u =>
    (|u| + 2) * Real.exp (-(Real.pi * |u|) / 2)
  let m : ℝ → ℝ := fun u =>
    (Icc (-1 : ℝ) 1).indicator (fun _ => Real.log 2) u + C * g u
  have hCentral : Integrable
      ((Icc (-1 : ℝ) 1).indicator (fun _ => Real.log 2)) := by
    exact (integrableOn_const (s := Icc (-1 : ℝ) 1)
      measure_Icc_lt_top.ne).integrable_indicator measurableSet_Icc
  have hg : Integrable g := by
    simpa only [g] using integrable_abs_add_two_mul_exp_pi
  have hm : Integrable m := by
    exact hCentral.add (hg.const_mul C)
  let L : ℝ := (∫ u : ℝ, m u) + 1
  have hmNonneg : ∀ u : ℝ, 0 ≤ m u := by
    intro u
    dsimp only [m]
    by_cases hu : u ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem hu]
      positivity
    · rw [Set.indicator_of_notMem hu, zero_add]
      positivity
  have hIntNonneg : 0 ≤ ∫ u : ℝ, m u :=
    integral_nonneg hmNonneg
  refine ⟨L, by dsimp only [L]; linarith, ?_⟩
  intro N hN
  have hCont : Continuous (fun u : ℝ =>
      pintz2023MellinWeight N ((u : ℂ) * I)) := by
    apply continuous_iff_continuousAt.2
    intro u
    have hDiff := differentiableOn_pintz2023MellinWeight hN
      ((u : ℂ) * I) (by norm_num)
    have hOpen : IsOpen {w : ℂ | -(1 : ℝ) < w.re} :=
      isOpen_lt continuous_const continuous_re
    have hAt := hDiff.continuousWithinAt.continuousAt
      (hOpen.mem_nhds (by norm_num))
    exact ContinuousAt.comp
      (g := pintz2023MellinWeight N)
      (f := fun v : ℝ => (v : ℂ) * I) hAt (by fun_prop)
  have hBound : ∀ᵐ u : ℝ ∂volume,
      ‖pintz2023MellinWeight N ((u : ℂ) * I)‖ ≤ m u := by
    filter_upwards [(show ∀ᵐ u : ℝ ∂volume, u ≠ 0 by
      simp [ae_iff, measure_singleton])] with u hu
    by_cases hsmall : |u| ≤ 1
    · have hmem : u ∈ Icc (-1 : ℝ) 1 := by
        exact ⟨(abs_le.mp hsmall).1, (abs_le.mp hsmall).2⟩
      have hKernel := norm_pintz2023MellinWeight_imaginary_le_log hN hu
      dsimp only [m]
      rw [Set.indicator_of_mem hmem]
      exact hKernel.trans (le_add_of_nonneg_right (by positivity))
    · have hlarge : 1 ≤ |u| := by linarith
      have hnotmem : u ∉ Icc (-1 : ℝ) 1 := by
        intro hmem
        exact hsmall (abs_le.mpr hmem)
      have hKernel := hTail N u hN hlarge
      dsimp only [m]
      rw [Set.indicator_of_notMem hnotmem, zero_add]
      simpa only [g, mul_assoc] using hKernel
  have hf : Integrable (fun u : ℝ =>
      pintz2023MellinWeight N ((u : ℂ) * I)) :=
    hm.mono' hCont.aestronglyMeasurable hBound
  refine ⟨hf, ?_⟩
  have hIntegral := integral_mono_ae hf.norm hm hBound
  dsimp only [L]
  exact hIntegral.trans (le_add_of_nonneg_right zero_le_one)

#print axioms norm_pintz2023MellinPowerDiff_imaginary_le_two
#print axioms norm_pintz2023MellinPowerDiff_imaginary_le_log
#print axioms norm_pintz2023MellinWeight_imaginary_le_log
#print axioms exists_norm_pintz2023MellinWeight_imaginary_tail_le
#print axioms exists_pintz2023MellinWeight_imaginary_integral_bound

end

end GafniTao
