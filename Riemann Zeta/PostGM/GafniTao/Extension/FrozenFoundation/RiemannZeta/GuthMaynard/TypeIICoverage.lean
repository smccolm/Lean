import RiemannZeta.GuthMaynard.ClassicalDensity
import RiemannZeta.GuthMaynard.PolynomialPowers
import RiemannZeta.GuthMaynard.TypeIIContour
import RiemannZeta.External.PNT.ResidueCalcOnRectangles
import Mathlib.Analysis.MellinInversion
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet

open Complex
open MeasureTheory
open scoped ArithmeticFunction.Moebius BigOperators
open Classical

namespace RiemannZeta.GuthMaynard

/-- Absolute summability of the termwise `L¹` norms makes the pointwise
series integrable.  This is the integrability companion to Mathlib's
`hasSum_integral_of_summable_integral_norm`; it is used below to justify
Mellin inversion for the Appendix C detector rather than relying on a
totalized integral. -/
private theorem integrable_tsum_of_summable_integral_norm
    {α : Type*} [MeasurableSpace α] {measure : Measure α}
    {F : ℕ → α → ℂ}
    (hFint : ∀ n, MeasureTheory.Integrable (F n) measure)
    (hFsum : Summable (fun n => ∫ x, ‖F n x‖ ∂measure)) :
    MeasureTheory.Integrable (fun x => ∑' n, F n x) measure := by
  have hMeas (n : ℕ) : AEStronglyMeasurable (F n) measure := (hFint n).1
  have hNormMeas (n : ℕ) : AEMeasurable (fun x => ‖F n x‖ₑ) measure :=
    (hMeas n).enorm
  have hLIntegral : ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂measure ≠ ⊤ := by
    have hEach (n : ℕ) : ∫⁻ x, ‖F n x‖ₑ ∂measure = ‖∫ x, ‖F n x‖ ∂measure‖₊ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hFint n).norm, ENNReal.coe_nnreal_eq,
        coe_nnnorm, Real.norm_of_nonneg (integral_nonneg fun x => norm_nonneg (F n x))]
      simp only [coe_nnnorm]
    rw [funext hEach]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 <|
      NNReal.summable_coe.1 hFsum.abs
  have hPointwise : ∀ᵐ x ∂measure, Summable (fun n => (‖F n x‖₊ : ℝ)) := by
    rw [← lintegral_tsum hNormMeas] at hLIntegral
    refine (ae_lt_top' (AEMeasurable.tsum hNormMeas) hLIntegral).mono ?_
    intro x hx
    rw [← ENNReal.tsum_coe_ne_top_iff_summable_coe]
    exact hx.ne
  have hBoundInt : Integrable (fun x => ∑' n, ‖F n x‖) measure := by
    refine ⟨AEStronglyMeasurable.tsum (fun n => (hFint n).norm.1), ?_⟩
    dsimp [HasFiniteIntegral]
    have hFinite : ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂measure < ⊤ := by
      rw [lintegral_tsum hNormMeas, lt_top_iff_ne_top]
      exact hLIntegral
    convert hFinite using 1
    apply lintegral_congr_ae
    simp_rw [← coe_nnnorm, ← NNReal.coe_tsum, enorm_eq_nnnorm, NNReal.nnnorm_eq]
    filter_upwards [hPointwise] with x hx
    exact ENNReal.coe_tsum (NNReal.summable_coe.mp hx)
  refine hBoundInt.mono' (AEStronglyMeasurable.tsum hMeas) ?_
  filter_upwards [hPointwise] with x hx
  exact norm_tsum_le_tsum_norm hx

/-- The natural-number version of the real cutoff in Appendix C. -/
private noncomputable def appendixCMollifierCutoff (T : ℝ) : ℕ :=
  detectorCutoff T - 1

private lemma appendixCMollifierCutoff_add_one (T : ℝ) :
    appendixCMollifierCutoff T + 1 = detectorCutoff T := by
  rw [appendixCMollifierCutoff, detectorCutoff]
  omega

private lemma appendixCMollifierCutoff_eq_floor (T : ℝ) :
    appendixCMollifierCutoff T = ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ := by
  rw [appendixCMollifierCutoff, detectorCutoff]
  omega

/-- The source mollifier is exactly the project's finite zeta mollifier at
the natural cutoff corresponding to `2 * T^(1/100)`. -/
private theorem shortMobiusPolynomial_eq_zetaMollifier (T : ℝ) (s : ℂ) :
    shortMobiusPolynomial T s = zetaMollifier (appendixCMollifierCutoff T) s := by
  rw [shortMobiusPolynomial, zetaMollifier]
  apply Finset.sum_congr
  · ext m
    rw [Finset.mem_Ico, Finset.mem_Icc]
    have hCut := appendixCMollifierCutoff_add_one T
    omega
  · intro m hm
    rfl

/-- The divisor convolution in `detectorCoeff` is the coefficient of the
finite zeta--Möbius product used by the Mellin transform. -/
private theorem mobius_sum_eq_mollifiedZetaCoeff (T : ℝ) (n : ℕ) (hT : 0 ≤ T) :
    mobius_sum n T = mollifiedZetaCoeff (appendixCMollifierCutoff T) n := by
  rw [mobius_sum, mollifiedZetaCoeff]
  apply Finset.sum_congr
  · ext d
    simp only [detectorDivisors, Finset.mem_filter, Nat.mem_divisors]
    have hNonneg : 0 ≤ 2 * T ^ (1 / 100 : ℝ) :=
      mul_nonneg (by norm_num) (Real.rpow_nonneg hT _)
    constructor
    · rintro ⟨hd, hdCut⟩
      refine ⟨hd, ?_⟩
      have hdFloor : d ≤ ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ :=
        (Nat.le_floor_iff hNonneg).mpr hdCut
      simpa [appendixCMollifierCutoff_eq_floor] using hdFloor
    · rintro ⟨hd, hdCut⟩
      refine ⟨hd, ?_⟩
      have hdFloor : d ≤ ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ := by
        simpa [appendixCMollifierCutoff_eq_floor] using hdCut
      exact (Nat.le_floor_iff hNonneg).mp hdFloor
  · intro d hd
    rfl

/-- `detectorCoeff` is the exponentially smoothed coefficient of the exact
Dirichlet product `ζ(s) M(s)`. -/
private theorem detectorCoeff_eq_mollifiedZetaCoeff (T : ℝ) (n : ℕ) (hT : 0 ≤ T) :
    detectorCoeff n T = mollifiedZetaCoeff (appendixCMollifierCutoff T) n *
      Real.exp (-(n : ℝ) / T ^ (1 / 2 : ℝ)) := by
  rw [detectorCoeff, mobius_sum_eq_mollifiedZetaCoeff T n hT]

/-- Gamma is integrable on the positive line `Re s = 1/2`.  Shifting once
reduces this to the already established weighted estimate on `Re s = -1/2`. -/
private theorem integrable_Gamma_half_vertical :
    MeasureTheory.Integrable
      (fun u : ℝ => Complex.Gamma ((1 / 2 : ℂ) + (u : ℂ) * I)) := by
  let a : ℝ := -(1 / 2 : ℝ)
  let g : ℝ → ℂ := fun u =>
    (((1 + |u| : ℝ) : ℂ) * Complex.Gamma ((a : ℂ) + (u : ℂ) * I))
  have hg : MeasureTheory.Integrable g := by
    simpa [g, a] using integrable_one_add_abs_mul_typeII_Gamma_horizontal
      (a := a) (by dsimp [a]; exact le_rfl) (by dsimp [a]; norm_num)
  refine MeasureTheory.Integrable.mono' hg.norm ?_ ?_
  · apply Continuous.aestronglyMeasurable
    apply continuous_iff_continuousAt.2
    intro u
    have hNoPole : ∀ m : ℕ, (1 / 2 : ℂ) + (u : ℂ) * I ≠ -m := by
      intro m hm
      have hRe := congrArg Complex.re hm
      have hmNonneg : (0 : ℝ) ≤ m := by positivity
      norm_num at hRe
      linarith
    exact ContinuousAt.comp'
      (Complex.differentiableAt_Gamma _ hNoPole).continuousAt (by fun_prop)
  · filter_upwards with u
    let s : ℂ := (a : ℂ) + (u : ℂ) * I
    have hs : s ≠ 0 := by
      intro h
      have hRe := congrArg Complex.re h
      simp [s, a] at hRe
    have hRec : Complex.Gamma ((1 / 2 : ℂ) + (u : ℂ) * I) =
        s * Complex.Gamma s := by
      have hArg : (1 / 2 : ℂ) + (u : ℂ) * I = s + 1 := by
        simp [s, a]
        ring_nf
      rw [hArg, Complex.Gamma_add_one s hs]
    rw [hRec, norm_mul]
    change ‖s‖ * ‖Complex.Gamma s‖ ≤ ‖g u‖
    rw [show ‖g u‖ = (1 + |u|) * ‖Complex.Gamma s‖ by
      rw [show g u = ((1 + |u| : ℝ) : ℂ) * Complex.Gamma s by rfl, norm_mul]
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ (1 + |u| : ℝ))]]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      ‖s‖ ≤ |s.re| + |s.im| := Complex.norm_le_abs_re_add_abs_im s
      _ ≤ 1 + |u| := by simp [s, a]; norm_num

/-- The real exponential, coerced to `ℂ`, whose Mellin transform is Gamma. -/
private noncomputable def appendixCExponential (t : ℝ) : ℂ := Complex.exp (-(t : ℂ))

private theorem appendixCExponential_mellinConvergent :
    MellinConvergent appendixCExponential ((1 / 2 : ℝ) : ℂ) := by
  rw [MellinConvergent]
  have hGamma := Complex.GammaIntegral_convergent
    (s := ((1 / 2 : ℝ) : ℂ)) (by norm_num)
  apply hGamma.congr_fun
  · intro t ht
    simp only [appendixCExponential, Complex.ofReal_neg, Complex.ofReal_exp]
    rw [smul_eq_mul, mul_comm]
  · exact measurableSet_Ioi

private theorem mellin_appendixCExponential_eq_Gamma {s : ℂ} (hs : 0 < s.re) :
    mellin appendixCExponential s = Complex.Gamma s := by
  calc
    mellin appendixCExponential s = Complex.GammaIntegral s := by
      simpa [appendixCExponential] using
        congrFun Complex.GammaIntegral_eq_mellin s |>.symm
    _ = Complex.Gamma s := (Complex.Gamma_eq_integral hs).symm

private theorem verticalIntegrable_mellin_appendixCExponential :
    VerticalIntegrable (mellin appendixCExponential) (1 / 2 : ℝ) := by
  apply integrable_Gamma_half_vertical.congr
  filter_upwards with u
  have hRe : 0 < (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I).re := by norm_num
  convert (mellin_appendixCExponential_eq_Gamma hRe).symm using 1
  all_goals norm_num

private theorem continuous_appendixCExponential (x : ℝ) :
    ContinuousAt appendixCExponential x := by
  change ContinuousAt (fun t : ℝ => Complex.exp (-(t : ℂ))) x
  fun_prop

set_option maxHeartbeats 800000 in
/-- The inverse Mellin transform of Gamma on `Re s = 1/2` is the exponential
cutoff used in Appendix C. -/
private theorem mellinInv_half_Gamma_eq_exp_neg {x : ℝ} (hx : 0 < x) :
    mellinInv (1 / 2 : ℝ) Complex.Gamma x =
      (Real.exp (-x) : ℂ) := by
  have hInv : mellinInv (1 / 2 : ℝ) (mellin appendixCExponential) x =
      appendixCExponential x :=
    mellinInv_mellin_eq (1 / 2 : ℝ) appendixCExponential hx
      appendixCExponential_mellinConvergent
      verticalIntegrable_mellin_appendixCExponential
      (continuous_appendixCExponential x)
  calc
    mellinInv (1 / 2 : ℝ) Complex.Gamma x =
        mellinInv (1 / 2 : ℝ) (mellin appendixCExponential) x := by
      rw [mellinInv, mellinInv]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      rw [mellin_appendixCExponential_eq_Gamma (by norm_num)]
    _ = appendixCExponential x := hInv
    _ = (Real.exp (-x) : ℂ) := by
      simp [appendixCExponential]

/-- The exponentially smoothed zeta--Möbius Dirichlet series in Appendix C,
written with Mathlib's zero-safe L-series term. -/
private noncomputable def appendixCSmoothedDetector (ρ : ℂ) (T x : ℝ) : ℂ :=
  ∑' n : ℕ, LSeries.term (mollifiedZetaCoeff (appendixCMollifierCutoff T)) ρ n *
    Complex.exp (-((n : ℝ) * x))

private lemma norm_mollifiedZetaCoeff_le_detectorCutoff (T : ℝ) (n : ℕ) (hT : 0 ≤ T) :
    ‖mollifiedZetaCoeff (appendixCMollifierCutoff T) n‖ ≤
      (detectorCutoff T : ℝ) := by
  rw [← mobius_sum_eq_mollifiedZetaCoeff T n hT]
  exact norm_mobius_sum_le_cutoff n T

private lemma norm_appendixC_LSeries_term_le_detectorCutoff {ρ : ℂ} (T : ℝ) (n : ℕ)
    (hT : 0 ≤ T) (hρ : 0 ≤ ρ.re) :
    ‖LSeries.term (mollifiedZetaCoeff (appendixCMollifierCutoff T)) ρ n‖ ≤
      (detectorCutoff T : ℝ) := by
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · positivity
  · have hnOneNat : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hnOneNat
    have hPow : 1 ≤ (n : ℝ) ^ ρ.re := Real.one_le_rpow hnOne hρ
    exact (div_le_iff₀ (lt_of_lt_of_le zero_lt_one hPow)).2
      ((norm_mollifiedZetaCoeff_le_detectorCutoff T n hT).trans
        (by nlinarith [show (0 : ℝ) ≤ detectorCutoff T by positivity]))

/-- Absolute convergence of the smoothed detector at every positive smoothing
parameter, uniformly for `Re ρ ≥ 0`. -/
private theorem summable_appendixCSmoothedDetector {ρ : ℂ} {T x : ℝ}
    (hT : 0 ≤ T) (hx : 0 < x) (hρ : 0 ≤ ρ.re) :
    Summable (fun n : ℕ =>
      LSeries.term (mollifiedZetaCoeff (appendixCMollifierCutoff T)) ρ n *
        Complex.exp (-((n : ℝ) * x))) := by
  have hGeom : Summable (fun n : ℕ => Real.exp (-(n : ℝ) * x)) := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (Real.summable_exp_nat_mul_iff.mpr (show -x < 0 by linarith))
  apply Summable.of_norm
  refine (hGeom.mul_left (detectorCutoff T : ℝ)).of_nonneg_of_le
    (fun n => norm_nonneg _) ?_
  intro n
  rw [norm_mul, Complex.norm_exp]
  have hRe : (-(((n : ℝ) : ℂ) * (x : ℂ))).re = -((n : ℝ) * x) := by
    norm_num
  rw [hRe]
  have hExpEq : Real.exp (-((n : ℝ) * x)) = Real.exp (-(n : ℝ) * x) := by
    congr 1
    ring
  rw [← hExpEq]
  apply mul_le_mul_of_nonneg_right
    (norm_appendixC_LSeries_term_le_detectorCutoff T n hT hρ)
  exact (Real.exp_pos (-((n : ℝ) * x))).le

private theorem hasSum_appendixCSmoothedDetector {ρ : ℂ} {T x : ℝ}
    (hT : 0 ≤ T) (hx : 0 < x) (hρ : 0 ≤ ρ.re) :
    HasSum (fun n : ℕ =>
      LSeries.term (mollifiedZetaCoeff (appendixCMollifierCutoff T)) ρ n *
        Complex.exp (-((n : ℝ) * x)))
      (appendixCSmoothedDetector ρ T x) := by
  exact (summable_appendixCSmoothedDetector hT hx hρ).hasSum

/-- The detector series in the notation used by the finite Type-I blocks. -/
private noncomputable def appendixCDetectorValue (ρ : ℂ) (T : ℝ) : ℂ :=
  ∑' n : ℕ, detectorCoeff n T * (n : ℂ) ^ (-ρ)

private lemma appendixC_smoothed_term_eq_detector_term {ρ : ℂ} {T : ℝ}
    (hT : 0 < T) (n : ℕ) :
    LSeries.term (mollifiedZetaCoeff (appendixCMollifierCutoff T)) ρ n *
        Complex.exp (((-((n : ℝ) / T ^ (1 / 2 : ℝ))) : ℝ) : ℂ) =
      detectorCoeff n T * (n : ℂ) ^ (-ρ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [detectorCoeff, mobius_sum, detectorDivisors]
  · rw [LSeries.term_of_ne_zero hn,
      detectorCoeff_eq_mollifiedZetaCoeff T n hT.le]
    rw [Complex.cpow_neg, div_eq_mul_inv]
    rw [← Complex.ofReal_exp]
    ring_nf

/-- Evaluating the smoothed L-series at `x = T⁻¹ᐟ²` gives exactly the
project's infinite detector value. -/
private theorem appendixCSmoothedDetector_at_scale {ρ : ℂ} {T : ℝ}
    (hT : 0 < T) :
    appendixCSmoothedDetector ρ T (1 / T ^ (1 / 2 : ℝ)) =
      appendixCDetectorValue ρ T := by
  unfold appendixCSmoothedDetector appendixCDetectorValue
  apply tsum_congr
  intro n
  have hArg : -(((n : ℝ) : ℂ) * ((1 / T ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
      (((-((n : ℝ) / T ^ (1 / 2 : ℝ))) : ℝ) : ℂ) := by
    push_cast
    simp [div_eq_mul_inv]
  rw [hArg]
  exact appendixC_smoothed_term_eq_detector_term hT n

private lemma norm_LSeries_term_div_rpow_eq_add (f : ℕ → ℂ) (ρ s : ℂ) (n : ℕ) :
    ‖LSeries.term f ρ n‖ / (n : ℝ) ^ s.re =
      ‖LSeries.term f (ρ + s) n‖ := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [LSeries.norm_term_eq, LSeries.norm_term_eq, if_neg hn, if_neg hn]
    rw [add_re, Real.rpow_add hnPos]
    field_simp [ne_of_gt (Real.rpow_pos_of_pos hnPos ρ.re),
      ne_of_gt (Real.rpow_pos_of_pos hnPos s.re)]

private lemma Gamma_mul_term_div_cpow_eq_add (f : ℕ → ℂ) (ρ s : ℂ) (n : ℕ) :
    Complex.Gamma s * LSeries.term f ρ n / (n : ℝ) ^ s =
      Complex.Gamma s * LSeries.term f (ρ + s) n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    rw [Complex.ofReal_natCast, Complex.cpow_add _ _ hnC]
    field_simp [Complex.cpow_ne_zero_iff.mpr (Or.inl hnC)]

set_option maxHeartbeats 800000 in
/-- Mellin transformation of the smoothed detector on every line where the
underlying zeta--Möbius L-series converges absolutely. -/
private theorem mellin_appendixCSmoothedDetector_eq {ρ s : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hρ : 0 ≤ ρ.re) (hs : 0 < s.re)
    (hAbs : 1 < (ρ + s).re) :
    mellin (appendixCSmoothedDetector ρ T) s =
      Complex.Gamma s * LSeries (mollifiedZetaCoeff (appendixCMollifierCutoff T))
        (ρ + s) := by
  let f : ℕ → ℂ := mollifiedZetaCoeff (appendixCMollifierCutoff T)
  have hLS : LSeriesSummable f (ρ + s) :=
    mollifiedZetaCoeff_LSeriesSummable (appendixCMollifierCutoff T) hAbs
  have hSumNorm : Summable (fun n : ℕ =>
      ‖LSeries.term f ρ n‖ / (n : ℝ) ^ s.re) := by
    have hNorm : Summable (fun n : ℕ => ‖LSeries.term f (ρ + s) n‖) :=
      summable_norm_iff.mpr hLS
    exact hNorm.congr (fun n => (norm_LSeries_term_div_rpow_eq_add f ρ s n).symm)
  have hMellin : HasSum (fun n : ℕ =>
      Complex.Gamma s * LSeries.term f ρ n / (n : ℝ) ^ s)
      (mellin (appendixCSmoothedDetector ρ T) s) := by
    apply hasSum_mellin
    · intro n
      rcases eq_or_ne n 0 with rfl | hn
      · left
        simp
      · right
        exact_mod_cast Nat.pos_of_ne_zero hn
    · exact hs
    · intro x hx
      have hSeries := hasSum_appendixCSmoothedDetector hT hx hρ
      simpa [f, Complex.ofReal_exp] using hSeries
    · exact hSumNorm
  have hMellin' : HasSum (fun n : ℕ =>
      Complex.Gamma s * LSeries.term f (ρ + s) n)
      (mellin (appendixCSmoothedDetector ρ T) s) :=
    hMellin.congr_fun (fun n => (Gamma_mul_term_div_cpow_eq_add f ρ s n).symm)
  have hProduct : HasSum (fun n : ℕ =>
      Complex.Gamma s * LSeries.term f (ρ + s) n)
      (Complex.Gamma s * LSeries f (ρ + s)) := by
    exact hLS.hasSum.mul_left (Complex.Gamma s)
  exact hMellin'.unique hProduct

/-- A fixed convergent p-series used to dominate all right-line detector
L-series uniformly in the ordinate. -/
private noncomputable def appendixCPSeries : ℝ :=
  ∑' n : ℕ, (n : ℝ) ^ (-(6 / 5 : ℝ))

private theorem summable_appendixCPSeries :
    Summable (fun n : ℕ => (n : ℝ) ^ (-(6 / 5 : ℝ))) := by
  exact Real.summable_nat_rpow.mpr (by norm_num)

private theorem appendixCPSeries_nonneg : 0 ≤ appendixCPSeries := by
  exact tsum_nonneg (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _)

private theorem norm_mollified_LSeries_le_cutoff_mul_pSeries {z : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hz : 6 / 5 ≤ z.re) :
    ‖LSeries (mollifiedZetaCoeff (appendixCMollifierCutoff T)) z‖ ≤
      (detectorCutoff T : ℝ) * appendixCPSeries := by
  let f : ℕ → ℂ := mollifiedZetaCoeff (appendixCMollifierCutoff T)
  have hAbs : 1 < z.re := by linarith
  have hLS : LSeriesSummable f z :=
    mollifiedZetaCoeff_LSeriesSummable (appendixCMollifierCutoff T) hAbs
  have hNorm : Summable (fun n : ℕ => ‖LSeries.term f z n‖) :=
    summable_norm_iff.mpr hLS
  have hTerm (n : ℕ) : ‖LSeries.term f z n‖ ≤
      (detectorCutoff T : ℝ) * (n : ℝ) ^ (-(6 / 5 : ℝ)) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hDen : (n : ℝ) ^ (6 / 5 : ℝ) ≤ (n : ℝ) ^ z.re :=
        Real.rpow_le_rpow_of_exponent_le hnOne hz
      rw [LSeries.norm_term_eq, if_neg hn]
      rw [Real.rpow_neg hnPos.le]
      have hCoeff := norm_mollifiedZetaCoeff_le_detectorCutoff T n hT
      have hLeft : ‖f n‖ / (n : ℝ) ^ z.re ≤
          (detectorCutoff T : ℝ) / (n : ℝ) ^ z.re := by
        exact div_le_div_of_nonneg_right hCoeff (Real.rpow_nonneg hnPos.le _)
      have hRight : (detectorCutoff T : ℝ) / (n : ℝ) ^ z.re ≤
          (detectorCutoff T : ℝ) / (n : ℝ) ^ (6 / 5 : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) (Real.rpow_pos_of_pos hnPos _)
          hDen
      exact hLeft.trans hRight
  calc
    ‖LSeries f z‖ ≤ ∑' n : ℕ, ‖LSeries.term f z n‖ :=
      norm_tsum_le_tsum_norm hNorm
    _ ≤ ∑' n : ℕ, (detectorCutoff T : ℝ) *
        (n : ℝ) ^ (-(6 / 5 : ℝ)) := by
      exact hNorm.tsum_le_tsum hTerm
        (summable_appendixCPSeries.mul_left (detectorCutoff T : ℝ))
    _ = (detectorCutoff T : ℝ) * appendixCPSeries := by
      rw [appendixCPSeries, tsum_mul_left]

set_option maxHeartbeats 800000 in
/-- The Mellin transform of the smoothed detector is genuinely integrable on
the right line `Re s = 1/2`, uniformly for the source range `Re ρ ≥ 7/10`. -/
private theorem verticalIntegrable_mellin_appendixCSmoothedDetector {ρ : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hρ : 7 / 10 ≤ ρ.re) :
    VerticalIntegrable (mellin (appendixCSmoothedDetector ρ T)) (1 / 2 : ℝ) := by
  let line : ℝ → ℂ := fun u => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I
  let g : ℝ → ℂ := fun u => Complex.Gamma (line u) *
    (riemannZeta (ρ + line u) *
      zetaMollifier (appendixCMollifierCutoff T) (ρ + line u))
  have hGammaCont : Continuous (fun u : ℝ => Complex.Gamma (line u)) := by
    apply continuous_iff_continuousAt.2
    intro u
    have hNoPole : ∀ m : ℕ, line u ≠ -m := by
      intro m hm
      have hRe := congrArg Complex.re hm
      have hmNonneg : (0 : ℝ) ≤ m := by positivity
      simp [line] at hRe
      linarith
    exact ContinuousAt.comp' (Complex.differentiableAt_Gamma _ hNoPole).continuousAt
      (by dsimp [line]; fun_prop)
  have hZetaCont : Continuous (fun u : ℝ => riemannZeta (ρ + line u)) := by
    apply continuous_iff_continuousAt.2
    intro u
    have hzRe : 1 < (ρ + line u).re := by simp [line]; linarith
    have hzNe : ρ + line u ≠ 1 := by
      intro hz
      have hRe := congrArg Complex.re hz
      simp [line] at hRe
      linarith
    exact ContinuousAt.comp' (differentiableAt_riemannZeta hzNe).continuousAt
      (by dsimp [line]; fun_prop)
  have hShortCont : Continuous (fun u : ℝ =>
      shortMobiusPolynomial T (ρ + line u)) := by
    simpa [line, add_assoc] using
      continuous_shortMobiusPolynomial_vertical T
        (ρ + ((1 / 2 : ℝ) : ℂ))
  have hMollCont : Continuous (fun u : ℝ =>
      zetaMollifier (appendixCMollifierCutoff T) (ρ + line u)) := by
    simpa only [← shortMobiusPolynomial_eq_zetaMollifier] using hShortCont
  have hgCont : Continuous g := by
    exact hGammaCont.mul (hZetaCont.mul hMollCont)
  let C : ℝ := (detectorCutoff T : ℝ) * appendixCPSeries
  have hDom : MeasureTheory.Integrable (fun u : ℝ =>
      C * ‖Complex.Gamma (line u)‖) := by
    have hGammaInt : MeasureTheory.Integrable
        (fun u : ℝ => Complex.Gamma (line u)) := by
      simpa [line] using integrable_Gamma_half_vertical
    exact hGammaInt.norm.const_mul C
  have hg : MeasureTheory.Integrable g := by
    refine MeasureTheory.Integrable.mono' hDom hgCont.aestronglyMeasurable ?_
    filter_upwards with u
    have hzRe : 6 / 5 ≤ (ρ + line u).re := by simp [line]; linarith
    have hAbs : 1 < (ρ + line u).re := by linarith
    have hLSeries := norm_mollified_LSeries_le_cutoff_mul_pSeries hT hzRe
    have hProduct := riemannZeta_mul_zetaMollifier_eq_LSeries
      (appendixCMollifierCutoff T) hAbs
    dsimp [g]
    rw [norm_mul, hProduct]
    dsimp [C]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hLSeries
      (norm_nonneg (Complex.Gamma (line u)))
  apply hg.congr
  filter_upwards with u
  have hsRe : 0 < (line u).re := by simp [line]
  have hρNonneg : 0 ≤ ρ.re := by linarith
  have hAbs : 1 < (ρ + line u).re := by simp [line]; linarith
  rw [mellin_appendixCSmoothedDetector_eq hT hρNonneg hsRe hAbs]
  dsimp [g]
  rw [riemannZeta_mul_zetaMollifier_eq_LSeries
    (appendixCMollifierCutoff T) hAbs]

set_option maxHeartbeats 800000 in
/-- The smoothed detector is continuous at every positive smoothing
parameter.  Uniform convergence is obtained on the neighborhood `[x/2,∞)`
from the same geometric majorant used for absolute convergence. -/
private theorem continuousAt_appendixCSmoothedDetector {ρ : ℂ} {T x : ℝ}
    (hT : 0 ≤ T) (hx : 0 < x) (hρ : 0 ≤ ρ.re) :
    ContinuousAt (appendixCSmoothedDetector ρ T) x := by
  let x₀ : ℝ := x / 2
  let term : ℕ → ℝ → ℂ := fun n y =>
    LSeries.term (mollifiedZetaCoeff (appendixCMollifierCutoff T)) ρ n *
      Complex.exp (-((n : ℝ) * y))
  let majorant : ℕ → ℝ := fun n =>
    (detectorCutoff T : ℝ) * Real.exp (-((n : ℝ) * x₀))
  have hx₀ : 0 < x₀ := by dsimp [x₀]; linarith
  have hMajorant : Summable majorant := by
    have hGeom : Summable (fun n : ℕ => Real.exp (-(n : ℝ) * x₀)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Real.summable_exp_nat_mul_iff.mpr (show -x₀ < 0 by linarith))
    simpa [majorant] using hGeom.mul_left (detectorCutoff T : ℝ)
  have hTermCont (n : ℕ) : ContinuousOn (term n) (Set.Ici x₀) := by
    apply Continuous.continuousOn
    dsimp [term]
    fun_prop
  have hBound (n : ℕ) (y : ℝ) (hy : y ∈ Set.Ici x₀) :
      ‖term n y‖ ≤ majorant n := by
    have hnNonneg : (0 : ℝ) ≤ n := by positivity
    have hArg : -((n : ℝ) * y) ≤ -((n : ℝ) * x₀) := by
      have := hy
      simp only [Set.mem_Ici] at this
      nlinarith
    have hExp : Real.exp (-((n : ℝ) * y)) ≤
        Real.exp (-((n : ℝ) * x₀)) := Real.exp_le_exp.mpr hArg
    dsimp [term, majorant]
    rw [norm_mul, Complex.norm_exp]
    have hRe : (-((n : ℂ) * (y : ℂ))).re = -((n : ℝ) * y) := by
      norm_num
    rw [hRe]
    calc
      ‖LSeries.term (mollifiedZetaCoeff (appendixCMollifierCutoff T)) ρ n‖ *
          Real.exp (-((n : ℝ) * y))
          ≤ (detectorCutoff T : ℝ) * Real.exp (-((n : ℝ) * y)) :=
        mul_le_mul_of_nonneg_right
          (norm_appendixC_LSeries_term_le_detectorCutoff T n hT hρ)
          (Real.exp_pos _).le
      _ ≤ (detectorCutoff T : ℝ) * Real.exp (-((n : ℝ) * x₀)) :=
        mul_le_mul_of_nonneg_left hExp (by positivity)
  have hContinuousOn : ContinuousOn (appendixCSmoothedDetector ρ T) (Set.Ici x₀) := by
    change ContinuousOn (fun y => ∑' n : ℕ, term n y) (Set.Ici x₀)
    exact continuousOn_tsum hTermCont hMajorant hBound
  have hNhd : Set.Ici x₀ ∈ nhds x := by
    apply Filter.mem_of_superset
      (Ioi_mem_nhds (show x₀ < x by dsimp [x₀]; linarith))
    exact Set.Ioi_subset_Ici_self
  exact hContinuousOn.continuousAt hNhd

set_option maxHeartbeats 800000 in
/-- Absolute convergence in the Mellin variable on `Re s = 1/2`.  The key
summability exponent is `Re ρ + 1/2 > 1`; this is exactly why Appendix C
works uniformly in the repaired source range `Re ρ ≥ 7/10`. -/
private theorem mellinConvergent_appendixCSmoothedDetector {ρ : ℂ} {T : ℝ}
    (hT : 0 ≤ T) (hρ : 7 / 10 ≤ ρ.re) :
    MellinConvergent (appendixCSmoothedDetector ρ T) ((1 / 2 : ℝ) : ℂ) := by
  let f : ℕ → ℂ := mollifiedZetaCoeff (appendixCMollifierCutoff T)
  let s : ℂ := ((1 / 2 : ℝ) : ℂ)
  let a : ℕ → ℂ := fun n => LSeries.term f ρ n
  let term : ℕ → ℝ → ℂ := fun n t =>
    a n * ((t : ℂ) ^ (s - 1) * Real.exp (-(n : ℝ) * t))
  have hs : 0 < s.re := by simp [s]
  have hAbs : 1 < (ρ + s).re := by simp [s]; linarith
  have hLS : LSeriesSummable f (ρ + s) :=
    mollifiedZetaCoeff_LSeriesSummable (appendixCMollifierCutoff T) hAbs
  have hSumNorm : Summable (fun n => ‖a n‖ / (n : ℝ) ^ s.re) := by
    have hNorm : Summable (fun n => ‖LSeries.term f (ρ + s) n‖) :=
      summable_norm_iff.mpr hLS
    exact hNorm.congr fun n => by
      simpa [a] using (norm_LSeries_term_div_rpow_eq_add f ρ s n).symm
  have hTermInt (n : ℕ) : MeasureTheory.IntegrableOn (term n) (Set.Ioi 0) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [term, a, LSeries.term]
    · have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hGamma := Complex.GammaIntegral_convergent hs
      rw [← mul_zero (n : ℝ),
        ← integrableOn_Ioi_comp_mul_left_iff _ _ hnPos] at hGamma
      refine (MeasureTheory.IntegrableOn.congr_fun
        (hGamma.const_mul (1 / (((n : ℝ) : ℂ) ^ (s - 1)))) ?_ measurableSet_Ioi).const_mul (a n)
      intro t ht
      change 1 / (((n : ℝ) : ℂ) ^ (s - 1)) *
          ((Real.exp (-((n : ℝ) * t)) : ℂ) *
            ((((n : ℝ) * t : ℝ) : ℂ) ^ (s - 1))) =
        (t : ℂ) ^ (s - 1) * (Real.exp (-(n : ℝ) * t) : ℂ)
      rw [mul_comm (Real.exp _ : ℂ), ← mul_assoc, neg_mul, Complex.ofReal_mul]
      rw [Complex.mul_cpow_ofReal_nonneg hnPos.le ht.le, ← mul_assoc, one_div,
        inv_mul_cancel₀, one_mul]
      rw [Ne, Complex.cpow_eq_zero_iff, not_and_or]
      exact Or.inl (Complex.ofReal_ne_zero.mpr hnPos.ne')
  have hTermSum : Summable (fun n => ∫ t in Set.Ioi 0, ‖term n t‖) := by
    apply Summable.of_norm
    convert! hSumNorm.mul_left (Real.Gamma s.re) using 2 with n
    simp_rw [term, norm_mul (a n), integral_const_mul]
    rw [← mul_div_assoc, mul_comm (Real.Gamma _), mul_div_assoc,
      norm_mul ‖a n‖, norm_norm]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [a, LSeries.term]
    congr 1
    have hnPos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hReal := Real.integral_rpow_mul_exp_neg_mul_Ioi hs hnPos
    simp_rw [← neg_mul (n : ℝ), one_div, Real.inv_rpow hnPos.le,
      ← div_eq_inv_mul] at hReal
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← hReal]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Real.abs_exp,
      norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  have hSeriesInt : MeasureTheory.IntegrableOn (fun t => ∑' n, term n t) (Set.Ioi 0) :=
    integrable_tsum_of_summable_integral_norm hTermInt hTermSum
  rw [MellinConvergent]
  apply hSeriesInt.congr_fun
  · intro t ht
    have htPos : 0 < t := ht
    have hSeries := hasSum_appendixCSmoothedDetector hT htPos (by linarith : 0 ≤ ρ.re)
    have hMul := hSeries.mul_left ((t : ℂ) ^ (s - 1))
    calc
      ∑' n, term n t = ∑' n,
          (t : ℂ) ^ (s - 1) *
            (LSeries.term (mollifiedZetaCoeff (appendixCMollifierCutoff T)) ρ n *
              Complex.exp (-((n : ℝ) * t))) := by
        apply tsum_congr
        intro n
        dsimp [term, a, f]
        rw [Complex.ofReal_exp]
        push_cast
        ring_nf
      _ = (t : ℂ) ^ (s - 1) * appendixCSmoothedDetector ρ T t := by
        simpa [Complex.ofReal_exp] using hMul.tsum_eq
  · exact measurableSet_Ioi

set_option maxHeartbeats 800000 in
/-- Exact inverse-Mellin representation of the infinite Appendix C detector
on the absolutely convergent line `Re s = 1/2`. -/
private theorem appendixCDetectorValue_eq_mellinInv_rightLine {ρ : ℂ} {T : ℝ}
    (hT : 0 < T) (hρ : 7 / 10 ≤ ρ.re) :
    appendixCDetectorValue ρ T =
      mellinInv (1 / 2 : ℝ)
        (fun s => Complex.Gamma s *
          LSeries (mollifiedZetaCoeff (appendixCMollifierCutoff T)) (ρ + s))
        (1 / T ^ (1 / 2 : ℝ)) := by
  let x : ℝ := 1 / T ^ (1 / 2 : ℝ)
  have hx : 0 < x := by
    dsimp [x]
    positivity
  have hInv : mellinInv (1 / 2 : ℝ)
      (mellin (appendixCSmoothedDetector ρ T)) x =
      appendixCSmoothedDetector ρ T x :=
    mellinInv_mellin_eq (1 / 2 : ℝ) (appendixCSmoothedDetector ρ T) hx
      (mellinConvergent_appendixCSmoothedDetector hT.le hρ)
      (verticalIntegrable_mellin_appendixCSmoothedDetector hT.le hρ)
      (continuousAt_appendixCSmoothedDetector hT.le hx (by linarith : 0 ≤ ρ.re))
  calc
    appendixCDetectorValue ρ T = appendixCSmoothedDetector ρ T x := by
      symm
      simpa [x] using appendixCSmoothedDetector_at_scale (ρ := ρ) hT
    _ = mellinInv (1 / 2 : ℝ) (mellin (appendixCSmoothedDetector ρ T)) x := hInv.symm
    _ = mellinInv (1 / 2 : ℝ)
        (fun s => Complex.Gamma s *
          LSeries (mollifiedZetaCoeff (appendixCMollifierCutoff T)) (ρ + s)) x := by
      rw [mellinInv, mellinInv]
      congr 1
      apply MeasureTheory.integral_congr_ae
      filter_upwards with u
      let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I
      have hs : 0 < s.re := by simp [s]
      have hAbs : 1 < (ρ + s).re := by simp [s]; linarith
      rw [mellin_appendixCSmoothedDetector_eq hT.le (by linarith : 0 ≤ ρ.re) hs hAbs]
    _ = mellinInv (1 / 2 : ℝ)
        (fun s => Complex.Gamma s *
          LSeries (mollifiedZetaCoeff (appendixCMollifierCutoff T)) (ρ + s))
        (1 / T ^ (1 / 2 : ℝ)) := by rfl

/-- Pole-removed zeta after translating the zero `ρ` to the origin. -/
private noncomputable def appendixCShiftedRegularizedZeta (ρ s : ℂ) : ℂ :=
  regularizedRiemannZeta (ρ + s)

/-- The analytic quotient which removes the apparent `Γ(s)` singularity at
`s = 0` when `ζ(ρ)=0`. -/
private noncomputable def appendixCZeroQuotient (ρ s : ℂ) : ℂ :=
  dslope (appendixCShiftedRegularizedZeta ρ) 0 s

/-- Entire numerator on the Appendix C rectangle.  The only remaining pole
of the original contour integrand is represented explicitly by division by
`s - (1 - ρ)`. -/
private noncomputable def appendixCContourNumerator (ρ : ℂ) (T : ℝ) (s : ℂ) : ℂ :=
  (T : ℂ) ^ (s / 2) * Complex.Gamma (s + 1) *
    shortMobiusPolynomial T (ρ + s) * appendixCZeroQuotient ρ s

/-- The residue crossed at the zeta pole `s = 1 - ρ`. -/
private noncomputable def appendixCContourResidue (ρ : ℂ) (T : ℝ) : ℂ :=
  (T : ℂ) ^ ((1 - ρ) / 2) * Complex.Gamma (1 - ρ) *
    shortMobiusPolynomial T 1

/-- The source contour kernel as a function of the complex shift variable. -/
private noncomputable def appendixCContourKernel (ρ : ℂ) (T : ℝ) (s : ℂ) : ℂ :=
  (T : ℂ) ^ (s / 2) * Complex.Gamma s *
    shortMobiusPolynomial T (ρ + s) * riemannZeta (ρ + s)

private theorem appendixCShiftedRegularizedZeta_zero {ρ : ℂ}
    (hρOne : ρ ≠ 1) (hZero : riemannZeta ρ = 0) :
    appendixCShiftedRegularizedZeta ρ 0 = 0 := by
  rw [appendixCShiftedRegularizedZeta, add_zero, regularizedRiemannZeta,
    Function.update_of_ne hρOne, hZero, mul_zero]

private theorem appendixCShiftedRegularizedZeta_eq {ρ s : ℂ}
    (hPole : ρ + s ≠ 1) :
    appendixCShiftedRegularizedZeta ρ s =
      (s - (1 - ρ)) * riemannZeta (ρ + s) := by
  rw [appendixCShiftedRegularizedZeta, regularizedRiemannZeta,
    Function.update_of_ne hPole]
  ring

/-- Away from the two removed points, the analytic numerator divided by its
explicit zeta-pole factor is exactly the original Appendix C integrand. -/
private theorem appendixCContourNumerator_div_eq_integrand {ρ s : ℂ} {T : ℝ}
    (hρOne : ρ ≠ 1) (hZero : riemannZeta ρ = 0)
    (hsZero : s ≠ 0) (hsPole : s ≠ 1 - ρ) :
    appendixCContourNumerator ρ T s / (s - (1 - ρ)) =
      (T : ℂ) ^ (s / 2) * Complex.Gamma s *
        shortMobiusPolynomial T (ρ + s) * riemannZeta (ρ + s) := by
  have hR0 := appendixCShiftedRegularizedZeta_zero hρOne hZero
  have hShiftPole : ρ + s ≠ 1 := by
    intro h
    apply hsPole
    linear_combination h
  have hSlope := sub_smul_dslope_of_zero hR0 s
  have hQuotient : s * appendixCZeroQuotient ρ s =
      (s - (1 - ρ)) * riemannZeta (ρ + s) := by
    simpa [appendixCZeroQuotient, appendixCShiftedRegularizedZeta_eq hShiftPole,
      smul_eq_mul] using hSlope
  rw [div_eq_iff (sub_ne_zero.mpr hsPole)]
  unfold appendixCContourNumerator
  rw [Complex.Gamma_add_one s hsZero]
  calc
    (T : ℂ) ^ (s / 2) * (s * Complex.Gamma s) *
          shortMobiusPolynomial T (ρ + s) * appendixCZeroQuotient ρ s =
        (T : ℂ) ^ (s / 2) * Complex.Gamma s *
          shortMobiusPolynomial T (ρ + s) *
            (s * appendixCZeroQuotient ρ s) := by ring
    _ = (T : ℂ) ^ (s / 2) * Complex.Gamma s *
          shortMobiusPolynomial T (ρ + s) *
            ((s - (1 - ρ)) * riemannZeta (ρ + s)) := by rw [hQuotient]
    _ = ((T : ℂ) ^ (s / 2) * Complex.Gamma s *
          shortMobiusPolynomial T (ρ + s) * riemannZeta (ρ + s)) *
            (s - (1 - ρ)) := by ring

/-- Exact residue evaluation at `s = 1 - ρ`. -/
private theorem appendixCContourNumerator_at_pole {ρ : ℂ} {T : ℝ}
    (hρOne : ρ ≠ 1) (hZero : riemannZeta ρ = 0) :
    appendixCContourNumerator ρ T (1 - ρ) = appendixCContourResidue ρ T := by
  let p : ℂ := 1 - ρ
  have hpZero : p ≠ 0 := sub_ne_zero.mpr hρOne.symm
  have hR0 := appendixCShiftedRegularizedZeta_zero hρOne hZero
  have hRp : appendixCShiftedRegularizedZeta ρ p = 1 := by
    have hρp : ρ + p = 1 := by dsimp [p]; ring
    rw [appendixCShiftedRegularizedZeta, hρp, regularizedRiemannZeta]
    simp
  have hSlope := sub_smul_dslope_of_zero hR0 p
  have hQuotient : p * appendixCZeroQuotient ρ p = 1 := by
    simpa [appendixCZeroQuotient, hRp, smul_eq_mul] using hSlope
  unfold appendixCContourNumerator appendixCContourResidue
  change (T : ℂ) ^ (p / 2) * Complex.Gamma (p + 1) *
      shortMobiusPolynomial T (ρ + p) * appendixCZeroQuotient ρ p =
    (T : ℂ) ^ (p / 2) * Complex.Gamma p * shortMobiusPolynomial T 1
  rw [Complex.Gamma_add_one p hpZero]
  have hρp : ρ + p = 1 := by dsimp [p]; ring
  rw [hρp]
  calc
    (T : ℂ) ^ (p / 2) * (p * Complex.Gamma p) *
          shortMobiusPolynomial T 1 * appendixCZeroQuotient ρ p =
        (T : ℂ) ^ (p / 2) * Complex.Gamma p *
          shortMobiusPolynomial T 1 * (p * appendixCZeroQuotient ρ p) := by ring
    _ = (T : ℂ) ^ (p / 2) * Complex.Gamma p * shortMobiusPolynomial T 1 := by
      rw [hQuotient, mul_one]

private theorem differentiableAt_shortMobiusPolynomial (T : ℝ) (s : ℂ) :
    DifferentiableAt ℂ (shortMobiusPolynomial T) s := by
  unfold shortMobiusPolynomial
  apply DifferentiableAt.fun_sum
  intro m _hm
  apply (differentiableAt_const (𝕜 := ℂ)
    ((ArithmeticFunction.moebius m : ℂ))).mul
  have hmZero : (m : ℂ) ≠ 0 := by
    have hmOne : 1 ≤ m := (Finset.mem_Ico.mp _hm).1
    exact_mod_cast (show m ≠ 0 by omega)
  exact differentiableAt_id.neg.const_cpow (Or.inl hmZero)

private theorem differentiableAt_appendixCShiftedRegularizedZeta (ρ s : ℂ) :
    DifferentiableAt ℂ (appendixCShiftedRegularizedZeta ρ) s := by
  unfold appendixCShiftedRegularizedZeta
  exact (differentiableAt_regularizedRiemannZeta (ρ + s)).comp s
    ((differentiableAt_const (𝕜 := ℂ) ρ).add differentiableAt_id)

private theorem differentiableAt_appendixCZeroQuotient (ρ s : ℂ) :
    DifferentiableAt ℂ (appendixCZeroQuotient ρ) s := by
  have hShift : DifferentiableOn ℂ (appendixCShiftedRegularizedZeta ρ) Set.univ :=
    fun z _hz => (differentiableAt_appendixCShiftedRegularizedZeta ρ z).differentiableWithinAt
  have hSlope : DifferentiableOn ℂ
      (dslope (appendixCShiftedRegularizedZeta ρ) 0) Set.univ :=
    (Complex.differentiableOn_dslope
      (Filter.univ_mem : Set.univ ∈ nhds (0 : ℂ))).2 hShift
  exact differentiableWithinAt_univ.mp (hSlope s (Set.mem_univ s))

/-- The pole-removed numerator is holomorphic throughout the open half-plane
`Re s > -1`, which contains every rectangle used to shift from `1/2` to
`1/2 - Re ρ` in the source range. -/
private theorem differentiableOn_appendixCContourNumerator {ρ : ℂ} {T : ℝ}
    (hT : 0 < T) :
    DifferentiableOn ℂ (appendixCContourNumerator ρ T)
      {s : ℂ | -(1 : ℝ) < s.re} := by
  intro s hs
  change -(1 : ℝ) < s.re at hs
  have hBase : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  have hPow : DifferentiableAt ℂ (fun z : ℂ => (T : ℂ) ^ (z / 2)) s :=
    differentiableAt_id.div_const 2 |>.const_cpow (Or.inl hBase)
  have hGammaNoPole : ∀ m : ℕ, s + 1 ≠ -m := by
    intro m hm
    have hRe := congrArg Complex.re hm
    have hmNonneg : (0 : ℝ) ≤ m := by positivity
    simp at hRe
    linarith
  have hGamma : DifferentiableAt ℂ (fun z : ℂ => Complex.Gamma (z + 1)) s :=
    (Complex.differentiableAt_Gamma (s + 1) hGammaNoPole).comp s
      (differentiableAt_id.add_const 1)
  have hMollifier : DifferentiableAt ℂ
      (fun z : ℂ => shortMobiusPolynomial T (ρ + z)) s :=
    (differentiableAt_shortMobiusPolynomial T (ρ + s)).comp s
      ((differentiableAt_const (𝕜 := ℂ) ρ).add differentiableAt_id)
  have hQuotient := differentiableAt_appendixCZeroQuotient ρ s
  exact (((hPow.mul hGamma).mul hMollifier).mul hQuotient).differentiableWithinAt

set_option maxHeartbeats 800000 in
/-- Finite-height rectangle shift.  The apparent pole at zero has already
been removed, so the rectangle crosses exactly the zeta pole `1 - ρ`. -/
private theorem appendixC_finite_rectangle_residue {ρ : ℂ} {T : ℝ}
    (hT : 2 ≤ T) (hRect : ρ ∈ ZeroRectangle (7 / 10) 1 T (2 * T))
    (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1 / 2 - ρ.re
    let R : ℝ := 3 * T
    RectangleIntegral'
      (fun s => appendixCContourNumerator ρ T s / (s - (1 - ρ)))
      ((a : ℂ) - (R : ℂ) * I) (((1 / 2 : ℝ) : ℂ) + (R : ℂ) * I) =
        appendixCContourResidue ρ T := by
  rw [mem_ZeroRectangle] at hRect
  rcases hRect with ⟨hβLower, hβUpper, hγLower, hγUpper⟩
  let a : ℝ := 1 / 2 - ρ.re
  let R : ℝ := 3 * T
  let z : ℂ := (a : ℂ) - (R : ℂ) * I
  let w : ℂ := ((1 / 2 : ℝ) : ℂ) + (R : ℂ) * I
  let p : ℂ := 1 - ρ
  let N : ℂ → ℂ := appendixCContourNumerator ρ T
  let f : ℂ → ℂ := fun s => N s / (s - p)
  let g : ℂ → ℂ := dslope N p
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hρOne : ρ ≠ 1 := by
    intro h
    have hIm := congrArg Complex.im h
    simp at hIm
    linarith
  have hzRe : z.re ≤ w.re := by simp [z, w, a]; linarith
  have hzIm : z.im ≤ w.im := by simp [z, w, R]; linarith
  have hpInterior : Rectangle z w ∈ nhds p := by
    rw [rectangle_mem_nhds_iff, Set.uIoo_of_le hzRe, Set.uIoo_of_le hzIm,
      mem_reProdIm, Set.mem_Ioo, Set.mem_Ioo]
    constructor
    · simp [p, z, w, a]
      constructor <;> linarith
    · simp [p, z, w, R]
      constructor <;> linarith
  have hRectSubset : Rectangle z w ⊆ {s : ℂ | -(1 : ℝ) < s.re} := by
    intro s hs
    have hsBounds := (mem_Rect hzRe hzIm s).mp hs
    change -(1 : ℝ) < s.re
    have haLower : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
    have hzReal : z.re = a := by simp [z]
    linarith [hsBounds.1]
  have hNdiff : DifferentiableOn ℂ N (Rectangle z w) := by
    exact (differentiableOn_appendixCContourNumerator hTpos).mono hRectSubset
  have hgHolo : HolomorphicOn g (Rectangle z w) := by
    exact (Complex.differentiableOn_dslope hpInterior).2 hNdiff
  have hNp : N p = appendixCContourResidue ρ T := by
    simpa [N, p] using appendixCContourNumerator_at_pole
      (T := T) hρOne hZero
  have hPrincipal : Set.EqOn
      (f - fun s => appendixCContourResidue ρ T / (s - p)) g
      (Rectangle z w \ {p}) := by
    intro s hs
    have hsp : s ≠ p := by simpa using hs.2
    have hSlope := sub_smul_dslope N p s
    change f s - appendixCContourResidue ρ T / (s - p) = g s
    rw [← hNp]
    dsimp [f, g]
    rw [← sub_div]
    rw [← hSlope]
    rw [smul_eq_mul, mul_div_cancel_left₀ _ (sub_ne_zero.mpr hsp)]
  have hResidue := ResidueTheoremOnRectangleWithSimplePole
    hzRe hzIm hpInterior hgHolo hPrincipal
  simpa [a, R, z, w, p, N, f, g] using hResidue

private theorem appendixC_inverse_scale_cpow {T : ℝ} (hT : 0 < T) (s : ℂ) :
    (((1 / T ^ (1 / 2 : ℝ) : ℝ) : ℂ) ^ (-s)) =
      (T : ℂ) ^ (s / 2) := by
  have hScale : 1 / T ^ (1 / 2 : ℝ) = T ^ (-(1 / 2 : ℝ)) := by
    rw [Real.rpow_neg hT.le]
    simp [one_div]
  rw [hScale]
  rw [← Complex.cpow_mul_ofReal_nonneg hT.le (-(1 / 2 : ℝ)) (-s)]
  congr 1
  push_cast
  ring

set_option maxHeartbeats 800000 in
/-- The right vertical side of the contour is exactly the infinite smoothed
detector. -/
private theorem appendixCDetectorValue_eq_rightContour {ρ : ℂ} {T : ℝ}
    (hT : 0 < T) (hρ : 7 / 10 ≤ ρ.re) :
    appendixCDetectorValue ρ T =
      (((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ u : ℝ, appendixCContourKernel ρ T
          (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) := by
  rw [appendixCDetectorValue_eq_mellinInv_rightLine hT hρ]
  rw [mellinInv, Complex.real_smul]
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with u
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I
  have hAbs : 1 < (ρ + s).re := by simp [s]; linarith
  have hProduct := riemannZeta_mul_zetaMollifier_eq_LSeries
    (appendixCMollifierCutoff T) hAbs
  have hScale := appendixC_inverse_scale_cpow hT s
  change (((1 / T ^ (1 / 2 : ℝ) : ℝ) : ℂ) ^ (-s)) *
      (Complex.Gamma s *
        LSeries (mollifiedZetaCoeff (appendixCMollifierCutoff T)) (ρ + s)) =
    appendixCContourKernel ρ T s
  rw [hScale, ← hProduct, ← shortMobiusPolynomial_eq_zetaMollifier]
  unfold appendixCContourKernel
  ring

/-- A coarse cutoff estimate used by all quantitative contour errors. -/
private theorem detectorCutoff_cast_le_three_mul {T : ℝ} (hT : 1 ≤ T) :
    (detectorCutoff T : ℝ) ≤ 3 * T := by
  have hTnonneg : 0 ≤ T := hT.trans' zero_le_one
  have hPow : T ^ (1 / 100 : ℝ) ≤ T := by
    have hExp : (1 / 100 : ℝ) ≤ 1 := by norm_num
    simpa using Real.rpow_le_rpow_of_exponent_le hT hExp
  have hFloor : (⌊2 * T ^ (1 / 100 : ℝ)⌋₊ : ℝ) ≤
      2 * T ^ (1 / 100 : ℝ) := by
    exact_mod_cast Nat.floor_le (by positivity : 0 ≤ 2 * T ^ (1 / 100 : ℝ))
  rw [detectorCutoff]
  push_cast
  linarith

/-- The short Möbius polynomial has the same cutoff bound everywhere to the
right of the critical line. -/
private theorem norm_shortMobiusPolynomial_le_cutoff {T : ℝ} {z : ℂ}
    (hz : 1 / 2 ≤ z.re) :
    ‖shortMobiusPolynomial T z‖ ≤ (detectorCutoff T : ℝ) := by
  unfold shortMobiusPolynomial
  calc
    ‖∑ m ∈ Finset.Ico 1 (detectorCutoff T),
        (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-z)‖
        ≤ ∑ _m ∈ Finset.Ico 1 (detectorCutoff T), (1 : ℝ) := by
      apply norm_sum_le_of_le
      intro m hm
      rw [norm_mul]
      have hMobius := norm_moebius_cast_le_one m
      have hmOne : 1 ≤ m := (Finset.mem_Ico.mp hm).1
      have hmPos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmOne)
      have hPow : ‖(m : ℂ) ^ (-z)‖ ≤ 1 := by
        rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_pos hmPos]
        apply Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hmOne)
        simp
        linarith
      nlinarith [norm_nonneg (ArithmeticFunction.moebius m : ℂ)]
    _ = ((Finset.Ico 1 (detectorCutoff T)).card : ℝ) := by simp
    _ ≤ (detectorCutoff T : ℝ) := by
      norm_cast
      simp [Nat.card_Ico]

set_option maxHeartbeats 800000 in
/-- Uniform pointwise bound on either horizontal side of the Appendix C
rectangle.  Six recurrences of Gamma overwhelm all deliberately coarse
polynomial bounds for zeta and the mollifier. -/
private theorem appendixCContourKernel_horizontal_norm_le {ρ : ℂ} {T x u : ℝ}
    (hT : 2 ≤ T) (hβUpper : ρ.re ≤ 1)
    (hγLower : T ≤ ρ.im) (hγUpper : ρ.im ≤ 2 * T)
    (hxLower : 1 / 2 - ρ.re ≤ x) (hxUpper : x ≤ 1 / 2)
    (hu : |u| = 3 * T) :
    ‖appendixCContourKernel ρ T ((x : ℂ) + (u : ℂ) * I)‖ ≤
      100 / T ^ 3 := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hTone : 1 ≤ T := by linarith
  let s : ℂ := (x : ℂ) + (u : ℂ) * I
  have hsRe : s.re = x := by simp [s]
  have hsIm : s.im = u := by simp [s]
  have hxWideLower : -(1 / 2 : ℝ) ≤ x := by linarith
  have hGamma := appendixC_Gamma_norm_le_inv_pow 6 (by norm_num)
    hxWideLower hxUpper (by rw [hu]; nlinarith)
  have hGamma' : ‖Complex.Gamma s‖ ≤ 720 / (3 * T) ^ 6 := by
    simpa [s, hu] using hGamma
  have hPowNorm : ‖(T : ℂ) ^ (s / 2)‖ = T ^ (x / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hTpos]
    congr 1
    simp [s]
  have hPow : T ^ (x / 2) ≤ T := by
    have hxExp : x / 2 ≤ 1 := by linarith
    simpa using Real.rpow_le_rpow_of_exponent_le hTone hxExp
  have hArgRe : 1 / 2 ≤ (ρ + s).re := by simp [s]; linarith
  have hMollifier := norm_shortMobiusPolynomial_le_cutoff (T := T) hArgRe
  have hMollifier' : ‖shortMobiusPolynomial T (ρ + s)‖ ≤ 3 * T :=
    hMollifier.trans (detectorCutoff_cast_le_three_mul hTone)
  have hRhoImAbs : |ρ.im| ≤ 2 * T := by
    rw [abs_of_nonneg (by linarith)]
    exact hγUpper
  have hArgImLower : 1 ≤ |(ρ + s).im| := by
    have hReverse : |u| - |ρ.im| ≤ |ρ.im + u| := by
      calc
        |u| - |ρ.im| ≤ abs (|u| - |ρ.im|) := le_abs_self _
        _ = abs (|u| - |-ρ.im|) := by simp
        _ ≤ |u - (-ρ.im)| := abs_abs_sub_abs_le_abs_sub _ _
        _ = |ρ.im + u| := by ring_nf
    have hTLower : T ≤ |ρ.im + u| := by rw [hu] at hReverse; linarith
    simp [s]
    linarith
  have hArgNorm : ‖ρ + s‖ ≤ 6 * T := by
    calc
      ‖ρ + s‖ ≤ |(ρ + s).re| + |(ρ + s).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ ≤ (3 / 2 : ℝ) + 5 * T := by
        have hReUpper : (ρ + s).re ≤ 3 / 2 := by simp [s]; linarith
        have hReNonneg : 0 ≤ (ρ + s).re := by linarith
        have hImUpper : |(ρ + s).im| ≤ 5 * T := by
          simp [s]
          exact (abs_add_le ρ.im u).trans (by rw [hu]; linarith)
        rw [abs_of_nonneg hReNonneg]
        linarith
      _ ≤ 6 * T := by linarith
  have hZeta := norm_riemannZeta_le_five_mul_norm
    (show (1 / 4 : ℝ) ≤ (ρ + s).re by linarith) hArgImLower
  have hZeta' : ‖riemannZeta (ρ + s)‖ ≤ 30 * T :=
    hZeta.trans (by nlinarith)
  unfold appendixCContourKernel
  rw [norm_mul, norm_mul, norm_mul, hPowNorm]
  calc
    T ^ (x / 2) * ‖Complex.Gamma s‖ *
          ‖shortMobiusPolynomial T (ρ + s)‖ * ‖riemannZeta (ρ + s)‖
        ≤ T * (720 / (3 * T) ^ 6) * (3 * T) * (30 * T) := by gcongr
    _ ≤ 100 / T ^ 3 := by
      field_simp
      nlinarith [sq_nonneg T, pow_pos hTpos 3, pow_pos hTpos 6]

private theorem appendixC_HIntegral_norm_le {ρ : ℂ} {T u : ℝ}
    (hT : 2 ≤ T) (hβLower : 7 / 10 ≤ ρ.re) (hβUpper : ρ.re ≤ 1)
    (hγLower : T ≤ ρ.im) (hγUpper : ρ.im ≤ 2 * T)
    (hu : |u| = 3 * T) :
    ‖HIntegral (appendixCContourKernel ρ T)
        (1 / 2 - ρ.re) (1 / 2) u‖ ≤ 100 / T ^ 3 := by
  have ha : 1 / 2 - ρ.re ≤ (1 / 2 : ℝ) := by linarith
  unfold HIntegral
  calc
    ‖∫ x in (1 / 2 - ρ.re)..(1 / 2),
        appendixCContourKernel ρ T ((x : ℂ) + (u : ℂ) * I)‖
        ≤ (100 / T ^ 3) * |(1 / 2 : ℝ) - (1 / 2 - ρ.re)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      have hxBounds : 1 / 2 - ρ.re ≤ x ∧ x ≤ (1 / 2 : ℝ) := by
        rw [Set.uIoc_of_le ha] at hx
        exact ⟨hx.1.le, hx.2⟩
      exact appendixCContourKernel_horizontal_norm_le hT hβUpper hγLower hγUpper
        hxBounds.1 hxBounds.2 hu
    _ ≤ 100 / T ^ 3 := by
      have hWidth : |(1 / 2 : ℝ) - (1 / 2 - ρ.re)| ≤ 1 := by
        rw [show (1 / 2 : ℝ) - (1 / 2 - ρ.re) = ρ.re by ring,
          abs_of_nonneg (by linarith)]
        exact hβUpper
      exact mul_le_of_le_one_right (by positivity) hWidth

private theorem appendixC_HIntegral'_norm_le {ρ : ℂ} {T u : ℝ}
    (hT : 2 ≤ T) (hβLower : 7 / 10 ≤ ρ.re) (hβUpper : ρ.re ≤ 1)
    (hγLower : T ≤ ρ.im) (hγUpper : ρ.im ≤ 2 * T)
    (hu : |u| = 3 * T) :
    ‖HIntegral' (appendixCContourKernel ρ T)
        (1 / 2 - ρ.re) (1 / 2) u‖ ≤ 100 / T ^ 3 := by
  have hBase := appendixC_HIntegral_norm_le hT hβLower hβUpper hγLower hγUpper hu
  unfold HIntegral'
  rw [norm_smul]
  have hScalar : ‖(1 / (2 * Real.pi * I) : ℂ)‖ ≤ 1 := by
    rw [norm_div, norm_one, norm_mul, norm_mul, Complex.norm_real, Complex.norm_I]
    norm_num
    rw [abs_of_pos Real.pi_pos]
    have hPi : (1 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hPiPos : 0 < Real.pi := Real.pi_pos
    rw [inv_mul_le_iff₀ hPiPos]
    nlinarith
  calc
    ‖(1 / (2 * Real.pi * I) : ℂ)‖ *
        ‖HIntegral (appendixCContourKernel ρ T)
          (1 / 2 - ρ.re) (1 / 2) u‖
        ≤ 1 * (100 / T ^ 3) :=
      mul_le_mul hScalar hBase (norm_nonneg _) (by norm_num)
    _ = 100 / T ^ 3 := one_mul _

set_option maxHeartbeats 800000 in
/-- On the boundary of the finite Appendix C rectangle, the pole-removed
quotient is the original contour kernel.  Both exceptional points lie
strictly inside the rectangle. -/
private theorem appendixC_finite_rectangle_kernel {ρ : ℂ} {T : ℝ}
    (hT : 2 ≤ T) (hRect : ρ ∈ ZeroRectangle (7 / 10) 1 T (2 * T))
    (hZero : riemannZeta ρ = 0) :
    let a : ℝ := 1 / 2 - ρ.re
    let R : ℝ := 3 * T
    RectangleIntegral' (appendixCContourKernel ρ T)
      ((a : ℂ) - (R : ℂ) * I) (((1 / 2 : ℝ) : ℂ) + (R : ℂ) * I) =
        appendixCContourResidue ρ T := by
  rw [mem_ZeroRectangle] at hRect
  rcases hRect with ⟨hβLower, hβUpper, hγLower, hγUpper⟩
  let a : ℝ := 1 / 2 - ρ.re
  let R : ℝ := 3 * T
  let z : ℂ := (a : ℂ) - (R : ℂ) * I
  let w : ℂ := ((1 / 2 : ℝ) : ℂ) + (R : ℂ) * I
  have hρOne : ρ ≠ 1 := by
    intro h
    have hIm := congrArg Complex.im h
    simp at hIm
    linarith
  have hFinite := appendixC_finite_rectangle_residue hT
    (show ρ ∈ ZeroRectangle (7 / 10) 1 T (2 * T) by
      rw [mem_ZeroRectangle]
      exact ⟨hβLower, hβUpper, hγLower, hγUpper⟩) hZero
  change RectangleIntegral' (appendixCContourKernel ρ T) z w =
    appendixCContourResidue ρ T
  rw [← hFinite]
  apply RectangleIntegral'_congr
  intro s hs
  have hsZero : s ≠ 0 := by
    intro hs0
    rw [hs0] at hs
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm,
      Set.mem_singleton_iff] at hs
    rcases hs with ((hBottom | hLeft) | hTop) | hRight
    · have : (0 : ℝ) = -R := by simpa [z, w] using hBottom.2
      dsimp [R] at this
      linarith
    · have : (0 : ℝ) = a := by simpa [z, w] using hLeft.1
      dsimp [a] at this
      linarith
    · have : (0 : ℝ) = R := by simpa [z, w] using hTop.2
      dsimp [R] at this
      linarith
    · have : (0 : ℝ) = 1 / 2 := by simpa [z, w] using hRight.1
      norm_num at this
  have hsPole : s ≠ 1 - ρ := by
    intro hsp
    rw [hsp] at hs
    simp only [RectangleBorder, Set.mem_union, Complex.mem_reProdIm,
      Set.mem_singleton_iff] at hs
    rcases hs with ((hBottom | hLeft) | hTop) | hRight
    · have : -ρ.im = -R := by simpa [z, w] using hBottom.2
      dsimp [R] at this
      linarith
    · have : 1 - ρ.re = a := by simpa [z, w] using hLeft.1
      dsimp [a] at this
      linarith
    · have : -ρ.im = R := by simpa [z, w] using hTop.2
      dsimp [R] at this
      linarith
    · have : 1 - ρ.re = 1 / 2 := by simpa [z, w] using hRight.1
      linarith
  exact (appendixCContourNumerator_div_eq_integrand hρOne hZero hsZero hsPole).symm

/-- A reusable quantitative tail estimate on a positive half-line. -/
private theorem norm_integral_Ioi_le_inv_pow_five
    (f : ℝ → ℂ) {C R : ℝ} (hR : 0 < R)
    (hPoint : ∀ u, R < u → ‖f u‖ ≤ C / u ^ 5) :
    ‖∫ u in Set.Ioi R, f u‖ ≤ C / (4 * R ^ 4) := by
  let g : ℝ → ℝ := fun u => C * u ^ (-(5 : ℝ))
  have hg : IntegrableOn g (Set.Ioi R) :=
    (integrableOn_Ioi_rpow_of_lt (a := -(5 : ℝ)) (by norm_num) hR).const_mul C
  calc
    ‖∫ u in Set.Ioi R, f u‖ ≤ ∫ u in Set.Ioi R, g u := by
      apply MeasureTheory.norm_integral_le_of_norm_le hg
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
      have huPos : 0 < u := hR.trans hu
      have h := hPoint u hu
      dsimp [g]
      rw [show u ^ (-(5 : ℝ)) = 1 / u ^ 5 by
        rw [Real.rpow_neg huPos.le]
        norm_num [one_div]]
      simpa [mul_div_assoc] using h
    _ = C / (4 * R ^ 4) := by
      dsimp [g]
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (a := -(5 : ℝ)) (by norm_num) hR]
      have hRne : R ≠ 0 := hR.ne'
      rw [show R ^ (-(5 : ℝ) + 1) = 1 / R ^ 4 by
        norm_num [Real.rpow_neg hR.le, one_div]]
      field_simp
      ring

set_option maxHeartbeats 800000 in
/-- Uniform inverse-fifth-power domination of the shifted (left) contour in
the two tails used by Appendix C. -/
private theorem appendixC_left_tail_pointwise {ρ : ℂ} {T u : ℝ}
    (hT : 2 ≤ T) (hβLower : 7 / 10 ≤ ρ.re) (hβUpper : ρ.re ≤ 1)
    (hγLower : T ≤ ρ.im) (hγUpper : ρ.im ≤ 2 * T)
    (hu : 3 * T ≤ |u|) :
    ‖typeIIContourIntegrand ρ T u‖ ≤ 51840 * T ^ 2 / |u| ^ 5 := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hTone : 1 ≤ T := by linarith
  let a : ℝ := 1 / 2 - ρ.re
  let s : ℂ := typeIIContourShift ρ u
  have haLower : -(1 / 2 : ℝ) ≤ a := by dsimp [a]; linarith
  have haUpper : a ≤ -(1 / 5 : ℝ) := by dsimp [a]; linarith
  have huOne : 1 ≤ |u| := by linarith
  have hGamma := appendixC_Gamma_norm_le_inv_pow 6 (by norm_num)
    haLower (by linarith : a ≤ 1 / 2) huOne
  have hGamma' : ‖Complex.Gamma s‖ ≤ 720 / |u| ^ 6 := by
    simpa [s, typeIIContourShift, a] using hGamma
  have hPowNorm : ‖(T : ℂ) ^ (s / 2)‖ = T ^ (a / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hTpos]
    congr 1
    simp [s, typeIIContourShift, a]
  have hPow : T ^ (a / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hTone (by linarith)
  have hCritical := rho_add_typeIIContourShift ρ u
  have hMollifier : ‖shortMobiusPolynomial T (ρ + s)‖ ≤ 3 * T := by
    rw [show ρ + s = (1 / 2 : ℂ) + ((ρ.im + u : ℝ) : ℂ) * I by
      simpa [s] using hCritical]
    exact (norm_shortMobiusPolynomial_criticalLine_le T (ρ.im + u)).trans
      (detectorCutoff_cast_le_three_mul hTone)
  have hZetaBase := norm_riemannZeta_shifted_criticalLine_le ρ.im u
  have hRhoWeight : 1 + |ρ.im| ≤ 3 * T := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  have huWeight : 1 + |u| ≤ 2 * |u| := by linarith
  have hZeta : ‖riemannZeta (ρ + s)‖ ≤ 24 * T * |u| := by
    rw [show ρ + s = (1 / 2 : ℂ) + ((ρ.im + u : ℝ) : ℂ) * I by
      simpa [s] using hCritical]
    calc
      ‖riemannZeta ((1 / 2 : ℂ) + ((ρ.im + u : ℝ) : ℂ) * I)‖
          ≤ (4 * (1 + |ρ.im|)) * (1 + |u|) := hZetaBase
      _ ≤ (4 * (3 * T)) * (2 * |u|) := by gcongr
      _ = 24 * T * |u| := by ring
  rw [typeIIContourIntegrand]
  change ‖(T : ℂ) ^ (s / 2) * Complex.Gamma s *
    shortMobiusPolynomial T (ρ + s) * riemannZeta (ρ + s)‖ ≤ _
  rw [norm_mul, norm_mul, norm_mul, hPowNorm]
  calc
    T ^ (a / 2) * ‖Complex.Gamma s‖ * ‖shortMobiusPolynomial T (ρ + s)‖ *
          ‖riemannZeta (ρ + s)‖
        ≤ 1 * (720 / |u| ^ 6) * (3 * T) * (24 * T * |u|) := by gcongr
    _ = 51840 * T ^ 2 / |u| ^ 5 := by
      have huNe : |u| ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one huOne)
      field_simp
      ring

set_option maxHeartbeats 800000 in
/-- Uniform inverse-fifth-power domination on the right Mellin line. -/
private theorem appendixC_right_tail_pointwise {ρ : ℂ} {T u : ℝ}
    (hT : 2 ≤ T) (hβLower : 7 / 10 ≤ ρ.re) (hu : 3 * T ≤ |u|) :
    ‖appendixCContourKernel ρ T
        (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
      (2160 * appendixCPSeries) * T ^ 2 / |u| ^ 5 := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hTone : 1 ≤ T := by linarith
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I
  have hsRe : s.re = 1 / 2 := by simp [s]
  have huOne : 1 ≤ |u| := by linarith
  have hGamma := appendixC_Gamma_norm_le_inv_pow 6 (by norm_num)
    (by norm_num : -(1 / 2 : ℝ) ≤ (1 / 2 : ℝ)) le_rfl huOne
  have hGamma' : ‖Complex.Gamma s‖ ≤ 720 / |u| ^ 6 := by
    simpa [s] using hGamma
  have hPowNorm : ‖(T : ℂ) ^ (s / 2)‖ = T ^ (1 / 4 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hTpos]
    congr 1
    simp [s]
    norm_num
  have hPow : T ^ (1 / 4 : ℝ) ≤ T := by
    simpa using Real.rpow_le_rpow_of_exponent_le hTone (by norm_num : (1 / 4 : ℝ) ≤ 1)
  have hAbs : 1 < (ρ + s).re := by simp [s]; linarith
  have hProduct := riemannZeta_mul_zetaMollifier_eq_LSeries
    (appendixCMollifierCutoff T) hAbs
  have hProductNorm :
      ‖shortMobiusPolynomial T (ρ + s) * riemannZeta (ρ + s)‖ ≤
        (3 * T) * appendixCPSeries := by
    rw [mul_comm, shortMobiusPolynomial_eq_zetaMollifier, hProduct]
    exact (norm_mollified_LSeries_le_cutoff_mul_pSeries hTpos.le
      (by simp [s]; linarith)).trans <|
        mul_le_mul_of_nonneg_right (detectorCutoff_cast_le_three_mul hTone)
          appendixCPSeries_nonneg
  unfold appendixCContourKernel
  change ‖(T : ℂ) ^ (s / 2) * Complex.Gamma s *
    shortMobiusPolynomial T (ρ + s) * riemannZeta (ρ + s)‖ ≤ _
  rw [show (T : ℂ) ^ (s / 2) * Complex.Gamma s *
      shortMobiusPolynomial T (ρ + s) * riemannZeta (ρ + s) =
      ((T : ℂ) ^ (s / 2) * Complex.Gamma s) *
        (shortMobiusPolynomial T (ρ + s) * riemannZeta (ρ + s)) by ring,
    norm_mul, norm_mul, hPowNorm]
  calc
    T ^ (1 / 4 : ℝ) * ‖Complex.Gamma s‖ *
          ‖shortMobiusPolynomial T (ρ + s) * riemannZeta (ρ + s)‖
        ≤ T * (720 / |u| ^ 6) * ((3 * T) * appendixCPSeries) := by gcongr
    _ ≤ (2160 * appendixCPSeries) * T ^ 2 / |u| ^ 5 := by
      have huPos : 0 < |u| := lt_of_lt_of_le zero_lt_one huOne
      have hP := appendixCPSeries_nonneg
      field_simp
      nlinarith

/-- The two omitted tails of the left contour have a uniform polynomial
bound. -/
private theorem appendixC_left_two_tails_norm_le {ρ : ℂ} {T : ℝ}
    (hT : 2 ≤ T) (hβLower : 7 / 10 ≤ ρ.re) (hβUpper : ρ.re ≤ 1)
    (hγLower : T ≤ ρ.im) (hγUpper : ρ.im ≤ 2 * T) :
    ‖(∫ u in Set.Iic (-(3 * T)), typeIIContourIntegrand ρ T u) +
        ∫ u in Set.Ioi (3 * T), typeIIContourIntegrand ρ T u‖ ≤
      (51840 * T ^ 2) / (2 * (3 * T) ^ 4) := by
  have hR : 0 < 3 * T := by positivity
  have hPos := norm_integral_Ioi_le_inv_pow_five
    (C := 51840 * T ^ 2) (fun u => typeIIContourIntegrand ρ T u) hR
      (fun u hu => by
        have huPos : 0 < u := hR.trans hu
        simpa [abs_of_pos huPos] using
          appendixC_left_tail_pointwise hT hβLower hβUpper hγLower hγUpper
            (u := u) (by simpa [abs_of_pos huPos] using hu.le))
  have hNeg := norm_integral_Ioi_le_inv_pow_five
    (C := 51840 * T ^ 2) (fun u => typeIIContourIntegrand ρ T (-u)) hR (fun u hu => by
      have huPos : 0 < u := hR.trans hu
      simpa [abs_of_pos huPos] using
        appendixC_left_tail_pointwise hT hβLower hβUpper hγLower hγUpper
          (u := -u) (by simpa [abs_of_pos huPos] using hu.le))
  simp only [integral_comp_neg_Ioi] at hNeg
  calc
    ‖(∫ u in Set.Iic (-(3 * T)), typeIIContourIntegrand ρ T u) +
          ∫ u in Set.Ioi (3 * T), typeIIContourIntegrand ρ T u‖
        ≤ ‖∫ u in Set.Iic (-(3 * T)), typeIIContourIntegrand ρ T u‖ +
            ‖∫ u in Set.Ioi (3 * T), typeIIContourIntegrand ρ T u‖ := norm_add_le _ _
    _ ≤ (51840 * T ^ 2) / (4 * (3 * T) ^ 4) +
          (51840 * T ^ 2) / (4 * (3 * T) ^ 4) := add_le_add hNeg hPos
    _ = (51840 * T ^ 2) / (2 * (3 * T) ^ 4) := by ring

/-- The two omitted tails of the right Mellin line satisfy the analogous
uniform bound. -/
private theorem appendixC_right_two_tails_norm_le {ρ : ℂ} {T : ℝ}
    (hT : 2 ≤ T) (hβLower : 7 / 10 ≤ ρ.re) :
    ‖(∫ u in Set.Iic (-(3 * T)), appendixCContourKernel ρ T
          (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) +
        ∫ u in Set.Ioi (3 * T), appendixCContourKernel ρ T
          (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)‖ ≤
      ((2160 * appendixCPSeries) * T ^ 2) / (2 * (3 * T) ^ 4) := by
  let f : ℝ → ℂ := fun u => appendixCContourKernel ρ T
    (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)
  have hR : 0 < 3 * T := by positivity
  have hPos := norm_integral_Ioi_le_inv_pow_five
    (C := (2160 * appendixCPSeries) * T ^ 2) f hR (fun u hu => by
    have huPos : 0 < u := hR.trans hu
    simpa [f, abs_of_pos huPos] using appendixC_right_tail_pointwise hT hβLower
      (u := u) (by simpa [abs_of_pos huPos] using hu.le))
  have hNeg := norm_integral_Ioi_le_inv_pow_five
    (C := (2160 * appendixCPSeries) * T ^ 2) (fun u => f (-u)) hR
    (fun u hu => by
      have huPos : 0 < u := hR.trans hu
      simpa [f, abs_of_pos huPos] using
        appendixC_right_tail_pointwise (ρ := ρ) hT hβLower
          (u := -u) (by simpa [abs_of_pos huPos] using hu.le))
  simp only [integral_comp_neg_Ioi] at hNeg
  calc
    ‖(∫ u in Set.Iic (-(3 * T)), f u) + ∫ u in Set.Ioi (3 * T), f u‖
        ≤ ‖∫ u in Set.Iic (-(3 * T)), f u‖ +
            ‖∫ u in Set.Ioi (3 * T), f u‖ := norm_add_le _ _
    _ ≤ ((2160 * appendixCPSeries) * T ^ 2) / (4 * (3 * T) ^ 4) +
          ((2160 * appendixCPSeries) * T ^ 2) / (4 * (3 * T) ^ 4) :=
      add_le_add hNeg hPos
    _ = ((2160 * appendixCPSeries) * T ^ 2) / (2 * (3 * T) ^ 4) := by ring

/-- The sole crossed residue is uniformly negligible in the dyadic zero
rectangle. -/
private theorem appendixC_residue_norm_le {ρ : ℂ} {T : ℝ}
    (hT : 2 ≤ T) (hβLower : 7 / 10 ≤ ρ.re) (hβUpper : ρ.re ≤ 1)
    (hγLower : T ≤ ρ.im) :
    ‖appendixCContourResidue ρ T‖ ≤ 2160 / T ^ 4 := by
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  have hTone : 1 ≤ T := by linarith
  have hPowNorm : ‖(T : ℂ) ^ ((1 - ρ) / 2)‖ = T ^ ((1 - ρ.re) / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hTpos]
    congr 1
    simp
  have hPow : T ^ ((1 - ρ.re) / 2) ≤ T := by
    simpa using Real.rpow_le_rpow_of_exponent_le hTone (by linarith : (1 - ρ.re) / 2 ≤ 1)
  have hGamma := appendixC_Gamma_norm_le_inv_pow 6 (by norm_num)
    (by simp only [sub_re, one_re]; linarith : -(1 / 2 : ℝ) ≤ (1 - ρ).re)
    (by simp only [sub_re, one_re]; linarith : (1 - ρ).re ≤ 1 / 2)
    (t := -ρ.im) (by
      rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ ρ.im)]
      linarith)
  have hGamma' : ‖Complex.Gamma (1 - ρ)‖ ≤ 720 / ρ.im ^ 6 := by
    have hArg : (((1 - ρ).re : ℝ) : ℂ) + ((-ρ.im : ℝ) : ℂ) * I = 1 - ρ := by
      apply Complex.ext <;> simp
    rw [hArg] at hGamma
    norm_num at hGamma ⊢
    simpa [abs_of_nonneg (by linarith : 0 ≤ ρ.im)] using hGamma
  have hMollifier : ‖shortMobiusPolynomial T 1‖ ≤ 3 * T :=
    (norm_shortMobiusPolynomial_le_cutoff (T := T) (z := 1) (by norm_num)).trans
      (detectorCutoff_cast_le_three_mul hTone)
  unfold appendixCContourResidue
  rw [norm_mul, norm_mul, hPowNorm]
  calc
    T ^ ((1 - ρ.re) / 2) * ‖Complex.Gamma (1 - ρ)‖ *
          ‖shortMobiusPolynomial T 1‖
        ≤ T * (720 / ρ.im ^ 6) * (3 * T) := by gcongr
    _ ≤ 2160 / T ^ 4 := by
      have hγPos : 0 < ρ.im := hTpos.trans_le hγLower
      have hPowMono : T ^ 6 ≤ ρ.im ^ 6 :=
        pow_le_pow_left₀ (by positivity) hγLower 6
      field_simp
      nlinarith [pow_pos hTpos 6, pow_pos hγPos 6]

set_option maxHeartbeats 800000 in
/-- The right contour kernel is a genuine whole-line Bochner-integrable
function, as required by the infinite rectangle identity. -/
private theorem integrable_appendixC_right_kernel {ρ : ℂ} {T : ℝ}
    (hT : 0 < T) (hβLower : 7 / 10 ≤ ρ.re) :
    Integrable (fun u : ℝ => appendixCContourKernel ρ T
      (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)) := by
  let line : ℝ → ℂ := fun u => ((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I
  let m : ℝ → ℂ := fun u => mellin (appendixCSmoothedDetector ρ T) (line u)
  have hm := verticalIntegrable_mellin_appendixCSmoothedDetector hT.le hβLower
  change Integrable m at hm
  have hPowCont : Continuous (fun u : ℝ => (T : ℂ) ^ (line u / 2)) := by
    apply continuous_const_cpow_of_ne_zero (T : ℂ) (by exact_mod_cast hT.ne')
    dsimp [line]
    fun_prop
  have hDom : Integrable (fun u : ℝ => T ^ (1 / 4 : ℝ) * ‖m u‖) :=
    hm.norm.const_mul (T ^ (1 / 4 : ℝ))
  have hProductInt : Integrable (fun u : ℝ => (T : ℂ) ^ (line u / 2) * m u) := by
    apply Integrable.mono' hDom
    · exact hPowCont.aestronglyMeasurable.mul hm.aestronglyMeasurable
    · filter_upwards with u
      have hPowNorm : ‖(T : ℂ) ^ (line u / 2)‖ = T ^ (1 / 4 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos hT]
        congr 1
        simp [line]
        norm_num
      rw [norm_mul, hPowNorm]
  apply hProductInt.congr
  filter_upwards with u
  · apply Eq.symm
    let s : ℂ := line u
    have hsPos : 0 < s.re := by simp [s, line]
    have hAbs : 1 < (ρ + s).re := by simp [s, line]; linarith
    have hMellin := mellin_appendixCSmoothedDetector_eq hT.le
      (by linarith : 0 ≤ ρ.re) hsPos hAbs
    have hProduct := riemannZeta_mul_zetaMollifier_eq_LSeries
      (appendixCMollifierCutoff T) hAbs
    have hKernel : appendixCContourKernel ρ T s = (T : ℂ) ^ (s / 2) * m u := by
      change appendixCContourKernel ρ T s = (T : ℂ) ^ (s / 2) *
        mellin (appendixCSmoothedDetector ρ T) s
      rw [hMellin]
      rw [← hProduct, ← shortMobiusPolynomial_eq_zetaMollifier]
      unfold appendixCContourKernel
      ring
    simpa [s, line] using hKernel

/-- The whole real-line integral split into its two tails and central
interval. -/
private theorem integral_eq_tails_add_interval (f : ℝ → ℂ) {a b : ℝ}
    (hf : Integrable f) :
    ∫ u : ℝ, f u =
      ((∫ u in Set.Iic a, f u) + ∫ u in Set.Ici b, f u) + ∫ u in a..b, f u := by
  rw [← intervalIntegral.integral_Iic_sub_Iic hf.restrict hf.restrict]
  have hWhole := intervalIntegral.integral_Iio_add_Ici (b := b) hf.restrict hf.restrict
  have hbEq : (∫ u in Set.Iic b, f u) = ∫ u in Set.Iio b, f u :=
    integral_Iic_eq_integral_Iio
  calc
    ∫ u : ℝ, f u = (∫ u in Set.Iio b, f u) + ∫ u in Set.Ici b, f u := hWhole.symm
    _ = ((∫ u in Set.Iic a, f u) + ∫ u in Set.Ici b, f u) +
          ((∫ u in Set.Iic b, f u) - ∫ u in Set.Iic a, f u) := by
      rw [hbEq]
      abel

/-- Expansion of the normalized rectangle integral into its two horizontal
and two vertical sides, with the vertical factors simplified to `1/(2π)`. -/
private theorem RectangleIntegral'_eq_edges (f : ℂ → ℂ) (a b R : ℝ) :
    RectangleIntegral' f ((a : ℂ) - (R : ℂ) * I) ((b : ℂ) + (R : ℂ) * I) =
      HIntegral' f a b (-R) - HIntegral' f a b R +
        (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ u in (-R)..R, f ((b : ℂ) + (u : ℂ) * I)) -
        (((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ u in (-R)..R, f ((a : ℂ) + (u : ℂ) * I)) := by
  unfold RectangleIntegral' RectangleIntegral HIntegral' HIntegral VIntegral
  simp [sub_re, sub_im, add_re, add_im, mul_re, mul_im, smul_eq_mul]
  field_simp [Real.pi_ne_zero]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Quantitative infinite contour shift.  All constants are deliberately
coarse; their only role is to make the eventual `1/3` detector threshold
fully explicit and uniform in the zero. -/
private theorem appendixC_contour_shift_error {ρ : ℂ} {T : ℝ}
    (hT : 2 ≤ T) (hRect : ρ ∈ ZeroRectangle (7 / 10) 1 T (2 * T))
    (hZero : riemannZeta ρ = 0) :
    ‖appendixCDetectorValue ρ T - typeIIContourIntegral ρ T‖ ≤
      200 / T ^ 3 + 2160 / T ^ 4 +
        (51840 * T ^ 2) / (4 * Real.pi * (3 * T) ^ 4) +
        ((2160 * appendixCPSeries) * T ^ 2) /
          (4 * Real.pi * (3 * T) ^ 4) := by
  rw [mem_ZeroRectangle] at hRect
  rcases hRect with ⟨hβLower, hβUpper, hγLower, hγUpper⟩
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) hT
  let a : ℝ := 1 / 2 - ρ.re
  let R : ℝ := 3 * T
  let f : ℂ → ℂ := appendixCContourKernel ρ T
  let right : ℝ → ℂ := fun u => f (((1 / 2 : ℝ) : ℂ) + (u : ℂ) * I)
  let left : ℝ → ℂ := fun u => f ((a : ℂ) + (u : ℂ) * I)
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hRect' : ρ ∈ ZeroRectangle (7 / 10) 1 T (2 * T) := by
    rw [mem_ZeroRectangle]
    exact ⟨hβLower, hβUpper, hγLower, hγUpper⟩
  have hRightInt : Integrable right := by
    simpa [right, f] using integrable_appendixC_right_kernel hTpos hβLower
  have hLeftEq (u : ℝ) : left u = typeIIContourIntegrand ρ T u := by
    unfold left f appendixCContourKernel typeIIContourIntegrand
    rfl
  have hLeftInt : Integrable left :=
    (integrable_typeIIContourIntegrand hTpos hβLower hβUpper).congr
      (Filter.Eventually.of_forall fun u => (hLeftEq u).symm)
  have hRightSplit := integral_eq_tails_add_interval right hRightInt
    (a := -R) (b := R)
  have hLeftSplit := integral_eq_tails_add_interval left hLeftInt
    (a := -R) (b := R)
  have hFinite := appendixC_finite_rectangle_kernel hT hRect' hZero
  dsimp only at hFinite
  rw [RectangleIntegral'_eq_edges] at hFinite
  have hRightExact := appendixCDetectorValue_eq_rightContour hTpos hβLower
  have hLeftExact : typeIIContourIntegral ρ T = c * ∫ u : ℝ, left u := by
    unfold typeIIContourIntegral c
    congr 1
  have hHorizontalBottom := appendixC_HIntegral'_norm_le hT hβLower hβUpper
    hγLower hγUpper (u := -R) (by simp [R]; positivity)
  have hHorizontalTop := appendixC_HIntegral'_norm_le hT hβLower hβUpper
    hγLower hγUpper (u := R) (by simp [R]; positivity)
  have hLeftTails := appendixC_left_two_tails_norm_le hT hβLower hβUpper
    hγLower hγUpper
  have hRightTails := appendixC_right_two_tails_norm_le hT hβLower
  have hResidue := appendixC_residue_norm_le hT hβLower hβUpper hγLower
  have hPiPos : 0 < Real.pi := Real.pi_pos
  have hCNorm : ‖c‖ = 1 / (2 * Real.pi) := by
    dsimp [c]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos]
    positivity
  rw [hRightExact, hLeftExact, hRightSplit, hLeftSplit]
  have hFinite' :
      HIntegral' f a (1 / 2) (-R) - HIntegral' f a (1 / 2) R +
          c * (∫ u in (-R)..R, right u) - c * (∫ u in (-R)..R, left u) =
        appendixCContourResidue ρ T := by
    simpa [f, a, R, c, right, left] using hFinite
  have hCentral : c * (∫ u in (-R)..R, right u) - c * (∫ u in (-R)..R, left u) =
      appendixCContourResidue ρ T - HIntegral' f a (1 / 2) (-R) +
        HIntegral' f a (1 / 2) R := by
    linear_combination hFinite'
  have hAlgebra :
      c * (((∫ u in Set.Iic (-R), right u) + ∫ u in Set.Ici R, right u) +
          ∫ u in (-R)..R, right u) -
        c * (((∫ u in Set.Iic (-R), left u) + ∫ u in Set.Ici R, left u) +
          ∫ u in (-R)..R, left u) =
      c * (((∫ u in Set.Iic (-R), right u) + ∫ u in Set.Ici R, right u) -
        ((∫ u in Set.Iic (-R), left u) + ∫ u in Set.Ici R, left u)) +
      (appendixCContourResidue ρ T -
        HIntegral' f a (1 / 2) (-R) + HIntegral' f a (1 / 2) R) := by
    linear_combination hCentral
  rw [hAlgebra]
  calc
    ‖c * (((∫ u in Set.Iic (-R), right u) + ∫ u in Set.Ici R, right u) -
          ((∫ u in Set.Iic (-R), left u) + ∫ u in Set.Ici R, left u)) +
        (appendixCContourResidue ρ T - HIntegral' f a (1 / 2) (-R) +
          HIntegral' f a (1 / 2) R)‖
      ≤ ‖c‖ * (‖(∫ u in Set.Iic (-R), right u) + ∫ u in Set.Ici R, right u‖ +
          ‖(∫ u in Set.Iic (-R), left u) + ∫ u in Set.Ici R, left u‖) +
        (‖appendixCContourResidue ρ T‖ + ‖HIntegral' f a (1 / 2) (-R)‖ +
          ‖HIntegral' f a (1 / 2) R‖) := by
        calc
          _ ≤ ‖c * (((∫ u in Set.Iic (-R), right u) + ∫ u in Set.Ici R, right u) -
                ((∫ u in Set.Iic (-R), left u) + ∫ u in Set.Ici R, left u))‖ +
              ‖appendixCContourResidue ρ T - HIntegral' f a (1 / 2) (-R) +
                HIntegral' f a (1 / 2) R‖ := norm_add_le _ _
          _ ≤ ‖c‖ * (‖(∫ u in Set.Iic (-R), right u) + ∫ u in Set.Ici R, right u‖ +
                ‖(∫ u in Set.Iic (-R), left u) + ∫ u in Set.Ici R, left u‖) +
              (‖appendixCContourResidue ρ T‖ + ‖HIntegral' f a (1 / 2) (-R)‖ +
                ‖HIntegral' f a (1 / 2) R‖) := by
            gcongr
            · rw [norm_mul]
              exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg c)
            · calc
                ‖appendixCContourResidue ρ T - HIntegral' f a (1 / 2) (-R) +
                    HIntegral' f a (1 / 2) R‖
                    ≤ ‖appendixCContourResidue ρ T - HIntegral' f a (1 / 2) (-R)‖ +
                      ‖HIntegral' f a (1 / 2) R‖ := norm_add_le _ _
                _ ≤ (‖appendixCContourResidue ρ T‖ +
                      ‖HIntegral' f a (1 / 2) (-R)‖) +
                      ‖HIntegral' f a (1 / 2) R‖ :=
                    add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ (1 / (2 * Real.pi)) *
          (((2160 * appendixCPSeries) * T ^ 2) / (2 * (3 * T) ^ 4) +
            (51840 * T ^ 2) / (2 * (3 * T) ^ 4)) +
          (2160 / T ^ 4 + 100 / T ^ 3 + 100 / T ^ 3) := by
      rw [hCNorm]
      gcongr
      · simpa [right, f, R, integral_Ici_eq_integral_Ioi] using hRightTails
      · simpa [left, R, integral_Ici_eq_integral_Ioi, hLeftEq] using hLeftTails
    _ = 200 / T ^ 3 + 2160 / T ^ 4 +
        (51840 * T ^ 2) / (4 * Real.pi * (3 * T) ^ 4) +
        ((2160 * appendixCPSeries) * T ^ 2) /
          (4 * Real.pi * (3 * T) ^ 4) := by ring

/-- Below the real Möbius cutoff, the truncated divisor set is the full
positive-divisor set. -/
theorem detectorDivisors_eq_divisors_of_le {n : ℕ} {T : ℝ}
    (hn : 0 < n) (hnCut : (n : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)) :
    detectorDivisors n T = n.divisors := by
  unfold detectorDivisors
  apply Finset.filter_eq_self.mpr
  intro d hd
  have hdNat : d ≤ n := Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hd)
  exact (by exact_mod_cast hdNat : (d : ℝ) ≤ n) |>.trans hnCut

/-- Möbius inversion identifies the unsmoothed detector coefficient with the
Dirichlet identity throughout the cancelled initial range. -/
theorem mobius_sum_eq_ite_of_le {n : ℕ} {T : ℝ}
    (hn : 0 < n) (hnCut : (n : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ)) :
    mobius_sum n T = if n = 1 then 1 else 0 := by
  rw [mobius_sum, detectorDivisors_eq_divisors_of_le hn hnCut]
  calc
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ) =
        ((ArithmeticFunction.moebius : ArithmeticFunction ℂ) *
          ArithmeticFunction.zeta) n := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
      simp only [ArithmeticFunction.intCoe_apply]
    _ = (1 : ArithmeticFunction ℂ) n := by
      rw [ArithmeticFunction.coe_moebius_mul_coe_zeta]
    _ = if n = 1 then 1 else 0 := ArithmeticFunction.one_apply

/-- The natural cutoff was deliberately defined as one past the floor of the
source's real cutoff, so membership below it is exactly the range in which
Möbius cancellation is valid. -/
theorem mobius_sum_eq_ite_of_lt_detectorCutoff {n : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (hn : 0 < n) (hnCut : n < detectorCutoff T) :
    mobius_sum n T = if n = 1 then 1 else 0 := by
  have hCutNonneg : 0 ≤ 2 * T ^ (1 / 100 : ℝ) := by positivity
  have hnFloor : n ≤ ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ := by
    rw [detectorCutoff] at hnCut
    omega
  exact mobius_sum_eq_ite_of_le hn
    ((Nat.le_floor_iff hCutNonneg).mp hnFloor)

/-- The constant coefficient in the smoothed detector is exactly the expected
`exp (-1/Y)` contribution. -/
theorem detectorCoeff_one (T : ℝ) (hT : 1 ≤ T) :
    detectorCoeff 1 T = Real.exp (-(1 : ℝ) / T ^ (1 / 2 : ℝ)) := by
  have hCut : 1 < detectorCutoff T := by
    rw [detectorCutoff]
    have hTwo : (2 : ℝ) ≤ 2 * T ^ (1 / 100 : ℝ) := by
      have hPow : 1 ≤ T ^ (1 / 100 : ℝ) := Real.one_le_rpow hT (by norm_num)
      nlinarith
    have hFloor : 2 ≤ ⌊2 * T ^ (1 / 100 : ℝ)⌋₊ :=
      (Nat.le_floor_iff (by positivity)).mpr hTwo
    omega
  rw [detectorCoeff, mobius_sum_eq_ite_of_lt_detectorCutoff
    (zero_le_one.trans hT) (by norm_num) hCut]
  norm_num

/-- All nonconstant coefficients before the Möbius cutoff vanish exactly. -/
theorem detectorCoeff_eq_zero_of_lt_cutoff {n : ℕ} {T : ℝ}
    (hT : 0 ≤ T) (hn : 2 ≤ n) (hnCut : n < detectorCutoff T) :
    detectorCoeff n T = 0 := by
  rw [detectorCoeff,
    mobius_sum_eq_ite_of_lt_detectorCutoff hT (by omega) hnCut,
    if_neg (by omega), zero_mul]

/-- Coefficients after separating the real and imaginary parts of the zero. -/
private noncomputable def appendixCLineCoeff (ρ : ℂ) (T : ℝ) (n : ℕ) : ℂ :=
  detectorCoeff n T * (n : ℂ) ^ (-(ρ.re : ℂ))

/-- An ordinary dyadic Dirichlet block with the separated coefficients is
exactly the detector block evaluated at `ρ`. -/
private theorem dirichletPoly_appendixCLineCoeff_eq_detectPoly
    (ρ : ℂ) (T : ℝ) (N : ℕ) :
    dirichletPoly N (appendixCLineCoeff ρ T) ρ.im = detectPoly N ρ T := by
  unfold dirichletPoly dyadicInterval appendixCLineCoeff detectPoly
  apply Finset.sum_congr rfl
  intro n hn
  have hnPos : 0 < n := by
    have := (Finset.mem_Ioc.mp hn).1
    omega
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
  rw [mul_assoc, ← Complex.cpow_add _ _ hnNe]
  congr 2
  apply Complex.ext <;> simp

/-- Every exponent below the exact search bound has scale at most the
detector upper endpoint. -/
private theorem dyadic_scale_le_upper_of_lt_count {T : ℝ} {j : ℕ}
    (hUpperOne : 1 ≤ detectorScaleUpper T) (hj : j < dyadicScaleIndexCount T) :
    (2 : ℝ) ^ j ≤ detectorScaleUpper T := by
  rw [dyadicScaleIndexCount] at hj
  have hjFloor : j ≤ ⌊Real.logb 2 (detectorScaleUpper T)⌋₊ := by omega
  have hjCast : (j : ℝ) ≤ ⌊Real.logb 2 (detectorScaleUpper T)⌋₊ := by
    exact_mod_cast hjFloor
  have hjLog : (j : ℝ) ≤ Real.logb 2 (detectorScaleUpper T) :=
    hjCast.trans (Nat.floor_le (by
      rw [Real.logb]
      exact div_nonneg (Real.log_nonneg hUpperOne) (Real.log_nonneg (by norm_num))))
  rw [Real.le_logb_iff_rpow_le (by norm_num) (lt_of_lt_of_le zero_lt_one hUpperOne),
    Real.rpow_natCast] at hjLog
  exact hjLog

/-- A non-admissible block inside the exact search range lies wholly below
the Möbius-cancellation cutoff and therefore vanishes. -/
private theorem detectPoly_eq_zero_of_lt_count_not_admissible {ρ : ℂ} {T : ℝ} {j : ℕ}
    (hT : 1 ≤ T) (hUpperOne : 1 ≤ detectorScaleUpper T)
    (hj : j < dyadicScaleIndexCount T) (hNot : ¬ IsAdmissibleDyadicScale T j) :
    detectPoly (2 ^ j) ρ T = 0 := by
  have hUpper := dyadic_scale_le_upper_of_lt_count hUpperOne hj
  have hLow : (2 : ℝ) ^ j < T ^ (1 / 100 : ℝ) := by
    by_contra h
    exact hNot ⟨le_of_not_gt h, hUpper⟩
  unfold detectPoly
  apply Finset.sum_eq_zero
  intro n hn
  have hnBounds := Finset.mem_Ioc.mp hn
  have hnTwo : 2 ≤ n := by
    have : 1 ≤ 2 ^ j := pow_pos (by omega : 0 < 2) j
    omega
  have hnReal : (n : ℝ) < 2 * T ^ (1 / 100 : ℝ) := by
    calc
      (n : ℝ) ≤ (2 * 2 ^ j : ℕ) := by exact_mod_cast hnBounds.2
      _ = 2 * (2 : ℝ) ^ j := by norm_num
      _ < 2 * T ^ (1 / 100 : ℝ) := by nlinarith
  have hnCut : n < detectorCutoff T := by
    rw [detectorCutoff]
    exact Nat.lt_succ_iff.mpr <| Nat.le_floor hnReal.le
  rw [detectorCoeff_eq_zero_of_lt_cutoff (zero_le_one.trans hT) hnTwo hnCut, zero_mul]

/-- Failure of the Type-I predicate bounds the entire finite dyadic body by
the sum of the source thresholds; blocks below the admissible range vanish
exactly by Möbius inversion. -/
private theorem norm_wideDirichletPoly_appendixC_le {ρ : ℂ} {T : ℝ}
    (hT : 1 ≤ T) (hLog : 0 < Real.log T)
    (hUpperOne : 1 ≤ detectorScaleUpper T) (hNotTypeI : ¬ IsTypeIZero ρ T) :
    ‖wideDirichletPoly 1 (dyadicScaleIndexCount T) (appendixCLineCoeff ρ T) ρ.im‖ ≤
      (dyadicScaleIndexCount T : ℝ) / (3 * Real.log T) := by
  rw [wideDirichletPoly_eq_sum_blocks]
  calc
    ‖∑ r ∈ Finset.range (dyadicScaleIndexCount T),
        dirichletPoly (2 ^ r * 1) (appendixCLineCoeff ρ T) ρ.im‖
        ≤ ∑ r ∈ Finset.range (dyadicScaleIndexCount T),
            ‖dirichletPoly (2 ^ r * 1) (appendixCLineCoeff ρ T) ρ.im‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r ∈ Finset.range (dyadicScaleIndexCount T),
          (1 / (3 * Real.log T) : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hrLt := Finset.mem_range.mp hr
      rw [mul_one, dirichletPoly_appendixCLineCoeff_eq_detectPoly]
      by_cases hAdm : IsAdmissibleDyadicScale T r
      · have hMem : r ∈ admissibleDyadicIndices T :=
          (mem_admissibleDyadicIndices T r).mpr hAdm
        have hNotLarge : ¬ 1 / (3 * Real.log T) ≤ ‖detectPoly (2 ^ r) ρ T‖ := by
          intro hLarge
          exact hNotTypeI ⟨r, hMem, hLarge⟩
        exact (lt_of_not_ge hNotLarge).le
      · rw [detectPoly_eq_zero_of_lt_count_not_admissible hT hUpperOne hrLt hAdm,
          norm_zero]
        positivity
    _ = (dyadicScaleIndexCount T : ℝ) / (3 * Real.log T) := by
      simp [div_eq_mul_inv]

/-- The exact number of dyadic blocks is eventually at most `log T`; this is
the quantitative pigeonhole constant required by the source's `1/(3 log T)`
threshold. -/
private theorem eventually_dyadicScaleIndexCount_le_log :
    ∀ᶠ T : ℝ in Filter.atTop,
      (dyadicScaleIndexCount T : ℝ) ≤ Real.log T := by
  have hLittle := isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 20)
  filter_upwards [hLittle.eventuallyLE,
    Filter.eventually_ge_atTop (Real.exp 5)] with T hLogSmall hT
  have hTpos : 0 < T := (Real.exp_pos 5).trans_le hT
  have hTone : 1 ≤ T := by
    have : (1 : ℝ) ≤ Real.exp 5 := by rw [← Real.exp_zero]; exact Real.exp_le_exp.mpr (by norm_num)
    exact this.trans hT
  have hLog : 5 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 5) hT
  have hLogNonneg : 0 ≤ Real.log T := by linarith
  have hLogSq : (Real.log T) ^ (2 : ℕ) ≤ T ^ (1 / 20 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLogNonneg _),
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hTpos.le _)] at hLogSmall
    simpa [Real.rpow_natCast] using hLogSmall
  have hScale : detectorScaleUpper T ≤ T ^ (11 / 20 : ℝ) := by
    calc
      detectorScaleUpper T = T ^ (1 / 2 : ℝ) * (Real.log T) ^ 2 := rfl
      _ ≤ T ^ (1 / 2 : ℝ) * T ^ (1 / 20 : ℝ) := by gcongr
      _ = T ^ (11 / 20 : ℝ) := by
        rw [← Real.rpow_add hTpos]
        norm_num
  have hUpperOne : 1 ≤ detectorScaleUpper T := by
    unfold detectorScaleUpper
    have hPowOne : 1 ≤ T ^ (1 / 2 : ℝ) := Real.one_le_rpow hTone (by norm_num)
    have hLogSqOne : 1 ≤ (Real.log T) ^ 2 := by nlinarith
    nlinarith
  have hLogb : Real.logb 2 (detectorScaleUpper T) ≤
      (11 / 20 : ℝ) * Real.logb 2 T := by
    calc
      Real.logb 2 (detectorScaleUpper T) ≤ Real.logb 2 (T ^ (11 / 20 : ℝ)) :=
        Real.logb_le_logb_of_le (by norm_num) (lt_of_lt_of_le zero_lt_one hUpperOne) hScale
      _ = (11 / 20 : ℝ) * Real.logb 2 T := by
        rw [Real.logb_rpow_eq_mul_logb_of_pos hTpos]
  have hCount : (dyadicScaleIndexCount T : ℝ) ≤
      Real.logb 2 (detectorScaleUpper T) + 1 := by
    have hLogbNonneg : 0 ≤ Real.logb 2 (detectorScaleUpper T) := by
      rw [Real.logb]
      exact div_nonneg (Real.log_nonneg hUpperOne) (Real.log_nonneg (by norm_num))
    rw [dyadicScaleIndexCount]
    push_cast
    simpa [add_comm] using add_le_add_right (Nat.floor_le hLogbNonneg) 1
  have hLogTwo : (69 / 100 : ℝ) < Real.log 2 :=
    (by norm_num : (69 / 100 : ℝ) < 0.6931471803) |>.trans Real.log_two_gt_d9
  have hCoeff : (11 / 20 : ℝ) / Real.log 2 < 4 / 5 := by
    rw [div_lt_iff₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 69 / 100) hLogTwo.le)]
    nlinarith
  calc
    (dyadicScaleIndexCount T : ℝ)
        ≤ Real.logb 2 (detectorScaleUpper T) + 1 := hCount
    _ ≤ (11 / 20 : ℝ) * Real.logb 2 T + 1 := by linarith
    _ = ((11 / 20 : ℝ) / Real.log 2) * Real.log T + 1 := by
      rw [Real.logb]
      ring
    _ ≤ (4 / 5 : ℝ) * Real.log T + 1 := by
      gcongr
    _ ≤ Real.log T := by linarith

private noncomputable def appendixCDetectorTail (ρ : ℂ) (T : ℝ) : ℂ :=
  let K := 2 ^ dyadicScaleIndexCount T
  ∑' n : ℕ, detectorCoeff (n + K + 1) T * ((n + K + 1 : ℕ) : ℂ) ^ (-ρ)

private theorem summable_appendixC_detector_terms {ρ : ℂ} {T : ℝ}
    (hT : 0 < T) (hβ : 0 ≤ ρ.re) :
    Summable (fun n : ℕ => detectorCoeff n T * (n : ℂ) ^ (-ρ)) := by
  have h := summable_appendixCSmoothedDetector hT.le
    (show 0 < 1 / T ^ (1 / 2 : ℝ) by positivity) hβ
  apply h.congr
  intro n
  have hArg : -(((n : ℝ) : ℂ) *
      ((1 / T ^ (1 / 2 : ℝ) : ℝ) : ℂ)) =
      (((-((n : ℝ) / T ^ (1 / 2 : ℝ))) : ℝ) : ℂ) := by
    push_cast
    simp [div_eq_mul_inv]
  rw [hArg]
  exact appendixC_smoothed_term_eq_detector_term hT n

/-- Exact decomposition of the infinite detector into its constant term,
the complete finite dyadic body, and the shifted exponential tail. -/
private theorem appendixCDetectorValue_eq_one_add_wide_add_tail {ρ : ℂ} {T : ℝ}
    (hT : 0 < T) (hβ : 0 ≤ ρ.re) :
    appendixCDetectorValue ρ T = detectorCoeff 1 T * (1 : ℂ) ^ (-ρ) +
      wideDirichletPoly 1 (dyadicScaleIndexCount T) (appendixCLineCoeff ρ T) ρ.im +
      appendixCDetectorTail ρ T := by
  let d : ℕ → ℂ := fun n => detectorCoeff n T * (n : ℂ) ^ (-ρ)
  let k := dyadicScaleIndexCount T
  let K := 2 ^ k
  have hSum : Summable d := summable_appendixC_detector_terms hT hβ
  have hSplit := hSum.sum_add_tsum_nat_add (K + 1)
  have hFinite : ∑ n ∈ Finset.range (K + 1), d n =
      d 1 + wideDirichletPoly 1 k (appendixCLineCoeff ρ T) ρ.im := by
    have hK : 1 ≤ K := pow_pos (by omega : 0 < 2) k
    rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < K + 1)]
    have hdZero : d 0 = 0 := by
      simp [d, detectorCoeff, mobius_sum, detectorDivisors]
    rw [hdZero, zero_add]
    have hSet : Finset.Ico 1 (K + 1) = {1} ∪ Finset.Ioc 1 K := by
      ext n
      simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton,
        Finset.mem_Ioc]
      omega
    rw [hSet, Finset.sum_union]
    · simp only [Finset.sum_singleton]
      congr 1
      unfold wideDirichletPoly
      apply Finset.sum_congr
      · ext n
        simp only [mul_one, Finset.mem_Ioc, K]
      · intro n hn
        have hnPos : 0 < n := by
          have := (Finset.mem_Ioc.mp hn).1
          omega
        have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hnPos.ne'
        dsimp [d, appendixCLineCoeff]
        rw [mul_assoc, ← Complex.cpow_add _ _ hnNe]
        congr 2
        apply Complex.ext <;> simp
    · exact Finset.disjoint_left.mpr (by simp)
  unfold appendixCDetectorValue appendixCDetectorTail
  dsimp [K, k] at hSplit hFinite ⊢
  rw [← hSplit, hFinite]
  dsimp only [d]
  simp only [Nat.cast_one]
  congr 1

/-- The chosen dyadic endpoint is strictly beyond the full detector range. -/
private theorem detectorScaleUpper_lt_finalDyadicScale {T : ℝ}
    (hUpper : 0 < detectorScaleUpper T) :
    detectorScaleUpper T < (2 : ℝ) ^ dyadicScaleIndexCount T := by
  have hLog := Nat.lt_floor_add_one (Real.logb 2 (detectorScaleUpper T))
  rw [Real.logb_lt_iff_lt_rpow (by norm_num) hUpper] at hLog
  rw [← Real.rpow_natCast]
  simpa [dyadicScaleIndexCount, Nat.cast_add, Nat.cast_one] using hLog

/-- A quantitative lower bound for the denominator of the geometric tail. -/
private theorem half_inv_le_one_sub_exp_neg_inv {Y : ℝ} (hY : 2 ≤ Y) :
    (2 * Y)⁻¹ ≤ 1 - Real.exp (-(1 / Y)) := by
  have hYpos : 0 < Y := by positivity
  let x := 1 / Y
  have hxPos : 0 < x := by dsimp [x]; positivity
  have hxHalf : x ≤ 1 / 2 := by
    dsimp [x]
    exact (div_le_iff₀ hYpos).2 (by nlinarith)
  have hxNorm : ‖-x‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_neg, abs_of_pos hxPos]
    linarith
  have hRem := Real.norm_exp_sub_one_sub_id_le hxNorm
  have hUpper : Real.exp (-x) - 1 + x ≤ x ^ 2 := by
    have := (le_abs_self (Real.exp (-x) - 1 - (-x))).trans hRem
    simpa only [sub_neg_eq_add, Real.norm_eq_abs, abs_neg, abs_of_pos hxPos] using this
  have hMain : x / 2 ≤ 1 - Real.exp (-x) := by
    nlinarith [sq_nonneg (x - 1 / 2)]
  have hEq : (2 * Y)⁻¹ = x / 2 := by
    dsimp [x]
    field_simp
  rw [hEq]
  simpa [x] using hMain

/-- Uniform pointwise majorant for the shifted detector tail. -/
private theorem norm_appendixCDetectorTail_term_le {ρ : ℂ} {T : ℝ}
    (hT : 1 ≤ T) (hβ : 0 ≤ ρ.re) (n : ℕ) :
    ‖detectorCoeff (n + 2 ^ dyadicScaleIndexCount T + 1) T *
        ((n + 2 ^ dyadicScaleIndexCount T + 1 : ℕ) : ℂ) ^ (-ρ)‖ ≤
      (detectorCutoff T : ℝ) *
        Real.exp (-((n + 2 ^ dyadicScaleIndexCount T + 1 : ℕ) : ℝ) /
          T ^ (1 / 2 : ℝ)) := by
  let m := n + 2 ^ dyadicScaleIndexCount T + 1
  have hmPos : 0 < m := by
    have hPow : 0 < 2 ^ dyadicScaleIndexCount T := pow_pos (by omega) _
    dsimp [m]
    omega
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hmPos
  have hPow : ‖(m : ℂ) ^ (-ρ)‖ ≤ 1 := by
    rw [Complex.norm_natCast_cpow_of_pos hmPos]
    have hOne : 1 ≤ (m : ℝ) ^ ρ.re := Real.one_le_rpow hmOne hβ
    rw [show (-ρ).re = -ρ.re by simp, Real.rpow_neg (by positivity)]
    exact inv_le_one_of_one_le₀ hOne
  rw [show n + 2 ^ dyadicScaleIndexCount T + 1 = m by rfl,
    detectorCoeff_eq_mollifiedZetaCoeff T m (zero_le_one.trans hT), norm_mul,
    norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  calc
    ‖mollifiedZetaCoeff (appendixCMollifierCutoff T) m‖ *
          Real.exp (-(m : ℝ) / T ^ (1 / 2 : ℝ)) * ‖(m : ℂ) ^ (-ρ)‖
        ≤ ‖mollifiedZetaCoeff (appendixCMollifierCutoff T) m‖ *
          Real.exp (-(m : ℝ) / T ^ (1 / 2 : ℝ)) * 1 := by gcongr
    _ ≤ (detectorCutoff T : ℝ) *
          Real.exp (-(m : ℝ) / T ^ (1 / 2 : ℝ)) := by
      simpa using mul_le_mul_of_nonneg_right
        (norm_mollifiedZetaCoeff_le_detectorCutoff T m (zero_le_one.trans hT))
        (Real.exp_pos _).le
    _ = _ := by rfl

/-- The shifted detector tail is bounded by an explicit geometric series. -/
private theorem norm_appendixCDetectorTail_le_geometric {ρ : ℂ} {T : ℝ}
    (hT : 1 ≤ T) (hβ : 0 ≤ ρ.re) :
    ‖appendixCDetectorTail ρ T‖ ≤
      (detectorCutoff T : ℝ) *
        Real.exp (-((2 ^ dyadicScaleIndexCount T : ℕ) : ℝ) /
          T ^ (1 / 2 : ℝ)) *
        (1 - Real.exp (-(1 / T ^ (1 / 2 : ℝ))))⁻¹ := by
  let Y := T ^ (1 / 2 : ℝ)
  let K := 2 ^ dyadicScaleIndexCount T
  let r := Real.exp (-(1 / Y))
  have hYpos : 0 < Y := by dsimp [Y]; positivity
  have hrNonneg : 0 ≤ r := by dsimp [r]; positivity
  have hrLt : r < 1 := by
    dsimp [r]
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hYpos)
  have hGeom : Summable (fun n : ℕ => r ^ n) :=
    summable_geometric_of_lt_one hrNonneg hrLt
  let major : ℕ → ℝ := fun n =>
    (detectorCutoff T : ℝ) * Real.exp (-(K : ℝ) / Y) * r ^ n
  have hMajor : Summable major := by
    simpa [major] using hGeom.mul_left
      ((detectorCutoff T : ℝ) * Real.exp (-(K : ℝ) / Y))
  have hPoint (n : ℕ) :
      ‖detectorCoeff (n + K + 1) T * ((n + K + 1 : ℕ) : ℂ) ^ (-ρ)‖ ≤ major n := by
    calc
      ‖detectorCoeff (n + K + 1) T * ((n + K + 1 : ℕ) : ℂ) ^ (-ρ)‖
          ≤ (detectorCutoff T : ℝ) *
              Real.exp (-((n + K + 1 : ℕ) : ℝ) / Y) := by
            simpa [K, Y] using norm_appendixCDetectorTail_term_le hT hβ n
      _ ≤ major n := by
        dsimp [major, r]
        calc
          (detectorCutoff T : ℝ) * Real.exp (-((n + K + 1 : ℕ) : ℝ) / Y)
              ≤ (detectorCutoff T : ℝ) *
                  (Real.exp (-(K : ℝ) / Y) * Real.exp (-(1 / Y)) ^ n) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                rw [← Real.exp_nat_mul, ← Real.exp_add]
                apply Real.exp_le_exp.mpr
                have hYne : Y ≠ 0 := hYpos.ne'
                push_cast
                field_simp
                nlinarith
          _ = (detectorCutoff T : ℝ) * Real.exp (-(K : ℝ) / Y) *
                Real.exp (-(1 / Y)) ^ n := by ring
  have hNormSummable : Summable (fun n : ℕ =>
      ‖detectorCoeff (n + K + 1) T * ((n + K + 1 : ℕ) : ℂ) ^ (-ρ)‖) :=
    hMajor.of_nonneg_of_le (fun n => norm_nonneg _) hPoint
  unfold appendixCDetectorTail
  dsimp [K] at hPoint hNormSummable ⊢
  calc
    ‖∑' n : ℕ, detectorCoeff (n + 2 ^ dyadicScaleIndexCount T + 1) T *
        ((n + 2 ^ dyadicScaleIndexCount T + 1 : ℕ) : ℂ) ^ (-ρ)‖
        ≤ ∑' n : ℕ, ‖detectorCoeff (n + 2 ^ dyadicScaleIndexCount T + 1) T *
            ((n + 2 ^ dyadicScaleIndexCount T + 1 : ℕ) : ℂ) ^ (-ρ)‖ :=
          norm_tsum_le_tsum_norm hNormSummable
    _ ≤ ∑' n : ℕ, major n :=
      hNormSummable.tsum_le_tsum hPoint hMajor
    _ = (detectorCutoff T : ℝ) * Real.exp (-(K : ℝ) / Y) * (1 - r)⁻¹ := by
      rw [show (∑' n : ℕ, major n) =
          ((detectorCutoff T : ℝ) * Real.exp (-(K : ℝ) / Y)) *
            ∑' n : ℕ, r ^ n by simp [major, tsum_mul_left]]
      rw [tsum_geometric_of_lt_one hrNonneg hrLt]
    _ = _ := by rfl

/-- Beyond the explicit source threshold, the geometric tail has a simple
super-polynomial majorant independent of the zero. -/
private theorem norm_appendixCDetectorTail_le_logGaussian {ρ : ℂ} {T : ℝ}
    (hT : Real.exp 10 ≤ T) (hβ : 0 ≤ ρ.re) :
    ‖appendixCDetectorTail ρ T‖ ≤
      6 * T ^ 2 * Real.exp (-(Real.log T) ^ 2) := by
  let Y := T ^ (1 / 2 : ℝ)
  let K := 2 ^ dyadicScaleIndexCount T
  have hTpos : 0 < T := (Real.exp_pos 10).trans_le hT
  have hTone : 1 ≤ T := by
    have : (1 : ℝ) ≤ Real.exp 10 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by norm_num)
    exact this.trans hT
  have hLog : 10 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 10) hT
  have hLogPos : 0 < Real.log T := by linarith
  have hYpos : 0 < Y := by dsimp [Y]; positivity
  have hYTwo : 2 ≤ Y := by
    dsimp [Y]
    have hFour : (4 : ℝ) ≤ T := by
      linarith [Real.add_one_lt_exp (by norm_num : (10 : ℝ) ≠ 0)]
    have hSqrt := Real.sqrt_le_sqrt hFour
    rw [← Real.sqrt_eq_rpow]
    norm_num at hSqrt
    exact hSqrt
  have hYleT : Y ≤ T := by
    dsimp [Y]
    simpa using Real.rpow_le_rpow_of_exponent_le hTone
      (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hUpperPos : 0 < detectorScaleUpper T := by
    unfold detectorScaleUpper
    positivity
  have hKUpper := detectorScaleUpper_lt_finalDyadicScale hUpperPos
  have hRatio : (Real.log T) ^ 2 < (K : ℝ) / Y := by
    rw [lt_div_iff₀ hYpos]
    simpa [detectorScaleUpper, Y, K, mul_comm] using hKUpper
  have hExp : Real.exp (-(K : ℝ) / Y) ≤ Real.exp (-(Real.log T) ^ 2) := by
    apply Real.exp_le_exp.mpr
    rw [show -(K : ℝ) / Y = -((K : ℝ) / Y) by ring]
    exact neg_le_neg hRatio.le
  let den := 1 - Real.exp (-(1 / Y))
  have hRatioLt : Real.exp (-(1 / Y)) < 1 := by
    rw [Real.exp_lt_one_iff]
    exact neg_neg_of_pos (one_div_pos.mpr hYpos)
  have hDenPos : 0 < den := by dsimp [den]; linarith
  have hDenLower : (2 * Y)⁻¹ ≤ den := by
    simpa [den] using half_inv_le_one_sub_exp_neg_inv hYTwo
  have hDenInv : den⁻¹ ≤ 2 * Y := by
    rw [inv_le_iff_one_le_mul₀' hDenPos]
    calc
      1 = (2 * Y) * (2 * Y)⁻¹ := by field_simp
      _ ≤ (2 * Y) * den := by gcongr
      _ = den * (2 * Y) := by ring
  have hGeom := norm_appendixCDetectorTail_le_geometric hTone hβ
  change ‖appendixCDetectorTail ρ T‖ ≤
      (detectorCutoff T : ℝ) * Real.exp (-(K : ℝ) / Y) * den⁻¹ at hGeom
  calc
    ‖appendixCDetectorTail ρ T‖
        ≤ (detectorCutoff T : ℝ) * Real.exp (-(K : ℝ) / Y) * den⁻¹ := hGeom
    _ ≤ (3 * T) * Real.exp (-(Real.log T) ^ 2) * (2 * Y) := by
      gcongr
      exact detectorCutoff_cast_le_three_mul hTone
    _ ≤ 6 * T ^ 2 * Real.exp (-(Real.log T) ^ 2) := by
      calc
        (3 * T) * Real.exp (-(Real.log T) ^ 2) * (2 * Y) =
            6 * T * Y * Real.exp (-(Real.log T) ^ 2) := by ring
        _ ≤ 6 * T * T * Real.exp (-(Real.log T) ^ 2) := by gcongr
        _ = 6 * T ^ 2 * Real.exp (-(Real.log T) ^ 2) := by ring

/-- The detector tail is eventually smaller than the fixed dichotomy margin. -/
private theorem eventually_norm_appendixCDetectorTail_le :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (ρ : ℂ), 0 ≤ ρ.re →
      ‖appendixCDetectorTail ρ T‖ ≤ 1 / 12 := by
  filter_upwards [Filter.eventually_ge_atTop (Real.exp 10)] with T hT
  intro ρ hβ
  have hTail := norm_appendixCDetectorTail_le_logGaussian hT hβ
  have hTpos : 0 < T := (Real.exp_pos 10).trans_le hT
  have hLog : 10 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 10) hT
  have hLogPos : 0 < Real.log T := by linarith
  have hExpBound : Real.exp (-(Real.log T) ^ 2) ≤ T⁻¹ ^ (10 : ℕ) := by
    calc
      Real.exp (-(Real.log T) ^ 2) ≤ Real.exp (-10 * Real.log T) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = T⁻¹ ^ (10 : ℕ) := by
        have hArg : -10 * Real.log T = (10 : ℕ) * (-Real.log T) := by ring
        rw [hArg, Real.exp_nat_mul, Real.exp_neg, Real.exp_log hTpos]
  have hTTwo : 2 ≤ T := by
    linarith [Real.add_one_lt_exp (by norm_num : (10 : ℝ) ≠ 0)]
  calc
    ‖appendixCDetectorTail ρ T‖ ≤ 6 * T ^ 2 * Real.exp (-(Real.log T) ^ 2) := hTail
    _ ≤ 6 * T ^ 2 * (T⁻¹ ^ (10 : ℕ)) := by gcongr
    _ = 6 / T ^ 8 := by field_simp
    _ ≤ 1 / 12 := by
      rw [div_le_iff₀ (pow_pos hTpos 8)]
      have hPow : (2 : ℝ) ^ 8 ≤ T ^ 8 := pow_le_pow_left₀ (by norm_num) hTTwo 8
      norm_num at hPow ⊢
      linarith

/-- The uncancelled constant detector coefficient retains a fixed margin. -/
private theorem norm_appendixCDetector_constant_ge {ρ : ℂ} {T : ℝ}
    (hT : 36 ≤ T) :
    5 / 6 ≤ ‖detectorCoeff 1 T * (1 : ℂ) ^ (-ρ)‖ := by
  have hTone : 1 ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hSqrt := Real.sqrt_le_sqrt hT
  have hYSix : 6 ≤ T ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    norm_num at hSqrt
    exact hSqrt
  have hYpos : 0 < T ^ (1 / 2 : ℝ) := by positivity
  have hInv : 1 / T ^ (1 / 2 : ℝ) ≤ 1 / 6 := by
    exact one_div_le_one_div_of_le (by norm_num) hYSix
  have hExpLower := Real.add_one_le_exp (-(1 / T ^ (1 / 2 : ℝ)))
  rw [detectorCoeff_one T hTone]
  simp only [one_cpow, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  calc
    (5 / 6 : ℝ) ≤ 1 - 1 / T ^ (1 / 2 : ℝ) := by linarith
    _ ≤ Real.exp (-(1 / T ^ (1 / 2 : ℝ))) := by linarith
    _ = Real.exp (-1 / T ^ (1 / 2 : ℝ)) := by congr 1; ring

/-- A single scalar majorant for all four contour-shift error terms. -/
private noncomputable def appendixCScalarErrorConstant : ℝ :=
  2360 + 160 / Real.pi + ((20 / 3) * appendixCPSeries) / Real.pi

private theorem appendixCScalarErrorConstant_pos : 0 < appendixCScalarErrorConstant := by
  unfold appendixCScalarErrorConstant
  have hP := appendixCPSeries_nonneg
  have hPi := Real.pi_pos
  positivity

private theorem appendixC_error_expression_le {T : ℝ} (hT : 1 ≤ T) :
    200 / T ^ 3 + 2160 / T ^ 4 +
        (51840 * T ^ 2) / (4 * Real.pi * (3 * T) ^ 4) +
        ((2160 * appendixCPSeries) * T ^ 2) /
          (4 * Real.pi * (3 * T) ^ 4) ≤
      appendixCScalarErrorConstant / T ^ 2 := by
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hTne : T ≠ 0 := hTpos.ne'
  have hPi : 0 < Real.pi := Real.pi_pos
  have hEq :
      (51840 * T ^ 2) / (4 * Real.pi * (3 * T) ^ 4) =
        (160 / Real.pi) / T ^ 2 := by
    field_simp [Real.pi_ne_zero, hTne]
    ring
  have hEqP :
      ((2160 * appendixCPSeries) * T ^ 2) /
          (4 * Real.pi * (3 * T) ^ 4) =
        (((20 / 3) * appendixCPSeries) / Real.pi) / T ^ 2 := by
    field_simp [Real.pi_ne_zero, hTne]
    ring
  rw [hEq, hEqP]
  have hThree : 200 / T ^ 3 ≤ 200 / T ^ 2 := by
    rw [div_le_div_iff_of_pos_left (by norm_num) (pow_pos hTpos 3) (pow_pos hTpos 2)]
    nlinarith [sq_nonneg T]
  have hFour : 2160 / T ^ 4 ≤ 2160 / T ^ 2 := by
    rw [div_le_div_iff_of_pos_left (by norm_num) (pow_pos hTpos 4) (pow_pos hTpos 2)]
    have hT2One : 1 ≤ T ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hT) (by linarith : 0 ≤ T + 1)]
    nlinarith [mul_nonneg (sq_nonneg T) (sub_nonneg.mpr hT2One)]
  calc
    200 / T ^ 3 + 2160 / T ^ 4 + (160 / Real.pi) / T ^ 2 +
          (((20 / 3) * appendixCPSeries) / Real.pi) / T ^ 2
        ≤ 200 / T ^ 2 + 2160 / T ^ 2 + (160 / Real.pi) / T ^ 2 +
          (((20 / 3) * appendixCPSeries) / Real.pi) / T ^ 2 := by linarith
    _ = appendixCScalarErrorConstant / T ^ 2 := by
      unfold appendixCScalarErrorConstant
      ring

/-- The complete infinite contour shift eventually costs at most `1/12`. -/
private theorem eventually_appendixC_contour_shift_error_le :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ (ρ : ℂ),
      ρ ∈ ZeroRectangle (7 / 10) 1 T (2 * T) → riemannZeta ρ = 0 →
      ‖appendixCDetectorValue ρ T - typeIIContourIntegral ρ T‖ ≤ 1 / 12 := by
  have hPow : Filter.Tendsto (fun T : ℝ => T ^ (2 : ℕ))
      Filter.atTop Filter.atTop := by
    exact Filter.tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hLim : Filter.Tendsto
      (fun T : ℝ => appendixCScalarErrorConstant / T ^ (2 : ℕ))
      Filter.atTop (nhds 0) := tendsto_const_nhds.div_atTop hPow
  have hSmall : ∀ᶠ T : ℝ in Filter.atTop,
      appendixCScalarErrorConstant / T ^ (2 : ℕ) < 1 / 12 :=
    hLim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 12))
  filter_upwards [hSmall, Filter.eventually_ge_atTop 2] with T hSmall hT
  intro ρ hRect hZero
  exact (appendixC_contour_shift_error hT hRect hZero).trans
    ((appendixC_error_expression_le (by linarith)).trans hSmall.le)

/-- Native Appendix C coverage: every sufficiently high zeta zero in the
source range is detected either by one admissible Type-I block or by the
contour Type-II integral. -/
theorem typeIContourTypeIICoverOn_native :
    TypeIContourTypeIICoverOnProp (7 / 10) := by
  have hEventually : ∀ᶠ T : ℝ in Filter.atTop,
      Real.exp 10 ≤ T ∧ 36 ≤ T ∧
      (dyadicScaleIndexCount T : ℝ) ≤ Real.log T ∧
      (∀ (ρ : ℂ), 0 ≤ ρ.re → ‖appendixCDetectorTail ρ T‖ ≤ 1 / 12) ∧
      (∀ (ρ : ℂ), ρ ∈ ZeroRectangle (7 / 10) 1 T (2 * T) →
        riemannZeta ρ = 0 →
        ‖appendixCDetectorValue ρ T - typeIIContourIntegral ρ T‖ ≤ 1 / 12) := by
    filter_upwards [Filter.eventually_ge_atTop (Real.exp 10),
      Filter.eventually_ge_atTop 36,
      eventually_dyadicScaleIndexCount_le_log,
      eventually_norm_appendixCDetectorTail_le,
      eventually_appendixC_contour_shift_error_le] with T hExp h36 hCount hTail hError
    exact ⟨hExp, h36, hCount, hTail, hError⟩
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 hEventually
  refine ⟨max 2 T₁, le_max_left 2 T₁, ?_⟩
  intro T hT ρ hRect hZero
  have hAll := hT₁ T (le_trans (le_max_right 2 T₁) hT)
  rcases hAll with ⟨hExp, h36, hCount, hTailAll, hErrorAll⟩
  by_cases hTypeI : IsTypeIZero ρ T
  · exact Or.inl hTypeI
  · right
    rw [mem_ZeroRectangle] at hRect
    rcases hRect with ⟨hβLower, hβUpper, hγLower, hγUpper⟩
    have hRect' : ρ ∈ ZeroRectangle (7 / 10) 1 T (2 * T) := by
      rw [mem_ZeroRectangle]
      exact ⟨hβLower, hβUpper, hγLower, hγUpper⟩
    have hTpos : 0 < T := (Real.exp_pos 10).trans_le hExp
    have hTone : 1 ≤ T := by
      have : (1 : ℝ) ≤ Real.exp 10 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by norm_num)
      exact this.trans hExp
    have hLogLower : 10 ≤ Real.log T := by
      simpa using Real.log_le_log (Real.exp_pos 10) hExp
    have hLog : 0 < Real.log T := by linarith
    have hUpperOne : 1 ≤ detectorScaleUpper T := by
      unfold detectorScaleUpper
      have hPowOne : 1 ≤ T ^ (1 / 2 : ℝ) :=
        Real.one_le_rpow hTone (by norm_num)
      have hLogSqOne : 1 ≤ (Real.log T) ^ 2 := by nlinarith
      nlinarith
    let W := wideDirichletPoly 1 (dyadicScaleIndexCount T)
      (appendixCLineCoeff ρ T) ρ.im
    let C := detectorCoeff 1 T * (1 : ℂ) ^ (-ρ)
    let E := appendixCDetectorTail ρ T
    have hWideBase := norm_wideDirichletPoly_appendixC_le hTone hLog hUpperOne hTypeI
    have hWide : ‖W‖ ≤ 1 / 3 := by
      dsimp [W]
      calc
        ‖wideDirichletPoly 1 (dyadicScaleIndexCount T)
            (appendixCLineCoeff ρ T) ρ.im‖
            ≤ (dyadicScaleIndexCount T : ℝ) / (3 * Real.log T) := hWideBase
        _ ≤ Real.log T / (3 * Real.log T) := by
          exact div_le_div_of_nonneg_right hCount (by positivity)
        _ = 1 / 3 := by field_simp
    have hTail : ‖E‖ ≤ 1 / 12 := by
      exact hTailAll ρ (by linarith)
    have hConstant : 5 / 6 ≤ ‖C‖ := by
      exact norm_appendixCDetector_constant_ge h36
    have hDecomp : appendixCDetectorValue ρ T = C + W + E := by
      simpa [C, W, E] using
        appendixCDetectorValue_eq_one_add_wide_add_tail hTpos (by linarith)
    have hConstantUpper : ‖C‖ ≤
        ‖appendixCDetectorValue ρ T‖ + ‖W‖ + ‖E‖ := by
      have hRearrange : C = appendixCDetectorValue ρ T - W - E := by
        rw [hDecomp]
        abel
      rw [hRearrange]
      calc
        ‖appendixCDetectorValue ρ T - W - E‖
            ≤ ‖appendixCDetectorValue ρ T - W‖ + ‖E‖ := norm_sub_le _ _
        _ ≤ (‖appendixCDetectorValue ρ T‖ + ‖W‖) + ‖E‖ := by
          gcongr
          exact norm_sub_le _ _
    have hDetector : 5 / 12 ≤ ‖appendixCDetectorValue ρ T‖ := by
      linarith
    have hError := hErrorAll ρ hRect' hZero
    unfold IsContourTypeIIZero
    have hDetectorUpper : ‖appendixCDetectorValue ρ T‖ ≤
        ‖appendixCDetectorValue ρ T - typeIIContourIntegral ρ T‖ +
          ‖typeIIContourIntegral ρ T‖ := by
      calc
        ‖appendixCDetectorValue ρ T‖ =
            ‖(appendixCDetectorValue ρ T - typeIIContourIntegral ρ T) +
              typeIIContourIntegral ρ T‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith

/-- Source-range specialization used by the finite Type-I/Type-II transfer. -/
theorem typeIContourTypeIICover_native : TypeIContourTypeIICoverProp :=
  typeIContourTypeIICoverOn_native

end RiemannZeta.GuthMaynard
