import RiemannZeta.GuthMaynard.HughesYoungBetaIntegral
import RiemannZeta.GuthMaynard.HughesYoungDFIProfile
import RiemannZeta.GuthMaynard.HughesYoungPolygamma
import Mathlib.Analysis.MellinTransform

open Asymptotics Complex Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Logarithmic beta continuation for the Hughes--Young central term

The DFI equation-(27) main term contains two logarithmic factors.  Before
the Hughes--Young Mellin contour can be moved to the absolute-convergence
line, those factors must be represented as parameter derivatives of the
beta integral.  This file establishes that bridge starting with the exact
left-parameter derivative on the source convergence domain.
-/

/-- The fixed `(1+x)^B` factor in the beta integral, viewed as the function
whose Mellin transform supplies the other power. -/
noncomputable def hughesYoungBetaTail (B : ℂ) (x : ℝ) : ℂ :=
  (1 + (x : ℂ)) ^ B

theorem continuousOn_hughesYoungBetaTail (B : ℂ) :
    ContinuousOn (hughesYoungBetaTail B) (Set.Ioi 0) := by
  intro x hx
  unfold hughesYoungBetaTail
  have hx0 : 0 < x := hx
  have hbase : 1 + (x : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using (show 0 < 1 + x by linarith)
  exact ((by fun_prop : ContinuousAt (fun y : ℝ => 1 + (y : ℂ)) x).cpow
    continuousAt_const hbase).continuousWithinAt

theorem locallyIntegrableOn_hughesYoungBetaTail (B : ℂ) :
    LocallyIntegrableOn (hughesYoungBetaTail B) (Set.Ioi 0) :=
  (continuousOn_hughesYoungBetaTail B).locallyIntegrableOn measurableSet_Ioi

theorem continuousOn_hughesYoungBetaIntegrand (A B : ℂ) :
    ContinuousOn
      (fun x : ℝ => (x : ℂ) ^ A * (1 + (x : ℂ)) ^ B) (Set.Ioi 0) := by
  intro x hx
  have hx0 : 0 < x := hx
  have hxbase : (x : ℂ) ∈ Complex.slitPlane :=
    Complex.ofReal_mem_slitPlane.2 hx0
  have honebase : 1 + (x : ℂ) ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    left
    simpa using (show 0 < 1 + x by linarith)
  exact (((Complex.continuous_ofReal.continuousAt).cpow continuousAt_const hxbase).mul
    ((by fun_prop : ContinuousAt (fun y : ℝ => 1 + (y : ℂ)) x).cpow
      continuousAt_const honebase)).continuousWithinAt

/-- On the right, a negative beta exponent is bounded by the corresponding
pure power. -/
theorem hughesYoungBetaTail_isBigO_atTop
    {B : ℂ} (hB : B.re ≤ 0) :
    hughesYoungBetaTail B =O[atTop] (fun x : ℝ => x ^ B.re) := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hbase : 0 < 1 + x := by positivity
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0.le _)]
  unfold hughesYoungBetaTail
  rw [show 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase]
  exact Real.rpow_le_rpow_of_nonpos hx0 (by linarith) hB

/-- Near zero, a negative beta exponent is uniformly bounded. -/
theorem hughesYoungBetaTail_isBigO_nhdsGT_zero
    {B : ℂ} (hB : B.re ≤ 0) :
    hughesYoungBetaTail B =O[𝓝[>] (0 : ℝ)] (fun _ : ℝ => (1 : ℝ)) := by
  apply IsBigO.of_bound 1
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : 0 < x := hx
  have hbase : 0 < 1 + x := by positivity
  rw [one_mul, Real.norm_eq_abs, abs_one]
  unfold hughesYoungBetaTail
  rw [show 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) by push_cast; rfl]
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hbase]
  exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hB

/-- The second logarithm in the beta kernel is controlled by the Mellin
logarithm uniformly on the whole positive axis. -/
theorem log_one_add_le_log_two_add_abs_log {x : ℝ} (hx : 0 < x) :
    Real.log (1 + x) ≤ Real.log 2 + |Real.log x| := by
  by_cases hx1 : x ≤ 1
  · have hpos : 0 < 1 + x := by positivity
    have hle : 1 + x ≤ 2 := by linarith
    have hlog := (Real.strictMonoOn_log.le_iff_le hpos (by norm_num : (0 : ℝ) < 2)).2 hle
    exact hlog.trans (le_add_of_nonneg_right (abs_nonneg _))
  · have h1x : 1 < x := lt_of_not_ge hx1
    have hpos : 0 < 1 + x := by positivity
    have h2x : 0 < 2 * x := mul_pos (by norm_num) hx
    have hle : 1 + x ≤ 2 * x := by linarith
    have hlog := (Real.strictMonoOn_log.le_iff_le hpos h2x).2 hle
    rw [Real.log_mul (by norm_num) hx.ne'] at hlog
    rw [abs_of_nonneg (Real.log_nonneg h1x.le)]
    exact hlog

theorem integrableOn_hughesYoungBeta
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ A * (1 + (x : ℂ)) ^ B) (Set.Ioi 0) := by
  have hB : B.re < 0 := by
    have hs : A.re + B.re + 1 < 0 := by simpa using hAB
    have hA' : -1 < A.re := by
      have : 0 < A.re + 1 := by simpa using hA
      linarith
    linarith
  have htop : (A + 1).re < -B.re := by
    have hs : A.re + B.re + 1 < 0 := by simpa using hAB
    simp only [add_re, one_re]
    linarith
  have hc := mellinConvergent_of_isBigO_rpow
    (E := ℂ) (a := -B.re) (b := 0)
    (f := hughesYoungBetaTail B) (s := A + 1)
    (locallyIntegrableOn_hughesYoungBetaTail B)
    (by simpa only [neg_neg] using hughesYoungBetaTail_isBigO_atTop hB.le)
    htop
    (by simpa only [neg_zero, Real.rpow_zero] using
      hughesYoungBetaTail_isBigO_nhdsGT_zero hB.le)
    (by simpa using hA)
  simpa only [MellinConvergent, hughesYoungBetaTail, add_sub_cancel_right,
    smul_eq_mul] using hc

theorem integrableOn_hughesYoungLogXBeta
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    IntegrableOn
      (fun x : ℝ => (Real.log x : ℂ) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) (Set.Ioi 0) := by
  have hB : B.re < 0 := by
    have hs : A.re + B.re + 1 < 0 := by simpa using hAB
    have hA' : -1 < A.re := by
      have : 0 < A.re + 1 := by simpa using hA
      linarith
    linarith
  have htop : (A + 1).re < -B.re := by
    have hs : A.re + B.re + 1 < 0 := by simpa using hAB
    simp only [add_re, one_re]
    linarith
  have hm := (mellin_hasDerivAt_of_isBigO_rpow
    (E := ℂ) (a := -B.re) (b := 0)
    (f := hughesYoungBetaTail B) (s := A + 1)
    (locallyIntegrableOn_hughesYoungBetaTail B)
    (by simpa only [neg_neg] using hughesYoungBetaTail_isBigO_atTop hB.le)
    htop
    (by simpa only [neg_zero, Real.rpow_zero] using
      hughesYoungBetaTail_isBigO_nhdsGT_zero hB.le)
    (by simpa using hA)).1
  simpa only [MellinConvergent, hughesYoungBetaTail, add_sub_cancel_right,
    smul_eq_mul, Complex.real_smul, mul_assoc, mul_left_comm, mul_comm] using hm

/-- Absolute integrability of the beta kernel with the second source
logarithm.  It is deduced from the base Mellin integral and its first
Mellin derivative, using the global logarithmic comparison above. -/
theorem integrableOn_hughesYoungLogOneAddBeta
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    IntegrableOn
      (fun x : ℝ => (Real.log (1 + x) : ℂ) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) (Set.Ioi 0) := by
  have hB : B.re < 0 := by
    have hsum : A.re + B.re + 1 < 0 := by simpa using hAB
    have hA' : -1 < A.re := by
      have : 0 < A.re + 1 := by simpa using hA
      linarith
    linarith
  have htop : (A + 1).re < -B.re := by
    have hsum : A.re + B.re + 1 < 0 := by simpa using hAB
    simp only [add_re, one_re]
    linarith
  have hbase := mellinConvergent_of_isBigO_rpow
    (E := ℂ) (a := -B.re) (b := 0)
    (f := hughesYoungBetaTail B) (s := A + 1)
    (locallyIntegrableOn_hughesYoungBetaTail B)
    (by simpa only [neg_neg] using
      hughesYoungBetaTail_isBigO_atTop hB.le)
    htop
    (by simpa only [neg_zero, Real.rpow_zero] using
      hughesYoungBetaTail_isBigO_nhdsGT_zero hB.le)
    (by simpa using hA)
  have hlog := (mellin_hasDerivAt_of_isBigO_rpow
    (E := ℂ) (a := -B.re) (b := 0)
    (f := hughesYoungBetaTail B) (s := A + 1)
    (locallyIntegrableOn_hughesYoungBetaTail B)
    (by simpa only [neg_neg] using
      hughesYoungBetaTail_isBigO_atTop hB.le)
    htop
    (by simpa only [neg_zero, Real.rpow_zero] using
      hughesYoungBetaTail_isBigO_nhdsGT_zero hB.le)
    (by simpa using hA)).1
  have hbase' : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ A * (1 + (x : ℂ)) ^ B) (Set.Ioi 0) := by
    simpa only [MellinConvergent, hughesYoungBetaTail, add_sub_cancel_right,
      smul_eq_mul] using hbase
  have hlog' : IntegrableOn
      (fun x : ℝ => (Real.log x : ℂ) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) (Set.Ioi 0) := by
    simpa only [MellinConvergent, hughesYoungBetaTail, add_sub_cancel_right,
      smul_eq_mul, Complex.real_smul, mul_assoc, mul_left_comm, mul_comm] using hlog
  let g : ℝ → ℝ := fun x =>
    Real.log 2 * ‖(x : ℂ) ^ A * (1 + (x : ℂ)) ^ B‖ +
      ‖(Real.log x : ℂ) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)‖
  have hg : IntegrableOn g (Set.Ioi 0) := by
    exact (hbase'.norm.const_mul (Real.log 2)).add hlog'.norm
  apply hg.mono'
  · have hlogCont : ContinuousOn (fun x : ℝ => Real.log (1 + x)) (Set.Ioi 0) :=
      (by fun_prop : ContinuousOn (fun x : ℝ => 1 + x) (Set.Ioi 0)).log
        (by intro x hx; have hx0 : 0 < x := hx; linarith)
    have hlogComplex : ContinuousOn
        (fun x : ℝ => (Real.log (1 + x) : ℂ)) (Set.Ioi 0) := by
      simpa only [Function.comp_apply] using
        Complex.continuous_ofReal.comp_continuousOn hlogCont
    exact hlogComplex.aestronglyMeasurable measurableSet_Ioi |>.mul
      hbase'.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    have hlog0 : 0 ≤ Real.log (1 + x) :=
      Real.log_nonneg (by linarith)
    dsimp only [g]
    rw [norm_mul, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_nonneg hlog0]
    calc
      Real.log (1 + x) * ‖(x : ℂ) ^ A * (1 + (x : ℂ)) ^ B‖ ≤
          (Real.log 2 + |Real.log x|) *
            ‖(x : ℂ) ^ A * (1 + (x : ℂ)) ^ B‖ :=
        mul_le_mul_of_nonneg_right (log_one_add_le_log_two_add_abs_log hx0)
          (norm_nonneg _)
      _ = Real.log 2 * ‖(x : ℂ) ^ A * (1 + (x : ℂ)) ^ B‖ +
          ‖(Real.log x : ℂ) *
            ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)‖ := by
        simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        ring

/-- Differentiating the second exponent inserts the literal logarithm
`log (1+x)`.  The proof uses a strict substrip and dominated complex
differentiation, so the conclusion concerns the actual Bochner integral. -/
theorem hasDerivAt_hughesYoungLogOneAddBetaIntegral
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    HasDerivAt
      (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
        (x : ℂ) ^ A * (1 + (x : ℂ)) ^ z)
      (∫ x in Set.Ioi (0 : ℝ),
        (Real.log (1 + x) : ℂ) *
          ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) B := by
  let δ : ℝ := -(A + B + 1).re / 2
  have hδ : 0 < δ := by
    have hs : A.re + B.re + 1 < 0 := by simpa using hAB
    dsimp [δ]
    linarith
  let Bδ : ℂ := ((B.re + δ : ℝ) : ℂ)
  have hABδ : (A + Bδ + 1).re < 0 := by
    have hs : A.re + B.re + 1 < 0 := by simpa using hAB
    change A.re + (B.re + δ) + 1 < 0
    dsimp [δ]
    linarith
  have hbound : IntegrableOn
      (fun x : ℝ => (Real.log (1 + x) : ℂ) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ Bδ)) (Set.Ioi 0) :=
    integrableOn_hughesYoungLogOneAddBeta hA hABδ
  have hbase : IntegrableOn
      (fun x : ℝ => (x : ℂ) ^ A * (1 + (x : ℂ)) ^ B) (Set.Ioi 0) := by
    have hB : B.re < 0 := by
      have hs : A.re + B.re + 1 < 0 := by simpa using hAB
      have hA' : -1 < A.re := by
        have : 0 < A.re + 1 := by simpa using hA
        linarith
      linarith
    have htop : (A + 1).re < -B.re := by
      have hs : A.re + B.re + 1 < 0 := by simpa using hAB
      simp only [add_re, one_re]
      linarith
    have hc := mellinConvergent_of_isBigO_rpow
      (E := ℂ) (a := -B.re) (b := 0)
      (f := hughesYoungBetaTail B) (s := A + 1)
      (locallyIntegrableOn_hughesYoungBetaTail B)
      (by simpa only [neg_neg] using
        hughesYoungBetaTail_isBigO_atTop hB.le)
      htop
      (by simpa only [neg_zero, Real.rpow_zero] using
        hughesYoungBetaTail_isBigO_nhdsGT_zero hB.le)
      (by simpa using hA)
    simpa only [MellinConvergent, hughesYoungBetaTail, add_sub_cancel_right,
      smul_eq_mul] using hc
  let F : ℂ → ℝ → ℂ := fun z x =>
    (x : ℂ) ^ A * (1 + (x : ℂ)) ^ z
  let F' : ℂ → ℝ → ℂ := fun z x =>
    (Real.log (1 + x) : ℂ) *
      ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ z)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0))
    (F := F) (F' := F')
    (bound := fun x => ‖(Real.log (1 + x) : ℂ) *
      ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ Bδ)‖)
    (s := Metric.ball B δ) (x₀ := B)
    (Metric.ball_mem_nhds B hδ)
    (Filter.Eventually.of_forall fun z =>
      (continuousOn_hughesYoungBetaIntegrand A z).aestronglyMeasurable measurableSet_Ioi)
    hbase
    (by
      dsimp only [F']
      exact (integrableOn_hughesYoungLogOneAddBeta hA hAB).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      intro z hz
      have hx0 : 0 < x := hx
      have hbase1 : 0 < 1 + x := by linarith
      have hzNorm : ‖z - B‖ < δ := by
        have hz' := Metric.mem_ball.mp hz
        rwa [dist_eq_norm] at hz'
      have hzre : z.re ≤ B.re + δ := by
        have hre := Complex.re_le_norm (z - B)
        simp only [sub_re] at hre
        linarith
      dsimp only [F', Bδ]
      have hone : 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hone]
      simp only [norm_mul, Complex.norm_real]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase1,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase1]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (by linarith) hzre)
          (Real.rpow_nonneg hx0.le _)) (norm_nonneg _))
    hbound.norm
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      intro z _hz
      have hx0 : 0 < x := hx
      have hbase1 : 0 < 1 + x := by linarith
      have hone : 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) := by
        push_cast
        rfl
      have hne : (1 + (x : ℂ)) ≠ 0 := by
        rw [hone]
        exact Complex.ofReal_ne_zero.mpr hbase1.ne'
      have hp := (hasDerivAt_id z).const_cpow (Or.inl hne)
      have hc := hp.const_mul ((x : ℂ) ^ A)
      dsimp only [F, F']
      convert hc using 1
      · rw [hone, Complex.ofReal_log hbase1.le]
        simp only [id_eq]
        ring)
  simpa only [F, F'] using hmain.2

/-- Differentiating the first exponent of the beta integral inserts the
literal logarithm `log x`.  This is an equality for the actual Bochner
integral on `Ioi 0`, not a formal derivative assigned by definition. -/
theorem hasDerivAt_hughesYoungLogXBetaIntegral
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    HasDerivAt
      (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
        (x : ℂ) ^ z * (1 + (x : ℂ)) ^ B)
      (∫ x in Set.Ioi (0 : ℝ),
        (Real.log x : ℂ) *
          ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) A := by
  have hB : B.re < 0 := by
    have hsum : A.re + B.re + 1 < 0 := by simpa using hAB
    have hA' : -1 < A.re := by
      have : 0 < A.re + 1 := by simpa using hA
      linarith
    linarith
  have htop : (A + 1).re < -B.re := by
    have hsum : A.re + B.re + 1 < 0 := by simpa using hAB
    simp only [add_re, one_re]
    linarith
  have hm := mellin_hasDerivAt_of_isBigO_rpow
    (E := ℂ)
    (a := -B.re) (b := 0)
    (f := hughesYoungBetaTail B) (s := A + 1)
    (locallyIntegrableOn_hughesYoungBetaTail B)
    (by simpa only [neg_neg] using
      hughesYoungBetaTail_isBigO_atTop hB.le)
    htop
    (by simpa only [neg_zero, Real.rpow_zero] using
      hughesYoungBetaTail_isBigO_nhdsGT_zero hB.le)
    (by simpa using hA)
  have hcomp := hm.2.comp A ((hasDerivAt_id A).add_const 1)
  have hsource :
      (mellin (hughesYoungBetaTail B) ∘ fun z : ℂ => id z + 1) =
        fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
          (x : ℂ) ^ z * (1 + (x : ℂ)) ^ B := by
    funext z
    unfold mellin hughesYoungBetaTail Function.comp
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    simp only [id_eq, add_sub_cancel_right, smul_eq_mul]
  have hderivative :
      mellin (fun t => Real.log t • hughesYoungBetaTail B t) (A + 1) =
        ∫ x in Set.Ioi (0 : ℝ),
          (Real.log x : ℂ) *
            ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B) := by
    unfold mellin
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
    intro x _hx
    simp only [hughesYoungBetaTail, smul_eq_mul]
    rw [Complex.real_smul]
    ring_nf
  rw [hsource, hderivative] at hcomp
  simpa only [mul_one] using hcomp

/-- Absolute integrability of the beta kernel with both DFI logarithms. -/
theorem integrableOn_hughesYoungMixedLogBeta
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    IntegrableOn
      (fun x : ℝ => (Real.log x : ℂ) * (Real.log (1 + x) : ℂ) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) (Set.Ioi 0) := by
  have hB : B.re < 0 := by
    have hs : A.re + B.re + 1 < 0 := by simpa using hAB
    have hA' : -1 < A.re := by
      have : 0 < A.re + 1 := by simpa using hA
      linarith
    linarith
  let a₀ : ℝ := -B.re
  let s₀ : ℝ := (A + 1).re
  let a₁ : ℝ := (s₀ + a₀) / 2
  let b₁ : ℝ := s₀ / 2
  have hspos : 0 < s₀ := by simpa [s₀] using hA
  have hsa : s₀ < a₀ := by
    dsimp [s₀, a₀]
    have hs : A.re + B.re + 1 < 0 := by simpa using hAB
    linarith
  have hsa₁ : s₀ < a₁ := by dsimp [a₁]; linarith
  have ha₁a₀ : a₁ < a₀ := by dsimp [a₁]; linarith
  have hb₁pos : 0 < b₁ := by dsimp [b₁]; linarith
  have hb₁s : b₁ < s₀ := by dsimp [b₁]; linarith
  have htop₀ : hughesYoungBetaTail B =O[atTop]
      (fun x : ℝ => x ^ (-a₀)) := by
    dsimp only [a₀]
    simpa only [neg_neg] using hughesYoungBetaTail_isBigO_atTop hB.le
  have hzero₀ : hughesYoungBetaTail B =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    simpa only [neg_zero, Real.rpow_zero] using
      hughesYoungBetaTail_isBigO_nhdsGT_zero hB.le
  let f₁ : ℝ → ℂ := fun x => Real.log x • hughesYoungBetaTail B x
  have hf₁loc : LocallyIntegrableOn f₁ (Set.Ioi 0) := by
    have hlogCont : ContinuousOn Real.log (Set.Ioi 0) :=
      Real.continuousOn_log.mono (by
        intro x hx
        exact ne_of_gt hx)
    exact (hlogCont.smul (continuousOn_hughesYoungBetaTail B)).locallyIntegrableOn
      measurableSet_Ioi
  have htop₁ : f₁ =O[atTop] (fun x : ℝ => x ^ (-a₁)) := by
    exact isBigO_rpow_top_log_smul ha₁a₀ htop₀
  have hzero₁ : f₁ =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun x : ℝ => x ^ (-b₁)) := by
    exact isBigO_rpow_zero_log_smul hb₁pos hzero₀
  have hlog₂ := (mellin_hasDerivAt_of_isBigO_rpow
    (E := ℂ) (a := a₁) (b := b₁) (f := f₁) (s := A + 1)
    hf₁loc htop₁ (by simpa [s₀] using hsa₁)
    hzero₁ (by simpa [s₀] using hb₁s)).1
  have hlog₁ : IntegrableOn
      (fun x : ℝ => (Real.log x : ℂ) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) (Set.Ioi 0) := by
    have hm := (mellin_hasDerivAt_of_isBigO_rpow
      (E := ℂ) (a := a₀) (b := 0)
      (f := hughesYoungBetaTail B) (s := A + 1)
      (locallyIntegrableOn_hughesYoungBetaTail B) htop₀
      (by simpa [s₀] using hsa) hzero₀ (by simpa [s₀] using hspos)).1
    simpa only [MellinConvergent, hughesYoungBetaTail, add_sub_cancel_right,
      smul_eq_mul, Complex.real_smul, mul_assoc, mul_left_comm, mul_comm] using hm
  have hlog₂' : IntegrableOn
      (fun x : ℝ => (Real.log x : ℂ) *
        ((Real.log x : ℂ) *
          ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B))) (Set.Ioi 0) := by
    simpa only [MellinConvergent, f₁, hughesYoungBetaTail,
      add_sub_cancel_right, smul_eq_mul, Complex.real_smul,
      mul_assoc, mul_left_comm, mul_comm] using hlog₂
  let g : ℝ → ℝ := fun x =>
    Real.log 2 * ‖(Real.log x : ℂ) *
      ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)‖ +
    ‖(Real.log x : ℂ) * ((Real.log x : ℂ) *
      ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B))‖
  have hg : IntegrableOn g (Set.Ioi 0) :=
    (hlog₁.norm.const_mul (Real.log 2)).add hlog₂'.norm
  apply hg.mono'
  · have hlogOneCont : ContinuousOn
        (fun x : ℝ => (Real.log (1 + x) : ℂ)) (Set.Ioi 0) := by
      have hr : ContinuousOn (fun x : ℝ => Real.log (1 + x)) (Set.Ioi 0) :=
        (by fun_prop : ContinuousOn (fun x : ℝ => 1 + x) (Set.Ioi 0)).log
          (by intro x hx; have hx0 : 0 < x := hx; linarith)
      simpa only [Function.comp_apply] using
        Complex.continuous_ofReal.comp_continuousOn hr
    have hlogXCont : ContinuousOn
        (fun x : ℝ => (Real.log x : ℂ)) (Set.Ioi 0) := by
      have hr : ContinuousOn Real.log (Set.Ioi 0) :=
        Real.continuousOn_log.mono (by intro x hx; exact ne_of_gt hx)
      simpa only [Function.comp_apply] using
        Complex.continuous_ofReal.comp_continuousOn hr
    exact ((hlogXCont.mul hlogOneCont).mul
      (continuousOn_hughesYoungBetaIntegrand A B)).aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    have hlogOne0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
    dsimp only [g]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hlogOne0]
    have hc := log_one_add_le_log_two_add_abs_log hx0
    let K : ℝ := ‖(x : ℂ) ^ A‖ * ‖(1 + (x : ℂ)) ^ B‖
    change |Real.log x| * Real.log (1 + x) * K ≤
      Real.log 2 * (|Real.log x| * K) + |Real.log x| * (|Real.log x| * K)
    calc
      |Real.log x| * Real.log (1 + x) * K =
          Real.log (1 + x) * (|Real.log x| * K) := by ring
      _ ≤ (Real.log 2 + |Real.log x|) * (|Real.log x| * K) :=
        mul_le_mul_of_nonneg_right hc
          (mul_nonneg (abs_nonneg _) (by dsimp [K]; positivity))
      _ = Real.log 2 * (|Real.log x| * K) +
          |Real.log x| * (|Real.log x| * K) := by ring

/-- The mixed parameter derivative is the literal two-logarithm beta
integral occurring in DFI equation (27). -/
theorem hasDerivAt_hughesYoungMixedLogBetaIntegral
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    HasDerivAt
      (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
        (Real.log x : ℂ) *
          ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ z))
      (∫ x in Set.Ioi (0 : ℝ),
        (Real.log x : ℂ) * (Real.log (1 + x) : ℂ) *
          ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) B := by
  let δ : ℝ := -(A + B + 1).re / 2
  have hδ : 0 < δ := by
    have hs : A.re + B.re + 1 < 0 := by simpa using hAB
    dsimp [δ]
    linarith
  let Bδ : ℂ := ((B.re + δ : ℝ) : ℂ)
  have hABδ : (A + Bδ + 1).re < 0 := by
    have hs : A.re + B.re + 1 < 0 := by simpa using hAB
    change A.re + (B.re + δ) + 1 < 0
    dsimp [δ]
    linarith
  have hbound := integrableOn_hughesYoungMixedLogBeta hA hABδ
  have hlogX : IntegrableOn
      (fun x : ℝ => (Real.log x : ℂ) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) (Set.Ioi 0) := by
    have hB : B.re < 0 := by
      have hs : A.re + B.re + 1 < 0 := by simpa using hAB
      have hA' : -1 < A.re := by
        have : 0 < A.re + 1 := by simpa using hA
        linarith
      linarith
    have htop : (A + 1).re < -B.re := by
      have hs : A.re + B.re + 1 < 0 := by simpa using hAB
      simp only [add_re, one_re]
      linarith
    have hm := (mellin_hasDerivAt_of_isBigO_rpow
      (E := ℂ) (a := -B.re) (b := 0)
      (f := hughesYoungBetaTail B) (s := A + 1)
      (locallyIntegrableOn_hughesYoungBetaTail B)
      (by simpa only [neg_neg] using hughesYoungBetaTail_isBigO_atTop hB.le)
      htop
      (by simpa only [neg_zero, Real.rpow_zero] using
        hughesYoungBetaTail_isBigO_nhdsGT_zero hB.le)
      (by simpa using hA)).1
    simpa only [MellinConvergent, hughesYoungBetaTail, add_sub_cancel_right,
      smul_eq_mul, Complex.real_smul, mul_assoc, mul_left_comm, mul_comm] using hm
  let F : ℂ → ℝ → ℂ := fun z x => (Real.log x : ℂ) *
    ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ z)
  let F' : ℂ → ℝ → ℂ := fun z x =>
    (Real.log x : ℂ) * (Real.log (1 + x) : ℂ) *
      ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ z)
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0))
    (F := F) (F' := F')
    (bound := fun x => ‖(Real.log x : ℂ) * (Real.log (1 + x) : ℂ) *
      ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ Bδ)‖)
    (s := Metric.ball B δ) (x₀ := B)
    (Metric.ball_mem_nhds B hδ)
    (Filter.Eventually.of_forall fun z =>
      ((by
        have hlogCont : ContinuousOn
            (fun x : ℝ => (Real.log x : ℂ)) (Set.Ioi 0) := by
          have hr := Real.continuousOn_log.mono
            (show Set.Ioi (0 : ℝ) ⊆ {0}ᶜ by intro x hx; exact ne_of_gt hx)
          simpa only [Function.comp_apply] using
            Complex.continuous_ofReal.comp_continuousOn hr
        exact hlogCont.mul (continuousOn_hughesYoungBetaIntegrand A z)) :
          ContinuousOn (F z) (Set.Ioi 0)).aestronglyMeasurable measurableSet_Ioi)
    hlogX
    (by
      dsimp only [F']
      exact (integrableOn_hughesYoungMixedLogBeta hA hAB).aestronglyMeasurable)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      intro z hz
      have hx0 : 0 < x := hx
      have hbase1 : 0 < 1 + x := by linarith
      have hbase_ge : (1 : ℝ) ≤ 1 + x := by linarith
      have hzNorm : ‖z - B‖ < δ := by
        have hz' := Metric.mem_ball.mp hz
        rwa [dist_eq_norm] at hz'
      have hzre : z.re ≤ B.re + δ := by
        have hre := Complex.re_le_norm (z - B)
        simp only [sub_re] at hre
        linarith
      dsimp only [F', Bδ]
      have hone : 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hone]
      simp only [norm_mul, Complex.norm_real]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase1,
        Complex.norm_cpow_eq_rpow_re_of_pos hbase1]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le
            hbase_ge hzre)
          (Real.rpow_nonneg hx0.le _))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
    hbound.norm
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      intro z _hz
      have hx0 : 0 < x := hx
      have hbase1 : 0 < 1 + x := by linarith
      have hone : 1 + (x : ℂ) = ((1 + x : ℝ) : ℂ) := by
        push_cast
        rfl
      have hne : (1 + (x : ℂ)) ≠ 0 := by
        rw [hone]
        exact Complex.ofReal_ne_zero.mpr hbase1.ne'
      have hp := (hasDerivAt_id z).const_cpow (Or.inl hne)
      have hc := hp.const_mul ((Real.log x : ℂ) * (x : ℂ) ^ A)
      dsimp only [F, F']
      convert hc using 1
      · funext y
        simp only [id_eq]
        ring
      · rw [hone, Complex.ofReal_log hbase1.le]
        simp only [id_eq]
        ring)
  simpa only [F, F'] using hmain.2

/-! ## Gamma-quotient continuation of the logarithmic kernels -/

/-- The meromorphic Gamma quotient which continues the convergent beta
integral in both exponent parameters. -/
noncomputable def hughesYoungGammaBeta (A B : ℂ) : ℂ :=
  Complex.Gamma (A + 1) * Complex.Gamma (-A - B - 1) /
    Complex.Gamma (-B)

/-- Exact left-parameter logarithmic derivative of the Gamma quotient on
the beta half-plane.  This is the first differentiated factor in
Hughes--Young equation (83). -/
theorem hasDerivAt_hughesYoungGammaBeta_left
    {A B : ℂ} (hA : 0 < (A + 1).re) (hC : 0 < (-A - B - 1).re) :
    HasDerivAt (fun z => hughesYoungGammaBeta z B)
      (hughesYoungGammaBeta A B *
        (Complex.digamma (A + 1) - Complex.digamma (-A - B - 1))) A := by
  have hGA := hasDerivAt_Gamma_eq_mul_digamma_of_re_pos hA
  have hleft : HasDerivAt (fun z : ℂ => Complex.Gamma (z + 1))
      (Complex.Gamma (A + 1) * Complex.digamma (A + 1)) A := by
    convert hGA.comp A ((hasDerivAt_id A).add_const 1) using 1
    ring
  have hGC := hasDerivAt_Gamma_eq_mul_digamma_of_re_pos hC
  have hright : HasDerivAt (fun z : ℂ => Complex.Gamma (-z - B - 1))
      (-(Complex.Gamma (-A - B - 1) * Complex.digamma (-A - B - 1))) A := by
    have hi : HasDerivAt (fun z : ℂ => -z - B - 1) (-1) A := by
      convert (((hasDerivAt_id A).neg.sub_const B).sub_const 1) using 1
    convert hGC.comp A hi using 1
    ring
  have hprod := hleft.mul hright
  have hquot := hprod.div_const (Complex.Gamma (-B))
  unfold hughesYoungGammaBeta
  convert hquot using 1
  ring

/-- Exact right-parameter logarithmic derivative of the Gamma quotient on
the beta half-plane. -/
theorem hasDerivAt_hughesYoungGammaBeta_right
    {A B : ℂ} (hC : 0 < (-A - B - 1).re) (hB : 0 < (-B).re) :
    HasDerivAt (fun z => hughesYoungGammaBeta A z)
      (hughesYoungGammaBeta A B *
        (Complex.digamma (-B) - Complex.digamma (-A - B - 1))) B := by
  have hGC := hasDerivAt_Gamma_eq_mul_digamma_of_re_pos hC
  have hcentral : HasDerivAt (fun z : ℂ => Complex.Gamma (-A - z - 1))
      (-(Complex.Gamma (-A - B - 1) * Complex.digamma (-A - B - 1))) B := by
    have hi : HasDerivAt (fun z : ℂ => -A - z - 1) (-1) B := by
      convert ((((hasDerivAt_id B).const_sub (-A)).sub_const 1)) using 1
    convert hGC.comp B hi using 1
    ring
  have hGB := hasDerivAt_Gamma_eq_mul_digamma_of_re_pos hB
  have hden : HasDerivAt (fun z : ℂ => Complex.Gamma (-z))
      (-(Complex.Gamma (-B) * Complex.digamma (-B))) B := by
    convert hGB.comp B (hasDerivAt_id B).neg using 1
    ring
  have hden0 : Complex.Gamma (-B) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hB
  have hnum := hcentral.const_mul (Complex.Gamma (A + 1))
  have hquot := hnum.div hden hden0
  unfold hughesYoungGammaBeta
  convert hquot using 1
  field_simp [hden0]
  ring

/-- Exact mixed derivative of the Gamma quotient.  The final summand is the
trigamma series created when the two logarithmic derivatives meet. -/
theorem hasDerivAt_hughesYoungGammaBeta_mixed
    {A B : ℂ} (hA : 0 < (A + 1).re) (hC : 0 < (-A - B - 1).re) :
    HasDerivAt (fun z => deriv (fun w => hughesYoungGammaBeta w z) A)
      (hughesYoungGammaBeta A B *
        ((Complex.digamma (-B) - Complex.digamma (-A - B - 1)) *
            (Complex.digamma (A + 1) - Complex.digamma (-A - B - 1)) +
          hughesYoungPolygammaSeries 1 (-A - B - 1))) B := by
  have hB : 0 < (-B).re := by
    have hre : (-B).re = (A + 1).re + (-A - B - 1).re := by
      simp only [neg_re, add_re, one_re, sub_re]
      ring
    rw [hre]
    positivity
  have hG := hasDerivAt_hughesYoungGammaBeta_right hC hB
  have hpsiC0 := hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one hC
  have hinner : HasDerivAt (fun z : ℂ => -A - z - 1) (-1) B := by
    convert ((((hasDerivAt_id B).const_sub (-A)).sub_const 1)) using 1
  have hpsiC : HasDerivAt
      (fun z : ℂ => Complex.digamma (-A - z - 1))
      (-hughesYoungPolygammaSeries 1 (-A - B - 1)) B := by
    convert hpsiC0.comp B hinner using 1
    ring
  have hP : HasDerivAt
      (fun z : ℂ =>
        Complex.digamma (A + 1) - Complex.digamma (-A - z - 1))
      (hughesYoungPolygammaSeries 1 (-A - B - 1)) B := by
    convert hpsiC.const_sub (Complex.digamma (A + 1)) using 1
    ring
  have hExplicit := hG.mul hP
  have hEvent :
      (fun z : ℂ => deriv (fun w => hughesYoungGammaBeta w z) A) =ᶠ[nhds B]
        (fun z => hughesYoungGammaBeta A z *
          (Complex.digamma (A + 1) - Complex.digamma (-A - z - 1))) := by
    have hOpen : IsOpen {z : ℂ | 0 < (-A - z - 1).re} :=
      isOpen_lt continuous_const (Complex.continuous_re.comp (by fun_prop))
    have hMem : B ∈ {z : ℂ | 0 < (-A - z - 1).re} := hC
    filter_upwards [hOpen.eventually_mem hMem] with z hz
    exact (hasDerivAt_hughesYoungGammaBeta_left hA hz).deriv
  have hEvent' :
      (fun z : ℂ => deriv (fun w => hughesYoungGammaBeta w z) A) =ᶠ[nhds B]
        ((fun z => hughesYoungGammaBeta A z) *
          fun z => Complex.digamma (A + 1) -
            Complex.digamma (-A - z - 1)) := by
    simpa only [Pi.mul_apply] using hEvent
  have hActual := hExplicit.congr_of_eventuallyEq hEvent'
  convert hActual using 1
  ring

theorem hughesYoungBetaIntegral_eq_gammaBeta
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    (∫ x in Set.Ioi (0 : ℝ),
      (x : ℂ) ^ A * (1 + (x : ℂ)) ^ B) = hughesYoungGammaBeta A B := by
  have hv : 0 < (-A - B - 1).re := by
    have hs : A.re + B.re + 1 < 0 := by simpa using hAB
    simp only [sub_re, neg_re, one_re]
    linarith
  have h := hughesYoung_betaIntegral_Ioi_eq_gamma
    (u := A + 1) (v := -A - B - 1) hA hv
  unfold hughesYoungGammaBeta
  convert h using 1 <;> ring_nf

theorem eventually_hughesYoungBetaIntegral_eq_gammaBeta_left
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
      (x : ℂ) ^ z * (1 + (x : ℂ)) ^ B) =ᶠ[nhds A]
      fun z => hughesYoungGammaBeta z B := by
  let U : Set ℂ := {z | 0 < (z + 1).re ∧ (z + B + 1).re < 0}
  have hU : IsOpen U := by
    apply IsOpen.inter
    · exact isOpen_lt continuous_const
        (Complex.continuous_re.comp (by fun_prop))
    · exact isOpen_lt
        (Complex.continuous_re.comp (by fun_prop)) continuous_const
  have hAU : A ∈ U := by exact ⟨hA, hAB⟩
  filter_upwards [hU.eventually_mem hAU] with z hz
  exact hughesYoungBetaIntegral_eq_gammaBeta hz.1 hz.2

theorem eventually_hughesYoungBetaIntegral_eq_gammaBeta_right
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    (fun z : ℂ => ∫ x in Set.Ioi (0 : ℝ),
      (x : ℂ) ^ A * (1 + (x : ℂ)) ^ z) =ᶠ[nhds B]
      fun z => hughesYoungGammaBeta A z := by
  let U : Set ℂ := {z | (A + z + 1).re < 0}
  have hU : IsOpen U := isOpen_lt
    (Complex.continuous_re.comp (by fun_prop)) continuous_const
  have hBU : B ∈ U := hAB
  filter_upwards [hU.eventually_mem hBU] with z hz
  exact hughesYoungBetaIntegral_eq_gammaBeta hA hz

/-- On the convergence strip, the first logarithmic beta integral is the
actual first-parameter derivative of the Gamma quotient. -/
theorem hughesYoungLogXBetaIntegral_eq_derivGammaBeta
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    (∫ x in Set.Ioi (0 : ℝ),
      (Real.log x : ℂ) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) =
      deriv (fun z => hughesYoungGammaBeta z B) A := by
  have hi := hasDerivAt_hughesYoungLogXBetaIntegral hA hAB
  have hg := hi.congr_of_eventuallyEq
    (eventually_hughesYoungBetaIntegral_eq_gammaBeta_left hA hAB).symm
  exact hg.deriv.symm

/-- On the convergence strip, the second logarithmic beta integral is the
actual second-parameter derivative of the Gamma quotient. -/
theorem hughesYoungLogOneAddBetaIntegral_eq_derivGammaBeta
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    (∫ x in Set.Ioi (0 : ℝ),
      (Real.log (1 + x) : ℂ) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) =
      deriv (fun z => hughesYoungGammaBeta A z) B := by
  have hi := hasDerivAt_hughesYoungLogOneAddBetaIntegral hA hAB
  have hg := hi.congr_of_eventuallyEq
    (eventually_hughesYoungBetaIntegral_eq_gammaBeta_right hA hAB).symm
  exact hg.deriv.symm

/-- The literal two-logarithm DFI kernel equals the mixed derivative of
the meromorphic Gamma quotient on its source convergence strip. -/
theorem hughesYoungMixedLogBetaIntegral_eq_derivGammaBeta
    {A B : ℂ} (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    (∫ x in Set.Ioi (0 : ℝ),
      (Real.log x : ℂ) * (Real.log (1 + x) : ℂ) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) =
      deriv (fun z => deriv (fun w => hughesYoungGammaBeta w z) A) B := by
  have hm := hasDerivAt_hughesYoungMixedLogBetaIntegral hA hAB
  let U : Set ℂ := {z | (A + z + 1).re < 0}
  have hU : IsOpen U := isOpen_lt
    (Complex.continuous_re.comp (by fun_prop)) continuous_const
  have hBU : B ∈ U := hAB
  have heq : (fun z : ℂ => deriv (fun w => hughesYoungGammaBeta w z) A) =ᶠ[nhds B]
      (fun z => ∫ x in Set.Ioi (0 : ℝ),
        (Real.log x : ℂ) *
          ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ z)) := by
    filter_upwards [hU.eventually_mem hBU] with z hz
    exact (hughesYoungLogXBetaIntegral_eq_derivGammaBeta hA hz).symm
  have hg := hm.congr_of_eventuallyEq heq
  exact hg.deriv.symm

/-- Meromorphic continuation of the complete affine two-logarithm beta
kernel.  `CX` is added to `log x`; `COne` is added to `log (1+x)`. -/
noncomputable def hughesYoungAffineLogBetaContinuation
    (A B CX COne : ℂ) : ℂ :=
  deriv (fun z => deriv (fun w => hughesYoungGammaBeta w z) A) B +
    COne * deriv (fun z => hughesYoungGammaBeta z B) A +
    CX * deriv (fun z => hughesYoungGammaBeta A z) B +
    CX * COne * hughesYoungGammaBeta A B

/-- Closed Gamma--digamma--trigamma formula for the continued equation-(83)
kernel.  Unlike the nested-`deriv` definition, this form exposes the
holomorphic factors and their quantitative vertical growth for the contour
shift to equation (96). -/
theorem hughesYoungAffineLogBetaContinuation_eq_explicit
    {A B CX COne : ℂ}
    (hA : 0 < (A + 1).re) (hC : 0 < (-A - B - 1).re) :
    hughesYoungAffineLogBetaContinuation A B CX COne =
      hughesYoungGammaBeta A B *
        ((Complex.digamma (A + 1) - Complex.digamma (-A - B - 1) + CX) *
            (Complex.digamma (-B) - Complex.digamma (-A - B - 1) + COne) +
          hughesYoungPolygammaSeries 1 (-A - B - 1)) := by
  have hB : 0 < (-B).re := by
    have hre : (-B).re = (A + 1).re + (-A - B - 1).re := by
      simp only [neg_re, add_re, one_re, sub_re]
      ring
    rw [hre]
    positivity
  unfold hughesYoungAffineLogBetaContinuation
  rw [show deriv (fun z => deriv (fun w => hughesYoungGammaBeta w z) A) B =
      hughesYoungGammaBeta A B *
        ((Complex.digamma (-B) - Complex.digamma (-A - B - 1)) *
            (Complex.digamma (A + 1) - Complex.digamma (-A - B - 1)) +
          hughesYoungPolygammaSeries 1 (-A - B - 1)) from
      (hasDerivAt_hughesYoungGammaBeta_mixed hA hC).deriv,
    show deriv (fun z => hughesYoungGammaBeta z B) A =
      hughesYoungGammaBeta A B *
        (Complex.digamma (A + 1) - Complex.digamma (-A - B - 1)) from
      (hasDerivAt_hughesYoungGammaBeta_left hA hC).deriv,
    show deriv (fun z => hughesYoungGammaBeta A z) B =
      hughesYoungGammaBeta A B *
        (Complex.digamma (-B) - Complex.digamma (-A - B - 1)) from
      (hasDerivAt_hughesYoungGammaBeta_right hC hB).deriv]
  ring

/-!
## The equation-(83) critical-line specialization

For the unshifted Hughes--Young moment the two beta exponents are not
independent.  If `s = 1/2 + it`, then the positive-shift branch uses
`A = -(1-s+w)` and `B = -(s+w)`.  Thus the third beta parameter is exactly
`2w`.  The following identity is the cancellation-preserving form used in
the passage from equation (83) to equation (96).
-/

/-- Exact Gamma--digamma--trigamma form of the positive equation-(83)
kernel.  In particular, this proves inside Lean the source substitutions
`A+1 = s-w`, `-B = s+w`, and `-A-B-1 = 2w`; none of those contour-scale
relations is left as an external algebraic convention. -/
theorem hughesYoungAffineLogBetaContinuation_critical_eq_explicit
    {t : ℝ} {w CX COne : ℂ}
    (hLeft : 0 < (afeCriticalPoint t - w).re)
    (hW : 0 < w.re) :
    hughesYoungAffineLogBetaContinuation
        (-(afeCriticalPoint (-t) + w))
        (-(afeCriticalPoint t + w)) CX COne =
      (Complex.Gamma (afeCriticalPoint t - w) *
          Complex.Gamma (2 * w) /
          Complex.Gamma (afeCriticalPoint t + w)) *
        ((Complex.digamma (afeCriticalPoint t - w) -
              Complex.digamma (2 * w) + CX) *
            (Complex.digamma (afeCriticalPoint t + w) -
              Complex.digamma (2 * w) + COne) +
          hughesYoungPolygammaSeries 1 (2 * w)) := by
  have hsum : afeCriticalPoint t + afeCriticalPoint (-t) = 1 := by
    unfold afeCriticalPoint
    push_cast
    ring
  have hA :
      0 < (-(afeCriticalPoint (-t) + w) + 1).re := by
    rw [show -(afeCriticalPoint (-t) + w) + 1 =
        afeCriticalPoint t - w by
      rw [← hsum]
      ring]
    exact hLeft
  have hCentral :
      0 <
        (-(-(afeCriticalPoint (-t) + w)) -
            (-(afeCriticalPoint t + w)) - 1).re := by
    rw [show
      -(-(afeCriticalPoint (-t) + w)) -
          (-(afeCriticalPoint t + w)) - 1 = 2 * w by
        rw [← hsum]
        ring]
    norm_num
    exact hW
  rw [hughesYoungAffineLogBetaContinuation_eq_explicit hA hCentral]
  have hAeq : -(afeCriticalPoint (-t) + w) + 1 =
      afeCriticalPoint t - w := by
    rw [← hsum]
    ring
  have hCeq : -(-(afeCriticalPoint (-t) + w)) -
      (-(afeCriticalPoint t + w)) - 1 = 2 * w := by
    rw [← hsum]
    ring
  have hBeq : -(-(afeCriticalPoint t + w)) =
      afeCriticalPoint t + w := by ring
  unfold hughesYoungGammaBeta
  rw [hAeq, hCeq, hBeq]

/-- Coordinate-swapped form of the preceding identity, used by the
negative-shift half of equation (83). -/
theorem hughesYoungAffineLogBetaContinuation_critical_swapped_eq_explicit
    {t : ℝ} {w CX COne : ℂ}
    (hLeft : 0 < (afeCriticalPoint (-t) - w).re)
    (hW : 0 < w.re) :
    hughesYoungAffineLogBetaContinuation
        (-(afeCriticalPoint t + w))
        (-(afeCriticalPoint (-t) + w)) CX COne =
      (Complex.Gamma (afeCriticalPoint (-t) - w) *
          Complex.Gamma (2 * w) /
          Complex.Gamma (afeCriticalPoint (-t) + w)) *
        ((Complex.digamma (afeCriticalPoint (-t) - w) -
              Complex.digamma (2 * w) + CX) *
            (Complex.digamma (afeCriticalPoint (-t) + w) -
              Complex.digamma (2 * w) + COne) +
          hughesYoungPolygammaSeries 1 (2 * w)) := by
  simpa only [neg_neg] using
    (hughesYoungAffineLogBetaContinuation_critical_eq_explicit
      (t := -t) (w := w) (CX := CX) (COne := COne) hLeft hW)

/-! ## Pole-cancelled Gamma factors for the central contour shift -/

/-- Entire-looking continuation of `z^2 Γ(z)` across the only Gamma pole
met when equation (84) is moved from `Re w < 1/2` to `Re w = 1`. -/
noncomputable def hughesYoungRegularizedGamma (z : ℂ) : ℂ :=
  z * Complex.Gamma (z + 1)

/-- Pole-cancelled continuation of `z^2 Γ(z) ψ(z)`.  The formula is obtained
by differentiating the Gamma recurrence and is expressed only at `z+1`,
whose real part stays positive throughout the Hughes--Young rectangle. -/
noncomputable def hughesYoungRegularizedGammaDigamma (z : ℂ) : ℂ :=
  Complex.Gamma (z + 1) *
    (z * Complex.digamma (z + 1) - 1)

theorem hughesYoungRegularizedGamma_eq
    {z : ℂ} (hz : z ≠ 0) :
    hughesYoungRegularizedGamma z = z ^ 2 * Complex.Gamma z := by
  unfold hughesYoungRegularizedGamma
  rw [Complex.Gamma_add_one z hz]
  ring

theorem hughesYoungRegularizedGammaDigamma_eq
    {z : ℂ} (hzRe : 0 < z.re) :
    hughesYoungRegularizedGammaDigamma z =
      z ^ 2 * Complex.Gamma z * Complex.digamma z := by
  have hz : z ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hpoles : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [neg_re, natCast_re] at hre
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  unfold hughesYoungRegularizedGammaDigamma
  rw [Complex.Gamma_add_one z hz,
    Complex.digamma_apply_add_one z hpoles]
  field_simp [hz]
  ring

/-- Both regularized factors are complex differentiable wherever `z+1`
has positive real part.  This is the exact strip needed for the equation
(84) contour rectangle. -/
theorem differentiableAt_hughesYoungRegularizedGamma
    {z : ℂ} (hz : 0 < (z + 1).re) :
    DifferentiableAt ℂ hughesYoungRegularizedGamma z := by
  have hz' : 0 < z.re + 1 := by simpa using hz
  unfold hughesYoungRegularizedGamma
  exact differentiableAt_id.mul
    ((Complex.differentiableAt_Gamma (z + 1) (fun m hm => by
      have hre := congrArg Complex.re hm
      simp only [add_re, one_re, neg_re, natCast_re] at hre
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)).comp z (differentiableAt_id.add_const 1))

theorem differentiableAt_hughesYoungRegularizedGammaDigamma
    {z : ℂ} (hz : 0 < (z + 1).re) :
    DifferentiableAt ℂ hughesYoungRegularizedGammaDigamma z := by
  have hz' : 0 < z.re + 1 := by simpa using hz
  have hGamma : DifferentiableAt ℂ (fun y : ℂ => Complex.Gamma (y + 1)) z :=
    (Complex.differentiableAt_Gamma (z + 1) (fun m hm => by
      have hre := congrArg Complex.re hm
      simp only [add_re, one_re, neg_re, natCast_re] at hre
      have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith)).comp z (differentiableAt_id.add_const 1)
  have hDigamma : DifferentiableAt ℂ
      (fun y : ℂ => Complex.digamma (y + 1)) z := by
    exact (hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one hz).differentiableAt.comp
      z (differentiableAt_id.add_const 1)
  unfold hughesYoungRegularizedGammaDigamma
  fun_prop

/-- Pole-cancelled equation-(84) beta factor.  Multiplication by
`(s-w)^2` is exactly the zero supplied by the completed-zeta polynomial on
the opposite critical-line factor. -/
noncomputable def hughesYoungEquation84RegularizedBetaKernel
    (t : ℝ) (w CX COne : ℂ) : ℂ :=
  let z := afeCriticalPoint t - w
  let p := afeCriticalPoint t + w
  let U := -Complex.digamma (2 * w) + CX
  let V := Complex.digamma p - Complex.digamma (2 * w) + COne
  Complex.Gamma (2 * w) / Complex.Gamma p *
    (hughesYoungRegularizedGammaDigamma z * V +
      hughesYoungRegularizedGamma z *
        (U * V + hughesYoungPolygammaSeries 1 (2 * w)))

/-- Exact pole-cancellation identity on the original equation-(83)
convergence strip.  The right side remains meaningful when `s-w=0` and is
therefore the function used for the subsequent rectangle shift. -/
theorem sq_mul_hughesYoungEquation84CriticalBetaKernel_eq_regularized
    {t : ℝ} {w CX COne : ℂ}
    (hz : 0 < (afeCriticalPoint t - w).re) :
    (afeCriticalPoint t - w) ^ 2 *
        ((Complex.Gamma (afeCriticalPoint t - w) *
            Complex.Gamma (2 * w) /
            Complex.Gamma (afeCriticalPoint t + w)) *
          ((Complex.digamma (afeCriticalPoint t - w) -
                Complex.digamma (2 * w) + CX) *
              (Complex.digamma (afeCriticalPoint t + w) -
                Complex.digamma (2 * w) + COne) +
            hughesYoungPolygammaSeries 1 (2 * w))) =
      hughesYoungEquation84RegularizedBetaKernel t w CX COne := by
  let z := afeCriticalPoint t - w
  let p := afeCriticalPoint t + w
  let U := -Complex.digamma (2 * w) + CX
  let V := Complex.digamma p - Complex.digamma (2 * w) + COne
  have hz0 : z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [zero_re] at hre
    have hz' : 0 < z.re := by simpa only [z] using hz
    linarith
  have hreg := hughesYoungRegularizedGamma_eq hz0
  have hregPsi := hughesYoungRegularizedGammaDigamma_eq
    (by simpa only [z] using hz)
  unfold hughesYoungEquation84RegularizedBetaKernel
  dsimp only [z, p, U, V] at hreg hregPsi ⊢
  rw [hreg, hregPsi]
  ring

/-- Holomorphy of the pole-cancelled equation-(84) beta factor on the full
rectangle `0 < Re w < 3/2`.  This is the analytic fact that permits the
source contour to cross `Re w = 1/2` without an artificial residue. -/
theorem differentiableAt_hughesYoungEquation84RegularizedBetaKernel
    (t : ℝ) {w CX COne : ℂ}
    (hw : 0 < w.re) (hwUpper : w.re < 3 / 2) :
    DifferentiableAt ℂ
      (fun z => hughesYoungEquation84RegularizedBetaKernel t z CX COne) w := by
  let zfun : ℂ → ℂ := fun y => afeCriticalPoint t - y
  let pfun : ℂ → ℂ := fun y => afeCriticalPoint t + y
  let two : ℂ → ℂ := fun y => 2 * y
  have hzDiff : DifferentiableAt ℂ zfun w := by
    dsimp only [zfun]
    fun_prop
  have hpDiff : DifferentiableAt ℂ pfun w := by
    dsimp only [pfun]
    fun_prop
  have htwoDiff : DifferentiableAt ℂ two w := by
    dsimp only [two]
    fun_prop
  have hzOne : 0 < (zfun w + 1).re := by
    dsimp only [zfun]
    simp [afeCriticalPoint]
    linarith
  have hp : 0 < (pfun w).re := by
    dsimp only [pfun]
    simp [afeCriticalPoint]
    linarith
  have htwo : 0 < (two w).re := by
    dsimp only [two]
    norm_num
    exact hw
  have hReg : DifferentiableAt ℂ
      (fun y => hughesYoungRegularizedGamma (zfun y)) w :=
    (differentiableAt_hughesYoungRegularizedGamma hzOne).comp w hzDiff
  have hRegPsi : DifferentiableAt ℂ
      (fun y => hughesYoungRegularizedGammaDigamma (zfun y)) w :=
    (differentiableAt_hughesYoungRegularizedGammaDigamma hzOne).comp w hzDiff
  have hGammaTwo : DifferentiableAt ℂ
      (fun y => Complex.Gamma (two y)) w :=
    (hasDerivAt_Gamma_eq_mul_digamma_of_re_pos htwo).differentiableAt.comp
      w htwoDiff
  have hGammaP : DifferentiableAt ℂ
      (fun y => Complex.Gamma (pfun y)) w :=
    (hasDerivAt_Gamma_eq_mul_digamma_of_re_pos hp).differentiableAt.comp
      w hpDiff
  have hGammaP0 : Complex.Gamma (pfun w) ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos hp
  have hPsiTwo : DifferentiableAt ℂ
      (fun y => Complex.digamma (two y)) w :=
    (hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one htwo).differentiableAt.comp
      w htwoDiff
  have hPsiP : DifferentiableAt ℂ
      (fun y => Complex.digamma (pfun y)) w :=
    (hasDerivAt_digamma_eq_hughesYoungPolygammaSeries_one hp).differentiableAt.comp
      w hpDiff
  have hPolyTwo : DifferentiableAt ℂ
      (fun y => hughesYoungPolygammaSeries 1 (two y)) w :=
    (hasDerivAt_hughesYoungPolygammaSeries 1 (by norm_num) htwo).differentiableAt.comp
      w htwoDiff
  have hU : DifferentiableAt ℂ
      (fun y => -Complex.digamma (two y) + CX) w :=
    hPsiTwo.neg.add_const CX
  have hV : DifferentiableAt ℂ
      (fun y => Complex.digamma (pfun y) -
        Complex.digamma (two y) + COne) w :=
    (hPsiP.sub hPsiTwo).add_const COne
  have hInner : DifferentiableAt ℂ
      (fun y =>
        hughesYoungRegularizedGammaDigamma (zfun y) *
            (Complex.digamma (pfun y) -
              Complex.digamma (two y) + COne) +
          hughesYoungRegularizedGamma (zfun y) *
            ((-Complex.digamma (two y) + CX) *
                (Complex.digamma (pfun y) -
                  Complex.digamma (two y) + COne) +
              hughesYoungPolygammaSeries 1 (two y))) w :=
    (hRegPsi.mul hV).add (hReg.mul ((hU.mul hV).add hPolyTwo))
  have hAll := (hGammaTwo.div hGammaP hGammaP0).mul hInner
  unfold hughesYoungEquation84RegularizedBetaKernel
  dsimp only [zfun, pfun, two] at hAll ⊢
  exact hAll

/-- On the source convergence strip, the continuation is exactly the
literal affine two-logarithm integral—not merely a formal expression. -/
theorem hughesYoungAffineLogBetaIntegral_eq_continuation
    {A B CX COne : ℂ}
    (hA : 0 < (A + 1).re) (hAB : (A + B + 1).re < 0) :
    (∫ x in Set.Ioi (0 : ℝ),
      ((Real.log x : ℂ) + CX) * ((Real.log (1 + x) : ℂ) + COne) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) =
      hughesYoungAffineLogBetaContinuation A B CX COne := by
  let f₀ : ℝ → ℂ := fun x =>
    (x : ℂ) ^ A * (1 + (x : ℂ)) ^ B
  let fX : ℝ → ℂ := fun x => (Real.log x : ℂ) * f₀ x
  let fOne : ℝ → ℂ := fun x => (Real.log (1 + x) : ℂ) * f₀ x
  let fMix : ℝ → ℂ := fun x =>
    (Real.log x : ℂ) * (Real.log (1 + x) : ℂ) * f₀ x
  have h₀ : IntegrableOn f₀ (Set.Ioi 0) := by
    simpa only [f₀] using integrableOn_hughesYoungBeta hA hAB
  have hX : IntegrableOn fX (Set.Ioi 0) := by
    simpa only [fX, f₀] using integrableOn_hughesYoungLogXBeta hA hAB
  have hOne : IntegrableOn fOne (Set.Ioi 0) := by
    simpa only [fOne, f₀] using integrableOn_hughesYoungLogOneAddBeta hA hAB
  have hMix : IntegrableOn fMix (Set.Ioi 0) := by
    simpa only [fMix, f₀] using integrableOn_hughesYoungMixedLogBeta hA hAB
  have hLeft : IntegrableOn (fun x => fMix x + COne * fX x) (Set.Ioi 0) := by
    simpa only [Pi.add_apply] using hMix.add (hX.const_mul COne)
  have hRight : IntegrableOn
      (fun x => CX * fOne x + CX * COne * f₀ x) (Set.Ioi 0) := by
    simpa only [Pi.add_apply] using
      (hOne.const_mul CX).add (h₀.const_mul (CX * COne))
  have hpoint : (fun x : ℝ =>
      ((Real.log x : ℂ) + CX) * ((Real.log (1 + x) : ℂ) + COne) * f₀ x) =
      fun x => (fMix x + COne * fX x) + (CX * fOne x + CX * COne * f₀ x) := by
    funext x
    dsimp only [fMix, fX, fOne]
    ring
  rw [show (∫ x in Set.Ioi (0 : ℝ),
      ((Real.log x : ℂ) + CX) * ((Real.log (1 + x) : ℂ) + COne) *
        ((x : ℂ) ^ A * (1 + (x : ℂ)) ^ B)) =
      ∫ x in Set.Ioi (0 : ℝ),
        (fMix x + COne * fX x) + (CX * fOne x + CX * COne * f₀ x) by
    change (∫ x in Set.Ioi (0 : ℝ),
      ((Real.log x : ℂ) + CX) * ((Real.log (1 + x) : ℂ) + COne) * f₀ x) = _
    rw [hpoint]]
  change (∫ x in Set.Ioi (0 : ℝ),
    ((fMix + fun x => COne * fX x) +
      ((fun x => CX * fOne x) + fun x => CX * COne * f₀ x)) x) = _
  simp only [Pi.add_apply]
  rw [MeasureTheory.integral_add
      hLeft hRight,
    MeasureTheory.integral_add hMix (hX.const_mul COne),
    MeasureTheory.integral_add (hOne.const_mul CX) (h₀.const_mul (CX * COne))]
  simp only [MeasureTheory.integral_const_mul]
  rw [hughesYoungMixedLogBetaIntegral_eq_derivGammaBeta hA hAB,
    hughesYoungLogXBetaIntegral_eq_derivGammaBeta hA hAB,
    hughesYoungLogOneAddBetaIntegral_eq_derivGammaBeta hA hAB,
    hughesYoungBetaIntegral_eq_gammaBeta hA hAB]
  unfold hughesYoungAffineLogBetaContinuation
  ring

end RiemannZeta.GuthMaynard
