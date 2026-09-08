import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.MellinInversion
import RiemannZeta.GuthMaynard.LargeValuesReflection
import RiemannZeta.GuthMaynard.MediumReflection
import RiemannZeta.GuthMaynard.TypeISmoothing

open Complex Filter MeasureTheory Real Set
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology

namespace RiemannZeta.GuthMaynard

/-!
# Exact smooth Type-I Poisson reflection

This file is the literal analytic bridge from the smooth source block to its
Poisson modes.  Negative Fourier frequency `-m` has phase
`m*x - t/(2π)*log x`; its stationary point is therefore `t/(2πm)`, and the
stationary frequencies have scale `t/(2^r Y)`.
-/

/-! ## Mellin transform of the actual Type-I cutoff

The exact Mellin route is the formal replacement for appealing to an
unavailable black-box stationary-phase theorem.  It keeps the fixed cutoff
as a Schwartz transform and leaves one common logarithmic reflection
integral, which is controlled by the weighted B-process estimate in
`LargeValuesReflection.lean`.
-/

private noncomputable def typeIDyadicCutoffComplex (x : ℝ) : ℂ :=
  (typeIDyadicCutoff x : ℂ)

private theorem contDiff_typeIDyadicCutoffComplex :
    ContDiff ℝ ∞ typeIDyadicCutoffComplex := by
  exact Complex.ofRealCLM.contDiff.comp contDiff_typeIDyadicCutoff

private theorem hasCompactSupport_typeIDyadicCutoffComplex :
    HasCompactSupport typeIDyadicCutoffComplex := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (1 / 2 : ℝ) 2))
  intro x hx
  by_cases hhalf : x ≤ 1 / 2
  · simp [typeIDyadicCutoffComplex,
      typeIDyadicCutoff_eq_zero_of_le_half hhalf]
  · have htwo : 2 ≤ x := by
      by_contra hnot
      exact hx ⟨le_of_not_ge hhalf, le_of_not_ge hnot⟩
    simp [typeIDyadicCutoffComplex,
      typeIDyadicCutoff_eq_zero_of_two_le htwo]

theorem mellinConvergent_typeIDyadicCutoff_one :
    MellinConvergent typeIDyadicCutoffComplex (1 : ℂ) := by
  rw [MellinConvergent]
  have hInt : Integrable typeIDyadicCutoffComplex volume :=
    contDiff_typeIDyadicCutoffComplex.continuous.integrable_of_hasCompactSupport
      hasCompactSupport_typeIDyadicCutoffComplex
  simpa using hInt.integrableOn

/-- Logarithmic-coordinate Schwartz kernel for the literal cutoff used in
the #15 smooth partition. -/
noncomputable def typeIDyadicMellinKernel (u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) * typeIDyadicCutoffComplex (Real.exp (-u))

theorem contDiff_typeIDyadicMellinKernel :
    ContDiff ℝ ∞ typeIDyadicMellinKernel := by
  have hExp : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) :=
    Real.contDiff_exp.comp contDiff_neg
  exact (Complex.ofRealCLM.contDiff.comp hExp).mul
    (contDiff_typeIDyadicCutoffComplex.comp hExp)

theorem hasCompactSupport_typeIDyadicMellinKernel :
    HasCompactSupport typeIDyadicMellinKernel := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact
      (Set.Icc (-Real.log 2) (Real.log 2)))
  intro u hu
  have hcut : typeIDyadicCutoff (Real.exp (-u)) = 0 := by
    by_cases hleft : u < -Real.log 2
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      have hlog : Real.log 2 < -u := by linarith
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact (Real.exp_lt_exp).mpr hlog |>.le
    · have hright : Real.log 2 < u := by
        by_contra hnot
        exact hu ⟨le_of_not_gt hleft, le_of_not_gt hnot⟩
      apply typeIDyadicCutoff_eq_zero_of_le_half
      have hneg : -u < -Real.log 2 := by linarith
      rw [Real.exp_neg]
      have hinv : (Real.exp u)⁻¹ ≤ (2 : ℝ)⁻¹ := by
        apply (inv_le_inv₀ (Real.exp_pos u) (by norm_num : (0 : ℝ) < 2)).2
        rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        exact (Real.exp_lt_exp).mpr hright |>.le
      simpa only [inv_eq_one_div] using hinv
  simp [typeIDyadicMellinKernel, typeIDyadicCutoffComplex, hcut]

/-- Schwartz realization of the logarithmic cutoff. -/
noncomputable def typeIDyadicMellinSchwartz : 𝓢(ℝ, ℂ) :=
  hasCompactSupport_typeIDyadicMellinKernel.toSchwartzMap
    contDiff_typeIDyadicMellinKernel

@[simp]
theorem typeIDyadicMellinSchwartz_apply (u : ℝ) :
    typeIDyadicMellinSchwartz u = typeIDyadicMellinKernel u := rfl

/-- Mellin transform of the fixed Type-I cutoff on `Re s = 1`. -/
noncomputable def typeIDyadicCutoffMellin (r : ℝ) : ℂ :=
  mellin typeIDyadicCutoffComplex ((1 : ℂ) + (r : ℂ) * I)

theorem typeIDyadicCutoffMellin_eq_fourier (r : ℝ) :
    typeIDyadicCutoffMellin r =
      𝓕 typeIDyadicMellinSchwartz (r / (2 * Real.pi)) := by
  unfold typeIDyadicCutoffMellin
  rw [mellin_eq_fourier, SchwartzMap.fourier_coe]
  simp
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (r / (2 * Real.pi)))
  funext u
  rw [typeIDyadicMellinSchwartz_apply]
  simp [typeIDyadicMellinKernel, typeIDyadicCutoffComplex,
    Complex.ofReal_exp]

theorem continuous_typeIDyadicCutoffMellin :
    Continuous typeIDyadicCutoffMellin := by
  have hEq : typeIDyadicCutoffMellin = fun r : ℝ =>
      𝓕 typeIDyadicMellinSchwartz (r / (2 * Real.pi)) := by
    funext r
    exact typeIDyadicCutoffMellin_eq_fourier r
  rw [hEq]
  exact (𝓕 typeIDyadicMellinSchwartz).continuous.comp
    (continuous_id.div_const (2 * Real.pi))

/-- The Mellin transform of the fixed Type-I dyadic cutoff has arbitrary
polynomial decay, uniformly in its vertical ordinate. -/
theorem typeIDyadicCutoffMellin_polynomial_decay (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ,
      |r| ^ n * ‖typeIDyadicCutoffMellin r‖ ≤ C := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 typeIDyadicMellinSchwartz
  let C : ℝ := (2 * Real.pi) ^ n * SchwartzMap.seminorm ℝ n 0 F
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro r
  have hSem := SchwartzMap.le_seminorm' (𝕜 := ℝ) n 0 F
    (r / (2 * Real.pi))
  rw [iteratedDeriv_zero] at hSem
  have hSem' : ‖r / (2 * Real.pi)‖ ^ n *
      ‖F (r / (2 * Real.pi))‖ ≤ SchwartzMap.seminorm ℝ n 0 F := hSem
  rw [typeIDyadicCutoffMellin_eq_fourier]
  change |r| ^ n * ‖F (r / (2 * Real.pi))‖ ≤ C
  have hpi : 0 < 2 * Real.pi := by positivity
  have hAbs : |r| = (2 * Real.pi) * ‖r / (2 * Real.pi)‖ := by
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpi]
    field_simp [hpi.ne']
  rw [hAbs, mul_pow]
  dsimp only [C]
  calc
    (2 * Real.pi) ^ n * ‖r / (2 * Real.pi)‖ ^ n *
          ‖F (r / (2 * Real.pi))‖ =
        (2 * Real.pi) ^ n *
          (‖r / (2 * Real.pi)‖ ^ n * ‖F (r / (2 * Real.pi))‖) := by ring
    _ ≤ (2 * Real.pi) ^ n * SchwartzMap.seminorm ℝ n 0 F :=
      mul_le_mul_of_nonneg_left hSem' (pow_nonneg hpi.le n)

theorem verticalIntegrable_typeIDyadicCutoffMellin :
    VerticalIntegrable (mellin typeIDyadicCutoffComplex) 1 := by
  rw [VerticalIntegrable]
  let F : 𝓢(ℝ, ℂ) := 𝓕 typeIDyadicMellinSchwartz
  have hFourier : Integrable (F : ℝ → ℂ) := F.integrable
  have hScaled : Integrable
      (fun u : ℝ => 𝓕 typeIDyadicMellinSchwartz
        (u / (2 * Real.pi))) := by
    simpa [F, div_eq_mul_inv] using
      hFourier.comp_mul_right'
        (show (2 * Real.pi)⁻¹ ≠ 0 by positivity)
  apply hScaled.congr
  filter_upwards with u
  exact (typeIDyadicCutoffMellin_eq_fourier u).symm

/-- Exact pointwise Mellin inversion for the actual #15 dyadic cutoff. -/
theorem typeIDyadicCutoff_mellinInversion {x : ℝ} (hx : 0 < x) :
    mellinInv 1 (mellin typeIDyadicCutoffComplex) x =
      (typeIDyadicCutoff x : ℂ) := by
  exact mellinInv_mellin_eq 1 typeIDyadicCutoffComplex hx
    mellinConvergent_typeIDyadicCutoff_one
    verticalIntegrable_typeIDyadicCutoffMellin
    contDiff_typeIDyadicCutoffComplex.continuous.continuousAt

/-- Vertical-line form used inside the exact Type-I reflection formula. -/
theorem typeIDyadicCutoff_eq_verticalMellinIntegral
    {x : ℝ} (hx : 0 < x) :
    (typeIDyadicCutoff x : ℂ) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          (x : ℂ) ^ (-((1 : ℂ) + (r : ℂ) * I)) *
            typeIDyadicCutoffMellin r := by
  rw [← typeIDyadicCutoff_mellinInversion hx]
  unfold mellinInv typeIDyadicCutoffMellin
  simp only [smul_eq_mul]
  norm_num

/-- Raw two-variable integrand obtained by inserting exact Mellin inversion
after the change of variables `v = m*x`. -/
noncomputable def typeIMellinReflectionIntegrand
    (sigma t q v r : ℝ) : ℂ :=
  (v / q : ℂ)⁻¹ *
    Complex.exp (-(((r * Real.log (v / q) : ℝ) : ℂ) * I)) *
      typeIDyadicCutoffMellin r *
        (gmReflectionPowerWeight sigma v *
          Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))

/-- Pointwise insertion of the literal cutoff's Mellin inversion into the
rescaled logarithmic phase. -/
theorem typeIDyadicCutoffPhase_eq_mellinIntegral
    (sigma t q : ℝ) {v : ℝ} (hv : 0 < v) (hq : 0 < q) :
    (typeIDyadicCutoff (v / q) : ℂ) *
        (gmReflectionPowerWeight sigma v *
          Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ, typeIMellinReflectionIntegrand sigma t q v r := by
  have hratio : 0 < v / q := div_pos hv hq
  rw [typeIDyadicCutoff_eq_verticalMellinIntegral hratio]
  rw [smul_mul_assoc]
  congr 1
  rw [← MeasureTheory.integral_mul_const]
  congr 1
  funext r
  unfold typeIMellinReflectionIntegrand typeIDyadicCutoffMellin
  rw [Complex.cpow_def_of_ne_zero
    (Complex.ofReal_ne_zero.mpr hratio.ne')]
  rw [← Complex.ofReal_log hratio.le]
  have hExpLog :
      Complex.exp ((Real.log (v / q) : ℝ) : ℂ) = (v / q : ℝ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hratio]
  have hsplit :
      (Real.log (v / q) : ℂ) * -((1 : ℂ) + (r : ℂ) * I) =
        -(Real.log (v / q) : ℂ) +
          -(((r * Real.log (v / q) : ℝ) : ℂ) * I) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_neg, hExpLog]
  have hRatioInv : (((v / q : ℝ) : ℂ))⁻¹ =
      (q : ℂ) * (v : ℂ)⁻¹ := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  have hRatioInvC : ((v : ℂ) / (q : ℂ))⁻¹ =
      (q : ℂ) * (v : ℂ)⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  rw [hRatioInv]
  rw [hRatioInvC]

/-- Algebraic factorization of the raw Mellin integrand.  All dependence on
the cutoff dilation `q` is outside the common weighted logarithmic kernel. -/
theorem typeIMellinReflectionIntegrand_eq_factored
    (sigma t : ℝ) {q v : ℝ} (r : ℝ) (hq : 0 < q) (hv : 0 < v) :
    typeIMellinReflectionIntegrand sigma t q v r =
      (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
        typeIDyadicCutoffMellin r *
          (gmReflectionPowerWeight sigma v *
            star ((v : ℂ)⁻¹ * Complex.exp
              (((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
  unfold typeIMellinReflectionIntegrand
  have hlog : Real.log (v / q) = Real.log v - Real.log q :=
    Real.log_div hv.ne' hq.ne'
  rw [hlog]
  have hRatioInv : ((v : ℂ) / (q : ℂ))⁻¹ =
      (q : ℂ) * (v : ℂ)⁻¹ := by
    field_simp [Complex.ofReal_ne_zero.mpr hq.ne',
      Complex.ofReal_ne_zero.mpr hv.ne']
  rw [hRatioInv]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hq.ne')]
  rw [← Complex.ofReal_log hq.le]
  have hstar :
      star ((v : ℂ)⁻¹ * Complex.exp
        (((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
        (v : ℂ)⁻¹ * Complex.exp
          (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
    rw [Complex.star_def, map_mul, map_inv₀, conj_ofReal,
      ← Complex.exp_conj]
    congr 1
    simp only [map_mul, conj_ofReal, conj_I]
    push_cast
    ring_nf
  rw [hstar]
  have hExpEq :
      Complex.exp (-(((r * (Real.log v - Real.log q) : ℝ) : ℂ) * I)) *
          Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) =
        Complex.exp ((Real.log q : ℂ) * ((r : ℂ) * I)) *
          Complex.exp
            (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  calc
    (q : ℂ) * (v : ℂ)⁻¹ *
          Complex.exp (-(((r * (Real.log v - Real.log q) : ℝ) : ℂ) * I)) *
          typeIDyadicCutoffMellin r *
          (gmReflectionPowerWeight sigma v *
            Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) =
        (q : ℂ) * (v : ℂ)⁻¹ * typeIDyadicCutoffMellin r *
          gmReflectionPowerWeight sigma v *
          (Complex.exp (-(((r * (Real.log v - Real.log q) : ℝ) : ℂ) * I)) *
            Complex.exp (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
      ring
    _ = (q : ℂ) * (v : ℂ)⁻¹ * typeIDyadicCutoffMellin r *
          gmReflectionPowerWeight sigma v *
          (Complex.exp ((Real.log q : ℂ) * ((r : ℂ) * I)) *
            Complex.exp
              (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
      rw [hExpEq]
    _ = (q : ℂ) * Complex.exp ((Real.log q : ℂ) * ((r : ℂ) * I)) *
          typeIDyadicCutoffMellin r *
          (gmReflectionPowerWeight sigma v *
            ((v : ℂ)⁻¹ * Complex.exp
              (-(((((t + r) * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))) := by
      ring

/-- Absolute integrability needed to exchange the finite physical interval
with the complete Mellin line.  Compactness of the physical interval and
Schwartz decay of the literal cutoff are both used explicitly. -/
theorem integrable_typeIMellinReflectionIntegrand
    {sigma t q A B : ℝ} (hsigma : 0 ≤ sigma) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    Integrable (Function.uncurry
      (typeIMellinReflectionIntegrand sigma t q))
      ((volume.restrict (Set.uIoc A B)).prod volume) := by
  have hH : Integrable typeIDyadicCutoffMellin := by
    simpa only [typeIDyadicCutoffMellin, VerticalIntegrable] using
      verticalIntegrable_typeIDyadicCutoffMellin
  let C : ℝ := (q / A) * A ^ (-sigma)
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hConst : Integrable (fun _v : ℝ => C)
      (volume.restrict (Set.uIoc A B)) := by
    exact MeasureTheory.integrableOn_const (hs := by simp)
  have hDom := hConst.mul_prod hH.norm
  apply hDom.mono'
  · have hElementary : AEStronglyMeasurable
        (fun z : ℝ × ℝ =>
          (z.1 / q : ℂ)⁻¹ *
            Complex.exp (-(((z.2 * Real.log (z.1 / q) : ℝ) : ℂ) * I)) *
              (gmReflectionPowerWeight sigma z.1 *
                Complex.exp
                  (-((((t * Real.log z.1 - 2 * Real.pi * z.1 : ℝ) : ℂ) * I)))))
        ((volume.restrict (Set.uIoc A B)).prod volume) := by
      apply StronglyMeasurable.aestronglyMeasurable
      unfold gmReflectionPowerWeight
      measurability
    exact (hElementary.mul (hH.aestronglyMeasurable.comp_snd)).congr
      (Filter.Eventually.of_forall fun z => by
        simp [typeIMellinReflectionIntegrand, Function.uncurry_def]
        ring)
  · rw [Measure.ae_prod_iff_ae_ae (by
      apply measurableSet_le
      · have hHM : Measurable fun z : ℝ × ℝ =>
            typeIDyadicCutoffMellin z.2 :=
          continuous_typeIDyadicCutoffMellin.measurable.comp measurable_snd
        unfold typeIMellinReflectionIntegrand Function.uncurry
        unfold gmReflectionPowerWeight
        measurability
      · exact ((continuous_typeIDyadicCutoffMellin.norm.comp continuous_snd
          |>.const_mul C)).measurable)]
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with v hv
    filter_upwards with r
    have hvIoc : v ∈ Set.Ioc A B := by
      simpa only [Set.uIoc_of_le hAB] using hv
    have hvPos : 0 < v := hA.trans hvIoc.1
    have hqv : q / v ≤ q / A := by
      exact div_le_div_of_nonneg_left hq.le hA hvIoc.1.le
    have hpow : v ^ (-sigma) ≤ A ^ (-sigma) := by
      exact Real.rpow_le_rpow_of_nonpos hA hvIoc.1.le (by linarith)
    have hNormRatio : ‖(v : ℂ) / (q : ℂ)‖⁻¹ = q / v := by
      rw [norm_div, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hvPos,
        abs_of_pos hq, inv_div]
    have hNormMellinPhase :
        ‖Complex.exp (-(((r * Real.log (v / q) : ℝ) : ℂ) * I))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    have hNormReflectionPhase :
        ‖Complex.exp
          (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [show ‖Function.uncurry
        (typeIMellinReflectionIntegrand sigma t q) (v, r)‖ =
        (q / v) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) by
      unfold typeIMellinReflectionIntegrand Function.uncurry
      simp only [norm_mul, norm_inv]
      rw [hNormRatio, hNormMellinPhase, hNormReflectionPhase,
        norm_gmReflectionPowerWeight hvPos]
      ring]
    change (q / v) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) ≤
      C * ‖typeIDyadicCutoffMellin r‖
    dsimp only [C]
    calc
      (q / v) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) ≤
          (q / A) * ‖typeIDyadicCutoffMellin r‖ * v ^ (-sigma) := by
        gcongr
      _ ≤ (q / A) * ‖typeIDyadicCutoffMellin r‖ * A ^ (-sigma) := by
        gcongr
      _ = q / A * A ^ (-sigma) * ‖typeIDyadicCutoffMellin r‖ := by
        ring

/-- Common conjugated power-weighted reflection integral produced by the
exact Mellin transform. -/
noncomputable def typeIPowerReflectionIntegral
    (sigma tau A B : ℝ) : ℂ :=
  ∫ v in A..B,
    gmReflectionPowerWeight sigma v *
      star ((v : ℂ)⁻¹ * Complex.exp
        (((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))

/-- Uniform weighted B-process bound for the common integral in the exact
Mellin reflection formula. -/
theorem norm_typeIPowerReflectionIntegral_le
    {sigma tau A B : ℝ} (htau : 1 ≤ tau)
    (hA : 0 < A) (hAB : A ≤ B) :
    ‖typeIPowerReflectionIntegral sigma tau A B‖ ≤
      (10 / Real.sqrt tau) *
        (B ^ (-sigma) +
          ∫ v in A..B,
            ‖(((-sigma / v : ℝ) : ℂ) *
              gmReflectionPowerWeight sigma v)‖) := by
  simpa only [typeIPowerReflectionIntegral] using
    norm_conj_powerWeighted_gmReflectionIntegral_le htau hA hAB

/-- Exact Mellin form of the rescaled medium Type-I integral.  The right
side has one common weighted logarithmic reflection integral; the mode scale
`q` appears only in explicit unitary/Mellin factors. -/
theorem typeIDyadicRescaledIntegral_eq_mellinReflection
    {sigma t q A B : ℝ} (hsigma : 0 ≤ sigma) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    (∫ v in A..B,
        (typeIDyadicCutoff (v / q) : ℂ) *
          (gmReflectionPowerWeight sigma v *
            Complex.exp
              (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r) A B := by
  calc
    (∫ v in A..B,
        (typeIDyadicCutoff (v / q) : ℂ) *
          (gmReflectionPowerWeight sigma v *
            Complex.exp
              (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))))) =
      ∫ v in A..B,
        (1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ, typeIMellinReflectionIntegrand sigma t q v r := by
        apply intervalIntegral.integral_congr
        intro v hv
        have hvIcc : v ∈ Set.Icc A B := by
          simpa only [Set.uIcc_of_le hAB] using hv
        exact typeIDyadicCutoffPhase_eq_mellinIntegral sigma t q
          (hA.trans_le hvIcc.1) hq
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ v in A..B,
          ∫ r : ℝ, typeIMellinReflectionIntegrand sigma t q v r := by
        rw [intervalIntegral.integral_smul]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ∫ v in A..B, typeIMellinReflectionIntegrand sigma t q v r := by
        rw [MeasureTheory.intervalIntegral_integral_swap
          (integrable_typeIMellinReflectionIntegrand hsigma hq hA hAB)]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r) A B := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with r
        unfold typeIPowerReflectionIntegral
        rw [← intervalIntegral.integral_const_mul]
        apply intervalIntegral.integral_congr
        intro v hv
        have hvIcc : v ∈ Set.Icc A B := by
          simpa only [Set.uIcc_of_le hAB] using hv
        exact typeIMellinReflectionIntegrand_eq_factored sigma t r hq
          (hA.trans_le hvIcc.1)

/-- Explicit Jacobian and logarithmic scale factor in `v = m*x`. -/
noncomputable def typeIReflectionScaleFactor
    (sigma t m : ℝ) : ℂ :=
  ((m : ℂ)⁻¹ *
    Complex.exp (((sigma * Real.log m : ℝ) : ℂ))) *
      Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))

/-- Physical cutoff integrand at Fourier frequency `m`. -/
noncomputable def typeIDyadicPhysicalIntegrand
    (sigma t m Q x : ℝ) : ℂ :=
  (typeIDyadicCutoff (x / Q) : ℂ) *
    (gmReflectionPowerWeight sigma x *
      Complex.exp
        (-((((t * Real.log x - 2 * Real.pi * m * x : ℝ) : ℂ) * I))))

/-- Exact physical-to-reflected rescaling before Mellin inversion. -/
theorem typeIDyadicPhysicalIntegral_rescale
    {sigma t m Q A B : ℝ} (hm : 0 < m) (hQ : 0 < Q)
    (hA : 0 < A) (hAB : A ≤ B) :
    (∫ x in A..B, typeIDyadicPhysicalIntegrand sigma t m Q x) =
      typeIReflectionScaleFactor sigma t m *
        ∫ v in m * A..m * B,
          typeIDyadicPhysicalIntegrand sigma t 1 (m * Q) v := by
  let g : ℝ → ℂ := typeIDyadicPhysicalIntegrand sigma t 1 (m * Q)
  have hPointwise : ∀ x ∈ Set.uIcc A B,
      typeIDyadicPhysicalIntegrand sigma t m Q x =
        (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) * g (m * x) := by
    intro x hx
    have hxIcc : x ∈ Set.Icc A B := by
      simpa only [Set.uIcc_of_le hAB] using hx
    have hxPos : 0 < x := hA.trans_le hxIcc.1
    have hlog : Real.log (m * x) = Real.log m + Real.log x :=
      Real.log_mul hm.ne' hxPos.ne'
    have hcut : m * x / (m * Q) = x / Q := by
      field_simp [hm.ne', hQ.ne']
    dsimp only [g]
    unfold typeIDyadicPhysicalIntegrand gmReflectionPowerWeight
    rw [hcut]
    rw [hlog]
    have hSigmaEq :
        Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
            Complex.exp (((-sigma * (Real.log m + Real.log x) : ℝ) : ℂ)) =
          Complex.exp (((-sigma * Real.log x : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hPhaseEq :
        Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I)) *
            Complex.exp
              (-((((t * (Real.log m + Real.log x) -
                2 * Real.pi * 1 * (m * x) : ℝ) : ℂ) * I))) =
          Complex.exp
            (-((((t * Real.log x - 2 * Real.pi * m * x : ℝ) : ℂ) * I))) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← hSigmaEq, ← hPhaseEq]
    ring
  have hChange := intervalIntegral.integral_comp_mul_left g hm.ne'
    (a := A) (b := B)
  calc
    (∫ x in A..B, typeIDyadicPhysicalIntegrand sigma t m Q x) =
      ∫ x in A..B,
        (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) * g (m * x) := by
        apply intervalIntegral.integral_congr
        exact hPointwise
    _ = (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) *
        ∫ x in A..B, g (m * x) := by
      rw [intervalIntegral.integral_const_mul]
    _ = (Complex.exp (((sigma * Real.log m : ℝ) : ℂ)) *
          Complex.exp ((((t * Real.log m : ℝ) : ℂ) * I))) *
        ((m : ℝ)⁻¹ • ∫ v in m * A..m * B, g v) := by
      rw [hChange]
    _ = typeIReflectionScaleFactor sigma t m *
        ∫ v in m * A..m * B,
          typeIDyadicPhysicalIntegrand sigma t 1 (m * Q) v := by
      unfold typeIReflectionScaleFactor
      simp only [Complex.real_smul]
      dsimp only [g]
      push_cast
      ring

/-- Exact Mellin-reflected formula for a physical dyadic Fourier mode. -/
theorem typeIDyadicPhysicalIntegral_eq_mellinReflection
    {sigma t m Q A B : ℝ} (hsigma : 0 ≤ sigma)
    (hm : 0 < m) (hQ : 0 < Q) (hA : 0 < A) (hAB : A ≤ B) :
    (∫ x in A..B, typeIDyadicPhysicalIntegrand sigma t m Q x) =
      typeIReflectionScaleFactor sigma t m *
        ((1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            ((m * Q : ℝ) : ℂ) *
              ((m * Q : ℝ) : ℂ) ^ ((r : ℂ) * I) *
                typeIDyadicCutoffMellin r *
                  typeIPowerReflectionIntegral sigma (t + r)
                    (m * A) (m * B)) := by
  rw [typeIDyadicPhysicalIntegral_rescale hm hQ hA hAB]
  congr 1
  have hFun : typeIDyadicPhysicalIntegrand sigma t 1 (m * Q) =
      fun v : ℝ =>
        (typeIDyadicCutoff (v / (m * Q)) : ℂ) *
          (gmReflectionPowerWeight sigma v *
            Complex.exp
              (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
    funext v
    unfold typeIDyadicPhysicalIntegrand
    congr 3
    ring_nf
  rw [hFun]
  exact typeIDyadicRescaledIntegral_eq_mellinReflection hsigma
    (mul_pos hm hQ) (mul_pos hm hA)
    (mul_le_mul_of_nonneg_left hAB hm.le)

/-- A rescaled dyadic integrand is supported strictly between `q/2` and
`2*q`.  Consequently any larger positive interval may be used for its
integral.  This is the support statement that lets all critical Poisson modes
share one reflection interval. -/
theorem integral_typeIDyadicPhysicalIntegrand_eq_interval
    {sigma t q L U : ℝ} (hq : 0 < q)
    (hL : L ≤ q / 2) (hU : 2 * q ≤ U) :
    (∫ v : ℝ, typeIDyadicPhysicalIntegrand sigma t 1 q v) =
      ∫ v in L..U, typeIDyadicPhysicalIntegrand sigma t 1 q v := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro v hv
  have hcut : typeIDyadicCutoff (v / q) ≠ 0 := by
    intro hzero
    apply hv
    simp [typeIDyadicPhysicalIntegrand, hzero]
  have hlower : 1 / 2 < v / q := by
    by_contra hnot
    exact hcut (typeIDyadicCutoff_eq_zero_of_le_half (le_of_not_gt hnot))
  have hupper : v / q < 2 := by
    by_contra hnot
    exact hcut (typeIDyadicCutoff_eq_zero_of_two_le (le_of_not_gt hnot))
  rw [Set.mem_Ioc]
  constructor
  · have hqhalf : q / 2 < v := by
      have hscaled := (lt_div_iff₀ hq).mp hlower
      nlinarith
    exact hL.trans_lt hqhalf
  · exact ((div_lt_iff₀ hq).mp hupper).le.trans hU

/-- Exact medium Type-I reflection with a mode-independent integration
interval.  For every `1 ≤ m ≤ M`, the change of variables `v = m*x` puts the
support inside `[Q/2, 2*M*Q]`; Mellin inversion then leaves the mode only in
explicit algebraic factors. -/
theorem typeIDyadicPhysicalIntegral_eq_common_mellinReflection
    {sigma t Q : ℝ} {m M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hm : 1 ≤ m) (hmM : m ≤ M) :
    (∫ x in Q / 2..2 * Q,
        typeIDyadicPhysicalIntegrand sigma t m Q x) =
      typeIReflectionScaleFactor sigma t m *
        ((1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            (((m : ℝ) * Q : ℝ) : ℂ) *
              (((m : ℝ) * Q : ℝ) : ℂ) ^ ((r : ℂ) * I) *
                typeIDyadicCutoffMellin r *
                  typeIPowerReflectionIntegral sigma (t + r)
                    (Q / 2) (2 * M * Q)) := by
  have hmPosNat : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hmPos : (0 : ℝ) < m := by exact_mod_cast hmPosNat
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hMPos : (0 : ℝ) < M := by exact_mod_cast hmPosNat.trans_le hmM
  rw [typeIDyadicPhysicalIntegral_rescale hmPos hQ (by positivity)
    (by linarith)]
  congr 1
  have hNatural :
      (∫ v : ℝ,
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v) =
        ∫ v in (m : ℝ) * (Q / 2)..(m : ℝ) * (2 * Q),
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v := by
    apply integral_typeIDyadicPhysicalIntegrand_eq_interval (mul_pos hmPos hQ)
    · exact le_of_eq (by ring)
    · exact le_of_eq (by ring)
  have hmMReal : (m : ℝ) ≤ M := by exact_mod_cast hmM
  have hCommon :
      (∫ v : ℝ,
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v) =
        ∫ v in Q / 2..2 * M * Q,
          typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) v := by
    apply integral_typeIDyadicPhysicalIntegrand_eq_interval (mul_pos hmPos hQ)
    · have hscale := mul_le_mul_of_nonneg_right hmOne hQ.le
      nlinarith
    · nlinarith
  rw [← hNatural, hCommon]
  have hFun : typeIDyadicPhysicalIntegrand sigma t 1 ((m : ℝ) * Q) =
      fun v : ℝ =>
        (typeIDyadicCutoff (v / ((m : ℝ) * Q)) : ℂ) *
          (gmReflectionPowerWeight sigma v *
            Complex.exp
              (-((((t * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I)))) := by
    funext v
    unfold typeIDyadicPhysicalIntegrand
    congr 3
    ring_nf
  rw [hFun]
  exact typeIDyadicRescaledIntegral_eq_mellinReflection hsigma
    (mul_pos hmPos hQ) (by positivity) (by
      have hMOne : (1 : ℝ) ≤ M := hmOne.trans hmMReal
      have hscale := mul_le_mul_of_nonneg_right hMOne hQ.le
      nlinarith)

/-- One mode of the exact common Mellin-reflection integrand. -/
noncomputable def typeICommonMellinMode
    (sigma t q A B r : ℝ) : ℂ :=
  (q : ℂ) * (q : ℂ) ^ ((r : ℂ) * I) *
    typeIDyadicCutoffMellin r *
      typeIPowerReflectionIntegral sigma (t + r) A B

theorem intervalIntegral_typeIMellinReflectionIntegrand_eq_commonMode
    {sigma t q A B : ℝ} (r : ℝ) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    (∫ v in A..B, typeIMellinReflectionIntegrand sigma t q v r) =
      typeICommonMellinMode sigma t q A B r := by
  unfold typeICommonMellinMode typeIPowerReflectionIntegral
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  have hvIcc : v ∈ Set.Icc A B := by
    simpa only [Set.uIcc_of_le hAB] using hv
  exact typeIMellinReflectionIntegrand_eq_factored sigma t r hq
    (hA.trans_le hvIcc.1)

theorem integrable_typeICommonMellinMode
    {sigma t q A B : ℝ} (hsigma : 0 ≤ sigma) (hq : 0 < q)
    (hA : 0 < A) (hAB : A ≤ B) :
    Integrable (typeICommonMellinMode sigma t q A B) := by
  have hJoint := integrable_typeIMellinReflectionIntegrand
    (sigma := sigma) (t := t) (q := q) (A := A) (B := B)
    hsigma hq hA hAB
  have hInner : Integrable (fun r : ℝ =>
      ∫ v in A..B, typeIMellinReflectionIntegrand sigma t q v r) := by
    have h := hJoint.integral_prod_right
    simpa only [intervalIntegral.integral_of_le hAB,
      Set.uIoc_of_le hAB, Function.uncurry_apply_pair] using h
  apply hInner.congr
  filter_upwards with r
  exact intervalIntegral_typeIMellinReflectionIntegrand_eq_commonMode
    r hq hA hAB

/-- The finite coefficient polynomial produced by exact medium reflection.
The coefficients are independent of the original ordinate except for the
standard unit-modulus Dirichlet phase. -/
noncomputable def typeIReflectedMellinPolynomial
    (sigma t Q : ℝ) (M : ℕ) (r : ℝ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    typeIReflectionScaleFactor sigma t m *
      (((m : ℝ) * Q : ℝ) : ℂ) *
        (((m : ℝ) * Q : ℝ) : ℂ) ^ ((r : ℂ) * I)

/-- Exact finite B-process assembly.  A whole block of critical modes is one
Mellin integral of a fixed finite Dirichlet polynomial against the common
oscillatory kernel.  No pointwise stationary-phase approximation or hidden
error term remains. -/
theorem sum_typeIDyadicPhysicalIntegral_eq_reflectedMellinPolynomial
    {sigma t Q : ℝ} {M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    (∑ m ∈ Finset.Icc 1 M,
        ∫ x in Q / 2..2 * Q,
          typeIDyadicPhysicalIntegrand sigma t m Q x) =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q) := by
  let S := Finset.Icc 1 M
  let A : ℝ := Q / 2
  let B : ℝ := 2 * M * Q
  have hA : 0 < A := by dsimp only [A]; positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    have hMOne : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hscale := mul_le_mul_of_nonneg_right hMOne hQ.le
    nlinarith
  have hModeInt : ∀ m ∈ S,
      Integrable (fun r : ℝ =>
        typeIReflectionScaleFactor sigma t m *
          typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r) := by
    intro m hmS
    have hmRange : 1 ≤ m ∧ m ≤ M := Finset.mem_Icc.mp hmS
    have hmPos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hmRange.1)
    exact (integrable_typeICommonMellinMode hsigma (mul_pos hmPos hQ)
      hA hAB).const_mul _
  calc
    (∑ m ∈ Finset.Icc 1 M,
        ∫ x in Q / 2..2 * Q,
          typeIDyadicPhysicalIntegrand sigma t m Q x) =
      ∑ m ∈ S,
        (1 / (2 * Real.pi) : ℝ) •
          ∫ r : ℝ,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        apply Finset.sum_congr rfl
        intro m hmS
        have hmRange : 1 ≤ m ∧ m ≤ M := Finset.mem_Icc.mp hmS
        rw [typeIDyadicPhysicalIntegral_eq_common_mellinReflection
          hsigma hQ hmRange.1 hmRange.2]
        unfold typeICommonMellinMode A B
        simp only [Complex.real_smul]
        rw [MeasureTheory.integral_const_mul]
        ring
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∑ m ∈ S,
          ∫ r : ℝ,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        rw [Finset.smul_sum]
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          ∑ m ∈ S,
            typeIReflectionScaleFactor sigma t m *
              typeICommonMellinMode sigma t ((m : ℝ) * Q) A B r := by
        congr 1
        exact (MeasureTheory.integral_finsetSum S hModeInt).symm
    _ = (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma t Q M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                (Q / 2) (2 * M * Q) := by
        congr 1
        apply MeasureTheory.integral_congr_ae
        filter_upwards with r
        dsimp only [S, A, B]
        unfold typeIReflectedMellinPolynomial typeICommonMellinMode
        rw [Finset.sum_mul, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro m hm
        ring

/-- Continuous compactly supported interpolation of a smooth Type-I block. -/
noncomputable def typeIReflectionKernel
    (Y A r : ℕ) (σ t x : ℝ) : ℂ :=
  (typeISourceSmoothWeight Y A r x : ℂ) *
    Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
    Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * I))

theorem contDiff_typeIReflectionKernel
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) :
    ContDiff ℝ ∞ (typeIReflectionKernel Y A r σ t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
    have hEventually : typeIReflectionKernel Y A r σ t =ᶠ[𝓝 0] 0 := by
      filter_upwards [Iio_mem_nhds hYreal] with y hy
      have hy' : y < (Y : ℝ) := hy
      have hleft : Real.smoothTransition (y - (Y : ℝ)) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      simp [typeIReflectionKernel, typeISourceSmoothWeight,
        typeITailBoundary, hleft]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hweight : ContDiffAt ℝ ∞
        (fun y : ℝ => (typeISourceSmoothWeight Y A r y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (contDiff_typeISourceSmoothWeight Y A r).contDiffAt
    have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.2 hx
    have hsigma : ContDiffAt ℝ ∞
        (fun y : ℝ => (((-σ * Real.log y : ℝ) : ℂ))) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (contDiffAt_const.mul hlog)
    have ht : ContDiffAt ℝ ∞
        (fun y : ℝ => (((-t * Real.log y : ℝ) : ℂ) * I)) x :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (contDiffAt_const.mul hlog)).mul contDiffAt_const
    exact (hweight.mul hsigma.cexp).mul ht.cexp

theorem hasCompactSupport_typeIReflectionKernel
    (Y A r : ℕ) (σ t : ℝ) :
    HasCompactSupport (typeIReflectionKernel Y A r σ t) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (A + 1)))
  intro x hx
  have hboundary : typeITailBoundary Y A x = 0 := by
    rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · have hleft : Real.smoothTransition (x - (Y : ℝ)) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by
          have hYnonneg : (0 : ℝ) ≤ Y := by positivity
          linarith)
      rw [typeITailBoundary, hleft, zero_mul]
    · have hx' : (((A + 1 : ℕ) : ℝ)) ≤ x := by
        push_cast
        exact le_of_not_ge hx
      have hright : Real.smoothTransition
          (((A + 1 : ℕ) : ℝ) - x) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      rw [typeITailBoundary, hright, mul_zero]
  simp [typeIReflectionKernel, typeISourceSmoothWeight, hboundary]

/-- Schwartz realization of the smooth Type-I kernel. -/
noncomputable def typeIReflectionSchwartz
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeIReflectionKernel Y A r σ t).toSchwartzMap
    (contDiff_typeIReflectionKernel Y A r σ t hY)

@[simp]
theorem typeIReflectionSchwartz_apply
    (Y A r : ℕ) (σ t x : ℝ) (hY : 0 < Y) :
    typeIReflectionSchwartz Y A r σ t hY x =
      typeIReflectionKernel Y A r σ t x := rfl

/-- Fourier mode of the smooth Type-I block. -/
noncomputable def typeIReflectionFourier
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) (ξ : ℝ) : ℂ :=
  𝓕 (typeIReflectionSchwartz Y A r σ t hY) ξ

/-- Literal Poisson expansion of the smooth block. -/
theorem typeIReflection_poisson
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) :
    ∑' n : ℤ, typeIReflectionKernel Y A r σ t n =
      ∑' m : ℤ, typeIReflectionFourier Y A r σ t hY m := by
  simpa [typeIReflectionFourier] using
    (SchwartzMap.tsum_eq_tsum_fourier
      (typeIReflectionSchwartz Y A r σ t hY) 0)

/-- Every fixed source block has arbitrary-order Fourier decay.  This is the
non-uniform Schwartz bound underlying the complete Poisson tail; the missing
medium Type-I theorem is precisely the parameter-uniform specialization at
the source cutoff `T^ε T/Q`. -/
theorem typeIReflectionFourier_fixed_decay
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      |ξ| ^ j * ‖typeIReflectionFourier Y A r σ t hY ξ‖ ≤ C := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 (typeIReflectionSchwartz Y A r σ t hY)
  obtain ⟨C, hC, hbound⟩ := F.decay j 0
  refine ⟨C, hC, ?_⟩
  intro ξ
  simpa [F, typeIReflectionFourier, Real.norm_eq_abs] using hbound ξ

/-- Absolute summability of the complete integer Poisson series for a fixed
source block.  This justifies an exact finite critical-window/remainder
decomposition without postulating any tail estimate. -/
theorem typeIReflectionFourier_summable
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) :
    Summable (fun m : ℤ =>
      typeIReflectionFourier Y A r σ t hY m) := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 (typeIReflectionSchwartz Y A r σ t hY)
  have hBigO := F.isBigO_cocompact_rpow (-2)
  have hSummable : Summable (fun m : ℤ => F (m : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hBigO.comp_tendsto Int.tendsto_coe_cofinite)
  simpa only [F, typeIReflectionFourier,
    SchwartzMap.fourierTransformCLM_apply] using hSummable

/-- At positive integers the continuous kernel is exactly the source block
summand. -/
theorem typeIReflectionKernel_natCast
    (Y A r n : ℕ) (σ t : ℝ) (hn : 0 < n) :
    typeIReflectionKernel Y A r σ t n =
      typeISourceSmoothWeight Y A r n *
        (n : ℂ) ^ (-(σ : ℂ)) * (n : ℂ) ^ (-(t : ℂ) * I) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hbase : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  rw [hbase]
  unfold typeIReflectionKernel
  rw [Complex.cpow_def_of_ne_zero (hbase ▸ hnNe),
    Complex.cpow_def_of_ne_zero (hbase ▸ hnNe),
    ← Complex.ofReal_log hnReal.le]
  simp only [ofReal_neg, ofReal_mul]
  ring_nf

/-- The negative frequency `-m` is the source logarithmic stationary phase,
with every nonoscillatory factor kept outside the exponential. -/
theorem typeIReflectionFourier_neg_eq_stationaryIntegral
    (Y A r : ℕ) (σ t m : ℝ) (hY : 0 < Y) :
    typeIReflectionFourier Y A r σ t hY (-m) =
      ∫ x : ℝ,
        (typeISourceSmoothWeight Y A r x : ℂ) *
          Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
          Complex.exp (2 * Real.pi * I *
            ((reflectionPhase t m x : ℝ) : ℂ)) := by
  rw [typeIReflectionFourier, SchwartzMap.fourier_coe, Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards with x
  rw [typeIReflectionSchwartz_apply]
  by_cases hweight : typeISourceSmoothWeight Y A r x = 0
  · simp [typeIReflectionKernel, hweight]
  · have hxPos : 0 < x := by
      by_contra hx
      have hxle : x ≤ 0 := le_of_not_gt hx
      have hYreal : (0 : ℝ) < Y := by exact_mod_cast hY
      have hleft : Real.smoothTransition (x - (Y : ℝ)) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      apply hweight
      simp [typeISourceSmoothWeight, typeITailBoundary, hleft]
    unfold typeIReflectionKernel reflectionPhase
    simp only [Real.inner_apply, smul_eq_mul]
    calc
      Complex.exp (((-2 * Real.pi * (x * -m) : ℝ) : ℂ) * I) *
          ((typeISourceSmoothWeight Y A r x : ℂ) *
            Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
            Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * I))) =
        (typeISourceSmoothWeight Y A r x : ℂ) *
          Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
          (Complex.exp (((-2 * Real.pi * (x * -m) : ℝ) : ℂ) * I) *
            Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * I))) := by ring
      _ = (typeISourceSmoothWeight Y A r x : ℂ) *
          Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
          Complex.exp
            ((((-2 * Real.pi * (x * -m) : ℝ) : ℂ) * I) +
              (((-t * Real.log x : ℝ) : ℂ) * I)) := by
            rw [Complex.exp_add]
      _ = (typeISourceSmoothWeight Y A r x : ℂ) *
          Complex.exp ((((-σ * Real.log x : ℝ) : ℂ))) *
          Complex.exp (2 * Real.pi * I *
            (((m * x - t / (2 * Real.pi) * Real.log x : ℝ)) : ℂ)) := by
            congr 2
            push_cast
            field_simp [Real.pi_ne_zero]
            ring

/-- The exact stationary-frequency window of the `r`-th source block.  Its
endpoints are constant multiples of `t/(2^r Y)`, the dual scale required by
the medium Type-I B-process. -/
theorem typeIReflection_stationary_window
    {Y r : ℕ} {t m : ℝ} (hY : 0 < Y) (hm : 0 < m) :
    reflectionStationaryPoint t m ∈
        Set.Icc (((2 ^ r * Y : ℕ) : ℝ) / 2)
          (2 * ((2 ^ r * Y : ℕ) : ℝ)) ↔
      t / (4 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ)) ≤ m ∧
        m ≤ t / (Real.pi * ((2 ^ r * Y : ℕ) : ℝ)) := by
  have hscale : (0 : ℝ) < (2 ^ r * Y : ℕ) := by positivity
  rw [reflectionStationaryPoint_mem_Icc_iff hm (by positivity)
    (by linarith : ((2 ^ r * Y : ℕ) : ℝ) / 2 ≤
      2 * ((2 ^ r * Y : ℕ) : ℝ))]
  have hlow : t / (2 * Real.pi *
      (2 * ((2 ^ r * Y : ℕ) : ℝ))) =
      t / (4 * Real.pi * ((2 ^ r * Y : ℕ) : ℝ)) := by ring
  have hupp : t / (2 * Real.pi *
      (((2 ^ r * Y : ℕ) : ℝ) / 2)) =
      t / (Real.pi * ((2 ^ r * Y : ℕ) : ℝ)) := by
    field_simp [Real.pi_ne_zero, hscale.ne']
  rw [hlow, hupp]

/-- On an interior medium scale the artificial source boundary is identically
one wherever the fixed dyadic cutoff is nonzero.  Thus the Poisson kernel is
the genuine boundary-free dyadic kernel, not a silently altered model. -/
theorem typeISourceSmoothWeight_eq_dyadic_of_interior
    {Y A r : ℕ}
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤
      (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A)
    (x : ℝ) :
    typeISourceSmoothWeight Y A r x =
      typeIDyadicCutoff (x / (2 ^ r * Y : ℕ)) := by
  let Q : ℝ := ((2 ^ r * Y : ℕ) : ℝ)
  by_cases hcut : typeIDyadicCutoff (x / Q) = 0
  · unfold typeISourceSmoothWeight
    change typeITailBoundary Y A x * typeIDyadicCutoff (x / Q) =
      typeIDyadicCutoff (x / Q)
    rw [hcut, mul_zero]
  · have hQ : 0 < Q := by
      have hleftPos : (0 : ℝ) < ((Y + 1 : ℕ) : ℝ) := by positivity
      nlinarith
    have hxLowerRatio : 1 / 2 < x / Q := by
      by_contra hnot
      exact hcut (typeIDyadicCutoff_eq_zero_of_le_half (le_of_not_gt hnot))
    have hxUpperRatio : x / Q < 2 := by
      by_contra hnot
      exact hcut (typeIDyadicCutoff_eq_zero_of_two_le (le_of_not_gt hnot))
    have hxLower : ((Y + 1 : ℕ) : ℝ) < x := by
      have hscaled := (lt_div_iff₀ hQ).mp hxLowerRatio
      linarith
    have hUpperReal : 2 * Q ≤ (A : ℝ) := by
      dsimp only [Q]
      exact_mod_cast hUpper
    have hxUpper : x < (A : ℝ) := by
      exact ((div_lt_iff₀ hQ).mp hxUpperRatio).trans_le hUpperReal
    have hleft : Real.smoothTransition (x - (Y : ℝ)) = 1 :=
      Real.smoothTransition.one_of_one_le (by push_cast at hxLower; linarith)
    have hright : Real.smoothTransition
        (((A + 1 : ℕ) : ℝ) - x) = 1 :=
      Real.smoothTransition.one_of_one_le (by push_cast; linarith)
    unfold typeISourceSmoothWeight typeITailBoundary
    rw [hleft, hright, one_mul, one_mul]

/-- Exact removal of the source boundary from the full continuous kernel on
an interior medium scale. -/
theorem typeIReflectionKernel_eq_dyadicPhysical_of_interior
    {Y A r : ℕ} {σ t : ℝ}
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤
      (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A) :
    typeIReflectionKernel Y A r σ t =
      typeIDyadicPhysicalIntegrand σ t 0 (2 ^ r * Y : ℕ) := by
  funext x
  unfold typeIReflectionKernel
  rw [typeISourceSmoothWeight_eq_dyadic_of_interior hLower hUpper]
  unfold typeIDyadicPhysicalIntegrand
    gmReflectionPowerWeight
  have hphase :
      Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * I)) =
        Complex.exp
          (-((((t * Real.log x - 2 * Real.pi * 0 * x : ℝ) : ℂ) * I))) := by
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

/-! ## Uniform normalized Fourier tail for interior medium blocks -/

/-- The boundary-free normalized Type-I amplitude on the fixed interval
`[1/2,2]`.  Dependence on the physical dyadic scale is recovered by Fourier
dilation, while `σ` is fixed throughout one zero-density estimate. -/
noncomputable def typeINormalizedAmplitude (σ x : ℝ) : ℂ :=
  (typeIDyadicCutoff x : ℂ) *
    Complex.exp ((((-σ * Real.log x : ℝ) : ℂ)))

/-- The normalized Type-I amplitude is smooth to every order. -/
theorem contDiff_typeINormalizedAmplitude (σ : ℝ) :
    ContDiff ℝ ∞ (typeINormalizedAmplitude σ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hEventually : typeINormalizedAmplitude σ =ᶠ[𝓝 0] 0 := by
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
      have hcut := typeIDyadicCutoff_eq_zero_of_le_half (le_of_lt hy)
      simp [typeINormalizedAmplitude, hcut]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hcut : ContDiffAt ℝ ∞
        (fun y : ℝ => (typeIDyadicCutoff y : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x
        contDiff_typeIDyadicCutoff.contDiffAt
    have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.2 hx
    have hpow : ContDiffAt ℝ ∞
        (fun y : ℝ => Complex.exp ((((-σ * Real.log y : ℝ) : ℂ)))) x :=
      (Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (contDiffAt_const.mul hlog)).cexp
    exact hcut.mul hpow

private theorem hasCompactSupport_typeINormalizedAmplitude (σ : ℝ) :
    HasCompactSupport (typeINormalizedAmplitude σ) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (1 / 2 : ℝ) 2))
  intro x hx
  have hcut : typeIDyadicCutoff x = 0 := by
    by_cases hhalf : x ≤ 1 / 2
    · exact typeIDyadicCutoff_eq_zero_of_le_half hhalf
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      by_contra htwo
      exact hx ⟨le_of_not_ge hhalf, le_of_not_ge htwo⟩
  simp [typeINormalizedAmplitude, hcut]

private noncomputable def typeINormalizedAmplitudeSchwartz (σ : ℝ) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeINormalizedAmplitude σ).toSchwartzMap
    (contDiff_typeINormalizedAmplitude σ)

@[simp]
private theorem typeINormalizedAmplitudeSchwartz_apply (σ x : ℝ) :
    typeINormalizedAmplitudeSchwartz σ x = typeINormalizedAmplitude σ x := rfl

/-- Normalized oscillatory kernel whose Fourier samples are the Poisson
modes of an interior dyadic block after the change of variables `x=Q*u`. -/
noncomputable def typeINormalizedKernel (σ t x : ℝ) : ℂ :=
  typeINormalizedAmplitude σ x *
    Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * I))

private theorem contDiff_typeINormalizedKernel (σ t : ℝ) :
    ContDiff ℝ ∞ (typeINormalizedKernel σ t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hEventually : typeINormalizedKernel σ t =ᶠ[𝓝 0] 0 := by
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num)] with y hy
      have hcut := typeIDyadicCutoff_eq_zero_of_le_half (le_of_lt hy)
      simp [typeINormalizedKernel, typeINormalizedAmplitude, hcut]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hamp : ContDiffAt ℝ ∞ (typeINormalizedAmplitude σ) x :=
      (contDiff_typeINormalizedAmplitude σ).contDiffAt
    have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.2 hx
    have hphase : ContDiffAt ℝ ∞
        (fun y : ℝ => Complex.exp ((((-t * Real.log y : ℝ) : ℂ) * I))) x :=
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp x
        (contDiffAt_const.mul hlog)).mul contDiffAt_const).cexp
    exact hamp.mul hphase

private theorem hasCompactSupport_typeINormalizedKernel (σ t : ℝ) :
    HasCompactSupport (typeINormalizedKernel σ t) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (1 / 2 : ℝ) 2))
  intro x hx
  have hcut : typeIDyadicCutoff x = 0 := by
    by_cases hhalf : x ≤ 1 / 2
    · exact typeIDyadicCutoff_eq_zero_of_le_half hhalf
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      by_contra htwo
      exact hx ⟨le_of_not_ge hhalf, le_of_not_ge htwo⟩
  simp [typeINormalizedKernel, typeINormalizedAmplitude, hcut]

/-- The `typeINormalizedKernelSchwartz` definition used by the source-facing construction in `TypeIReflection`. -/
noncomputable def typeINormalizedKernelSchwartz (σ t : ℝ) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeINormalizedKernel σ t).toSchwartzMap
    (contDiff_typeINormalizedKernel σ t)

@[simp]
theorem typeINormalizedKernelSchwartz_apply (σ t x : ℝ) :
    typeINormalizedKernelSchwartz σ t x = typeINormalizedKernel σ t x := rfl

/-- The `typeINormalizedFourier` definition used by the source-facing construction in `TypeIReflection`. -/
noncomputable def typeINormalizedFourier (σ t ξ : ℝ) : ℂ :=
  𝓕 (typeINormalizedKernelSchwartz σ t) ξ

private theorem typeINormalizedKernel_eq_amplitude_mul_cpow
    (σ t : ℝ) {x : ℝ} (hx : 0 < x) :
    typeINormalizedKernel σ t x =
      typeINormalizedAmplitude σ x * (x : ℂ) ^ ((-t : ℂ) * I) := by
  unfold typeINormalizedKernel
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
  rw [← Complex.ofReal_log hx.le]
  congr 2
  push_cast
  ring

private theorem contDiffAt_ofReal_cpow_neg_mul_I
    (t : ℝ) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ n (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x := by
  have hEq :
      (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) =ᶠ[nhds x]
        fun y : ℝ => Complex.exp ((((-t * Real.log y : ℝ) : ℂ) * I)) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne')]
    rw [← Complex.ofReal_log hy.le]
    congr 1
    push_cast
    ring
  have hExp : ContDiffAt ℝ n
      (fun y : ℝ => Complex.exp ((((-t * Real.log y : ℝ) : ℂ) * I))) x := by
    have hReal : ContDiffAt ℝ n (fun y : ℝ => -t * Real.log y) x :=
      contDiffAt_const.mul (Real.contDiffAt_log.mpr hx.ne')
    have hComplex : ContDiffAt ℝ n
        (fun y : ℝ => ((-t * Real.log y : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hReal
    exact (hComplex.mul contDiffAt_const).cexp
  exact hExp.congr_of_eventuallyEq hEq

private theorem norm_iteratedDeriv_ofReal_cpow_neg_mul_I_le
    (t : ℝ) (n : ℕ) {x : ℝ} (hx : 1 / 2 ≤ x) :
    ‖iteratedDeriv n (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ ≤
      2 ^ n * (|t| + n) ^ n := by
  have hxPos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hx
  rw [iteratedDeriv_ofReal_cpow ((-t : ℂ) * I) n hxPos, norm_mul]
  have hcoeff := norm_gmCpowDerivativeCoeff_le ((-t : ℂ) * I) n
  have hpow : ‖(x : ℂ) ^ ((-t : ℂ) * I - n)‖ ≤ 2 ^ n := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxPos]
    have hre : (((-t : ℂ) * I - n).re) = -(n : ℝ) := by simp
    rw [hre]
    have hmono : x ^ (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(n : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hx
        (neg_nonpos.mpr (Nat.cast_nonneg n))
    calc
      x ^ (-(n : ℝ)) ≤ (1 / 2 : ℝ) ^ (-(n : ℝ)) := hmono
      _ = 2 ^ n := by
        rw [Real.rpow_neg_eq_inv_rpow, Real.rpow_natCast]
        norm_num
  calc
    ‖gmCpowDerivativeCoeff ((-t : ℂ) * I) n‖ *
          ‖(x : ℂ) ^ ((-t : ℂ) * I - n)‖ ≤
        (‖((-t : ℂ) * I)‖ + n) ^ n * 2 ^ n :=
      mul_le_mul hcoeff hpow (norm_nonneg _) (by positivity)
    _ = 2 ^ n * (|t| + n) ^ n := by
      simp [Real.norm_eq_abs]
      ring

private theorem typeIMellinDerivativePower_le
    (t : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    (|t| + k) ^ k ≤
      (n + 1 : ℝ) ^ n * (1 + |t|) ^ n := by
  let B : ℝ := (n + 1) * (1 + |t|)
  have hnNonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hBOne : 1 ≤ B := by
    dsimp only [B]
    nlinarith [abs_nonneg t]
  have hbase : |t| + k ≤ B := by
    dsimp only [B]
    have hkReal : (k : ℝ) ≤ n := by exact_mod_cast hkn
    nlinarith [abs_nonneg t]
  calc
    (|t| + k) ^ k ≤ B ^ k :=
      pow_le_pow_left₀ (by positivity) hbase k
    _ ≤ B ^ n := pow_le_pow_right₀ hBOne hkn
    _ = (n + 1 : ℝ) ^ n * (1 + |t|) ^ n := by
      dsimp only [B]
      rw [mul_pow]

/-- Uniform derivative bound for the boundary-free normalized Type-I
kernel.  The constant may depend on the fixed density line `σ`, but is
independent of the ordinate and dyadic scale. -/
theorem typeINormalizedKernel_uniform_iteratedFDeriv (σ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ,
      ‖iteratedFDeriv ℝ n (typeINormalizedKernel σ t) x‖ ≤
        C * (1 + |t|) ^ n := by
  let C : ℝ := ∑ i ∈ Finset.range (n + 1),
    (n.choose i : ℝ) *
      SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
        2 ^ n * (n + 1 : ℝ) ^ n
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro t x
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  by_cases hxLow : x < 1 / 2
  · have hzero : typeINormalizedKernel σ t =ᶠ[nhds x] 0 := by
      filter_upwards [Iio_mem_nhds hxLow] with y hy
      simp [typeINormalizedKernel, typeINormalizedAmplitude,
        typeIDyadicCutoff_eq_zero_of_le_half (le_of_lt hy)]
    rw [hzero.iteratedDeriv_eq]
    simp
    positivity
  by_cases hxHigh : 2 < x
  · have hzero : typeINormalizedKernel σ t =ᶠ[nhds x] 0 := by
      filter_upwards [Ioi_mem_nhds hxHigh] with y hy
      simp [typeINormalizedKernel, typeINormalizedAmplitude,
        typeIDyadicCutoff_eq_zero_of_two_le (le_of_lt hy)]
    rw [hzero.iteratedDeriv_eq]
    simp
    positivity
  have hxIcc : x ∈ Set.Icc (1 / 2 : ℝ) 2 :=
    ⟨le_of_not_gt hxLow, le_of_not_gt hxHigh⟩
  have hxPos : 0 < x := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hxIcc.1
  have hlocal : typeINormalizedKernel σ t =ᶠ[nhds x]
      fun y : ℝ => typeINormalizedAmplitude σ y *
        (y : ℂ) ^ ((-t : ℂ) * I) := by
    filter_upwards [Ioi_mem_nhds hxPos] with y hy
    exact typeINormalizedKernel_eq_amplitude_mul_cpow σ t hy
  rw [hlocal.iteratedDeriv_eq]
  have hampSmooth : ContDiffAt ℝ n (typeINormalizedAmplitude σ) x :=
    (contDiff_typeINormalizedAmplitude σ).contDiffAt.of_le
      (by exact_mod_cast le_top)
  have hphaseSmooth := contDiffAt_ofReal_cpow_neg_mul_I t n hxPos
  change ‖iteratedDeriv n
      (typeINormalizedAmplitude σ *
        fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ ≤
    C * (1 + |t|) ^ n
  rw [iteratedDeriv_mul hampSmooth hphaseSmooth]
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℂ) * iteratedDeriv i (typeINormalizedAmplitude σ) x *
          iteratedDeriv (n - i)
            (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        ‖(n.choose i : ℂ) * iteratedDeriv i (typeINormalizedAmplitude σ) x *
          iteratedDeriv (n - i)
            (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℝ) *
          SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
            2 ^ n * (n + 1 : ℝ) ^ n) * (1 + |t|) ^ n := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hamp := SchwartzMap.le_seminorm' (𝕜 := ℝ) 0 i
        (typeINormalizedAmplitudeSchwartz σ) x
      simp only [pow_zero, one_mul] at hamp
      change ‖iteratedDeriv i (typeINormalizedAmplitude σ) x‖ ≤
        SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) at hamp
      have hphase := norm_iteratedDeriv_ofReal_cpow_neg_mul_I_le
        t (n - i) hxIcc.1
      have hpower := typeIMellinDerivativePower_le t (Nat.sub_le n i)
      have htwo : (2 : ℝ) ^ (n - i) ≤ 2 ^ n := by
        exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le n i)
      rw [norm_mul, norm_mul, Complex.norm_natCast]
      have hchoose : 0 ≤ (n.choose i : ℝ) := Nat.cast_nonneg _
      have hseminorm :
          0 ≤ SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) :=
        by positivity
      have hcoefficient :
          0 ≤ (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) :=
        mul_nonneg hchoose hseminorm
      have hphaseNonneg :
          0 ≤ ‖iteratedDeriv (n - i)
            (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ := norm_nonneg _
      have hinner :
          (2 : ℝ) ^ (n - i) * (|t| + ((n - i : ℕ) : ℝ)) ^ (n - i) ≤
            2 ^ n * ((n + 1 : ℝ) ^ n * (1 + |t|) ^ n) := by
        exact mul_le_mul htwo hpower (by positivity) (by positivity)
      calc
        (n.choose i : ℝ) * ‖iteratedDeriv i (typeINormalizedAmplitude σ) x‖ *
            ‖iteratedDeriv (n - i)
              (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ ≤
          (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
              ‖iteratedDeriv (n - i)
                (fun y : ℝ => (y : ℂ) ^ ((-t : ℂ) * I)) x‖ := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hamp hchoose) hphaseNonneg
        _ ≤ (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
              (2 ^ (n - i) * (|t| + ((n - i : ℕ) : ℝ)) ^ (n - i)) := by
            exact mul_le_mul_of_nonneg_left hphase hcoefficient
        _ ≤ (n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
              (2 ^ n * ((n + 1 : ℝ) ^ n * (1 + |t|) ^ n)) := by
            exact mul_le_mul_of_nonneg_left hinner hcoefficient
        _ = ((n.choose i : ℝ) *
            SchwartzMap.seminorm ℝ 0 i (typeINormalizedAmplitudeSchwartz σ) *
              2 ^ n * (n + 1 : ℝ) ^ n) * (1 + |t|) ^ n := by ring
    _ = C * (1 + |t|) ^ n := by
      dsimp only [C]
      rw [Finset.sum_mul]

private theorem integral_norm_iteratedFDeriv_typeINormalizedKernel_le
    (σ : ℝ) (p : ℕ) {D : ℝ}
    (hbound : ∀ t x : ℝ,
      ‖iteratedFDeriv ℝ p (typeINormalizedKernel σ t) x‖ ≤
        D * (1 + |t|) ^ p) (t : ℝ) :
    (∫ x : ℝ, ‖iteratedFDeriv ℝ p (typeINormalizedKernel σ t) x‖) ≤
      (3 / 2 : ℝ) * D * (1 + |t|) ^ p := by
  let f : ℝ → ℝ := fun x =>
    ‖iteratedFDeriv ℝ p (typeINormalizedKernel σ t) x‖
  have hfInt : Integrable f := by
    simpa only [f, pow_zero, one_mul] using
      (SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
        (typeINormalizedKernelSchwartz σ t) 0 p)
  have hsupport : Function.support f ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
    intro x hx
    by_contra hnot
    have hxOutside : x < 1 / 2 ∨ 2 < x := by
      by_cases hxLow : x < 1 / 2
      · exact Or.inl hxLow
      · exact Or.inr (lt_of_not_ge fun hxUpper =>
          hnot ⟨le_of_not_gt hxLow, hxUpper⟩)
    have hzero : typeINormalizedKernel σ t =ᶠ[nhds x] 0 := by
      rcases hxOutside with hxLow | hxHigh
      · filter_upwards [Iio_mem_nhds hxLow] with y hy
        simp [typeINormalizedKernel, typeINormalizedAmplitude,
          typeIDyadicCutoff_eq_zero_of_le_half (le_of_lt hy)]
      · filter_upwards [Ioi_mem_nhds hxHigh] with y hy
        simp [typeINormalizedKernel, typeINormalizedAmplitude,
          typeIDyadicCutoff_eq_zero_of_two_le (le_of_lt hy)]
    apply hx
    dsimp only [f]
    rw [(hzero.iteratedFDeriv ℝ p).eq_of_nhds]
    simp
  have hEq : f = Set.indicator (Set.Icc (1 / 2 : ℝ) 2) f := by
    funext x
    by_cases hx : x ∈ Set.Icc (1 / 2 : ℝ) 2
    · exact (Set.indicator_of_mem hx _).symm
    · have : f x = 0 := not_ne_iff.mp fun hne => hx (hsupport hne)
      simp only [Set.indicator, hx, if_false]
      exact this
  rw [show (∫ x : ℝ, ‖iteratedFDeriv ℝ p
      (typeINormalizedKernel σ t) x‖) = ∫ x : ℝ, f x by rfl]
  rw [hEq, MeasureTheory.integral_indicator measurableSet_Icc]
  calc
    (∫ x : ℝ in Set.Icc (1 / 2) 2, f x) ≤
        ∫ _x : ℝ in Set.Icc (1 / 2) 2, D * (1 + |t|) ^ p := by
      apply MeasureTheory.setIntegral_mono_on
      · exact hfInt.integrableOn
      · exact MeasureTheory.integrableOn_const
          (hs := ne_of_lt
            (measure_Icc_lt_top : volume (Set.Icc (1 / 2 : ℝ) 2) < (⊤ : ENNReal)))
      · exact measurableSet_Icc
      · intro x hx
        exact hbound t x
    _ = (3 / 2 : ℝ) * D * (1 + |t|) ^ p := by
      norm_num [max_eq_left]
      ring

/-- Uniform Fourier decay for the source-faithful normalized Type-I kernel.
The constant is independent of both the ordinate and Fourier frequency. -/
theorem typeINormalizedFourier_uniform_decay (σ : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ξ : ℝ,
      |ξ| ^ n * ‖typeINormalizedFourier σ t ξ‖ ≤
        C * (1 + |t|) ^ n := by
  choose D hD hDbound using fun p : ℕ =>
    typeINormalizedKernel_uniform_iteratedFDeriv σ p
  let C : ℝ := 2 ^ n * (3 / 2) * ∑ p ∈ Finset.range (n + 1), D p
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (by positivity) (by norm_num))
      (Finset.sum_nonneg fun p _ => hD p)
  refine ⟨C, hC, ?_⟩
  intro t ξ
  have hIntegrable : ∀ (k p : ℕ), k ≤ (0 : ℕ∞) → p ≤ (⊤ : ℕ∞) →
      Integrable (fun x : ℝ =>
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ p (typeINormalizedKernel σ t) x‖) := by
    intro k p _hk _hp
    simpa only [typeINormalizedKernelSchwartz_apply] using
      (SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
        (typeINormalizedKernelSchwartz σ t) k p)
  have hFourier := pow_mul_norm_iteratedFDeriv_fourier_le
    (f := typeINormalizedKernel σ t)
    (K := (0 : ℕ∞)) (N := (⊤ : ℕ∞))
    (contDiff_typeINormalizedKernel σ t) hIntegrable
    (k := 0) (n := n) (by norm_num) (by simp) ξ
  simp only [pow_zero, one_mul, zero_add, Finset.range_one,
    norm_iteratedFDeriv_zero] at hFourier
  have hFourier' : |ξ| ^ n * ‖typeINormalizedFourier σ t ξ‖ ≤
      2 ^ n * ∑ p ∈ Finset.range (n + 1),
        ∫ x : ℝ, ‖iteratedFDeriv ℝ p (typeINormalizedKernel σ t) x‖ := by
    simpa [typeINormalizedFourier, Real.norm_eq_abs, SchwartzMap.fourier_coe]
      using hFourier
  calc
    |ξ| ^ n * ‖typeINormalizedFourier σ t ξ‖ ≤
        2 ^ n * ∑ p ∈ Finset.range (n + 1),
          ∫ x : ℝ, ‖iteratedFDeriv ℝ p (typeINormalizedKernel σ t) x‖ := hFourier'
    _ ≤ 2 ^ n * ∑ p ∈ Finset.range (n + 1),
        ((3 / 2 : ℝ) * D p) * (1 + |t|) ^ n := by
      gcongr with p hp
      have hpn : p ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hp)
      have hint := integral_norm_iteratedFDeriv_typeINormalizedKernel_le
        σ p (hDbound p) t
      calc
        (∫ x : ℝ, ‖iteratedFDeriv ℝ p (typeINormalizedKernel σ t) x‖) ≤
            (3 / 2 : ℝ) * D p * (1 + |t|) ^ p := hint
        _ ≤ (3 / 2 : ℝ) * D p * (1 + |t|) ^ n := by
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ (by nlinarith [abs_nonneg t]) hpn)
            (mul_nonneg (by norm_num) (hD p))
    _ = C * (1 + |t|) ^ n := by
      dsimp only [C]
      rw [← Finset.sum_mul]
      rw [← Finset.mul_sum]
      ring

/-- At frequencies beyond the ordinate-scaled range, the normalized Type-I
Fourier coefficient has the `T⁻¹⁰⁰` decay required to sum the
nonstationary Poisson tail. -/
theorem typeINormalizedFourier_far_frequency_decay (σ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T t ξ : ℝ}, 1 ≤ T →
      (1 + |t|) * T ≤ |ξ| →
        ‖typeINormalizedFourier σ t ξ‖ ≤ C / T ^ 100 := by
  obtain ⟨C, hC, hDecay⟩ := typeINormalizedFourier_uniform_decay σ 101
  refine ⟨C, hC, ?_⟩
  intro T t ξ hT hξ
  have hbasePos : 0 < 1 + |t| := by positivity
  have hTPos : 0 < T := zero_lt_one.trans_le hT
  have hξPos : 0 < |ξ| := (mul_pos hbasePos hTPos).trans_le hξ
  have hpowξ : ((1 + |t|) * T) ^ 101 ≤ |ξ| ^ 101 :=
    pow_le_pow_left₀ (mul_nonneg hbasePos.le hTPos.le) hξ 101
  have hdiv : ‖typeINormalizedFourier σ t ξ‖ ≤
      C * (1 + |t|) ^ 101 / |ξ| ^ 101 := by
    rw [le_div_iff₀ (pow_pos hξPos 101)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hDecay t ξ
  calc
    ‖typeINormalizedFourier σ t ξ‖ ≤
        C * (1 + |t|) ^ 101 / |ξ| ^ 101 := hdiv
    _ ≤ C * (1 + |t|) ^ 101 / (((1 + |t|) * T) ^ 101) := by
      exact div_le_div_of_nonneg_left (mul_nonneg hC (by positivity))
        (pow_pos (mul_pos hbasePos hTPos) 101) hpowξ
    _ = C / T ^ 101 := by
      rw [mul_pow]
      field_simp [hbasePos.ne', hTPos.ne']
    _ ≤ C / T ^ 100 := by
      exact div_le_div_of_nonneg_left hC (pow_pos hTPos 100)
        (pow_le_pow_right₀ hT (by norm_num : 100 ≤ 101))

/-- The complete scaled Poisson tail outside the symmetric mode window
`|m| ≤ M`.  The physical dilation contributes the factor `Q`. -/
noncomputable def typeINormalizedFarTail
    (σ t : ℝ) (Q M : ℕ) : ℂ :=
  ∑' m : ℤ, if M < m.natAbs then
    (Q : ℂ) * typeINormalizedFourier σ t ((Q : ℝ) * (m : ℝ)) else 0

private theorem typeINormalizedFarTail_pointwise
    (σ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (Q M : ℕ),
      0 < Q → 0 < M → ∀ m : ℤ, M < m.natAbs →
      ‖(Q : ℂ) * typeINormalizedFourier σ t
          ((Q : ℝ) * (m : ℝ))‖ ≤
        (C * (1 + |t|) ^ 102 /
          ((Q : ℝ) ^ 101 * (M : ℝ) ^ 100)) *
            ‖1 / (m : ℂ) ^ 2‖ := by
  obtain ⟨C₀, hC₀, hDecay⟩ :=
    typeINormalizedFourier_uniform_decay σ 102
  let C : ℝ := C₀ + 1
  have hC : 0 < C := by dsimp only [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro t Q M hQ hM m hm
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hmNatPos : 0 < m.natAbs := hM.trans hm
  have hmNe : m ≠ 0 := Int.natAbs_ne_zero.mp hmNatPos.ne'
  have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hmNe
  have hmAbsPos : 0 < |(m : ℝ)| := abs_pos.mpr hmReal
  have hmAbs : (M : ℝ) ≤ |(m : ℝ)| := by
    have hcast : (M : ℝ) ≤ (m.natAbs : ℝ) := by exact_mod_cast (Nat.le_of_lt hm)
    simpa using hcast
  have hFreqAbs : |(Q : ℝ) * (m : ℝ)| =
      (Q : ℝ) * |(m : ℝ)| := by
    rw [abs_mul, abs_of_pos hQr]
  have hFreqPos : 0 < |(Q : ℝ) * (m : ℝ)| := by
    rw [hFreqAbs]
    positivity
  have hFourier :
      ‖typeINormalizedFourier σ t ((Q : ℝ) * (m : ℝ))‖ ≤
        C₀ * (1 + |t|) ^ 102 /
          |(Q : ℝ) * (m : ℝ)| ^ 102 := by
    rw [le_div_iff₀ (pow_pos hFreqPos 102)]
    simpa [mul_comm] using hDecay t ((Q : ℝ) * (m : ℝ))
  have hpow : (M : ℝ) ^ 100 * |(m : ℝ)| ^ 2 ≤
      |(m : ℝ)| ^ 102 := by
    calc
      (M : ℝ) ^ 100 * |(m : ℝ)| ^ 2 ≤
          |(m : ℝ)| ^ 100 * |(m : ℝ)| ^ 2 := by
            gcongr
      _ = |(m : ℝ)| ^ 102 := by ring
  have hDenPos : 0 < (Q : ℝ) ^ 101 * (M : ℝ) ^ 100 := by positivity
  rw [norm_mul, Complex.norm_natCast, norm_div, norm_one, norm_pow,
    Complex.norm_intCast]
  calc
    (Q : ℝ) *
        ‖typeINormalizedFourier σ t ((Q : ℝ) * (m : ℝ))‖ ≤
      (Q : ℝ) *
        (C₀ * (1 + |t|) ^ 102 /
          |(Q : ℝ) * (m : ℝ)| ^ 102) := by gcongr
    _ ≤ (C * (1 + |t|) ^ 102 /
          ((Q : ℝ) ^ 101 * (M : ℝ) ^ 100)) *
            (1 / |(m : ℝ)| ^ 2) := by
      rw [hFreqAbs, mul_pow]
      have hCcmp : C₀ ≤ C := by dsimp only [C]; linarith
      have hbase : 0 ≤ (1 + |t|) ^ 102 := by positivity
      have hDenSmall : 0 < (Q : ℝ) ^ 101 *
          ((M : ℝ) ^ 100 * |(m : ℝ)| ^ 2) := by positivity
      have hDenLarge : 0 < (Q : ℝ) ^ 101 * |(m : ℝ)| ^ 102 := by
        positivity
      have hDenOrder : (Q : ℝ) ^ 101 *
          ((M : ℝ) ^ 100 * |(m : ℝ)| ^ 2) ≤
          (Q : ℝ) ^ 101 * |(m : ℝ)| ^ 102 := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      have hLeftEq :
          (Q : ℝ) * (C₀ * (1 + |t|) ^ 102 /
              ((Q : ℝ) ^ 102 * |(m : ℝ)| ^ 102)) =
            C₀ * (1 + |t|) ^ 102 /
              ((Q : ℝ) ^ 101 * |(m : ℝ)| ^ 102) := by
        field_simp [hQr.ne']
      have hRightEq :
          (C * (1 + |t|) ^ 102 /
              ((Q : ℝ) ^ 101 * (M : ℝ) ^ 100)) *
                (1 / |(m : ℝ)| ^ 2) =
            C * (1 + |t|) ^ 102 /
              ((Q : ℝ) ^ 101 *
                ((M : ℝ) ^ 100 * |(m : ℝ)| ^ 2)) := by
        field_simp [hQr.ne', hMr.ne', hmAbsPos.ne']
      rw [hLeftEq, hRightEq]
      calc
        C₀ * (1 + |t|) ^ 102 /
            ((Q : ℝ) ^ 101 * |(m : ℝ)| ^ 102) ≤
          C * (1 + |t|) ^ 102 /
            ((Q : ℝ) ^ 101 * |(m : ℝ)| ^ 102) := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_right hCcmp hbase) hDenLarge.le
        _ ≤ C * (1 + |t|) ^ 102 /
            ((Q : ℝ) ^ 101 *
              ((M : ℝ) ^ 100 * |(m : ℝ)| ^ 2)) := by
              exact div_le_div_of_nonneg_left
                (mul_nonneg hC.le hbase) hDenSmall hDenOrder

/-- Uniform summation of the complete far Poisson tail.  The loss before
the cutoff gain is exactly `(1+|t|)^102 / (Q^101 M^100)`. -/
theorem typeINormalizedFarTail_bound (σ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (Q M : ℕ),
      0 < Q → 0 < M →
      ‖typeINormalizedFarTail σ t Q M‖ ≤
        K * (1 + |t|) ^ 102 /
          ((Q : ℝ) ^ 101 * (M : ℝ) ^ 100) := by
  obtain ⟨C, hC, hPointwise⟩ := typeINormalizedFarTail_pointwise σ
  have hPSeries : Summable (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) := by
    have hNorm : (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) =
        fun m : ℤ => |1 / (m : ℝ) ^ 2| := by
      funext m
      simp only [norm_div, norm_one, norm_pow, Complex.norm_intCast,
        abs_div, abs_one, pow_abs]
    rw [hNorm, summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (by norm_num)
  let B : ℝ := ∑' m : ℤ, ‖1 / (m : ℂ) ^ 2‖
  have hB : 0 ≤ B := tsum_nonneg fun m => norm_nonneg _
  refine ⟨C * B + 1, by positivity, ?_⟩
  intro t Q M hQ hM
  let scale : ℝ := C * (1 + |t|) ^ 102 /
    ((Q : ℝ) ^ 101 * (M : ℝ) ^ 100)
  have hComparison : ∀ m : ℤ,
      ‖if M < m.natAbs then
          (Q : ℂ) * typeINormalizedFourier σ t
            ((Q : ℝ) * (m : ℝ)) else 0‖ ≤
        scale * ‖1 / (m : ℂ) ^ 2‖ := by
    intro m
    by_cases hm : M < m.natAbs
    · simpa only [if_pos hm, scale] using hPointwise t Q M hQ hM m hm
    · have hscale : 0 ≤ scale := by
        dsimp only [scale]
        positivity
      rw [if_neg hm, norm_zero]
      exact mul_nonneg hscale (norm_nonneg _)
  have hScaledSummable : Summable
      (fun m : ℤ => scale * ‖1 / (m : ℂ) ^ 2‖) :=
    hPSeries.mul_left scale
  have hBound := tsum_of_norm_bounded hScaledSummable.hasSum hComparison
  rw [tsum_mul_left] at hBound
  change ‖typeINormalizedFarTail σ t Q M‖ ≤ scale * B at hBound
  have hDen : 0 < (Q : ℝ) ^ 101 * (M : ℝ) ^ 100 := by
    positivity
  calc
    ‖typeINormalizedFarTail σ t Q M‖ ≤ scale * B := hBound
    _ ≤ (C * B + 1) * (1 + |t|) ^ 102 /
          ((Q : ℝ) ^ 101 * (M : ℝ) ^ 100) := by
      dsimp only [scale]
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hDen).2
      have hpowNonneg : 0 ≤ (1 + |t|) ^ 102 := by positivity
      nlinarith

/-- Arbitrary-order version of `typeINormalizedFarTail_bound`.  Keeping the
order visible is essential in endpoint arguments: the physical cutoff may be
only `T^d` beyond the stationary window, where `d` is chosen after the final
epsilon. -/
theorem typeINormalizedFarTail_bound_order (σ : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (Q M : ℕ),
      0 < Q → 0 < M →
      ‖typeINormalizedFarTail σ t Q M‖ ≤
        K * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n) := by
  obtain ⟨C₀, hC₀, hDecay⟩ :=
    typeINormalizedFourier_uniform_decay σ (n + 2)
  let C : ℝ := C₀ + 1
  have hC : 0 < C := by dsimp only [C]; linarith
  have hPSeries : Summable (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) := by
    have hNorm : (fun m : ℤ => ‖1 / (m : ℂ) ^ 2‖) =
        fun m : ℤ => |1 / (m : ℝ) ^ 2| := by
      funext m
      simp only [norm_div, norm_one, norm_pow, Complex.norm_intCast,
        abs_div, abs_one, pow_abs]
    rw [hNorm, summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (by norm_num)
  let B : ℝ := ∑' m : ℤ, ‖1 / (m : ℂ) ^ 2‖
  have hB : 0 ≤ B := tsum_nonneg fun m => norm_nonneg _
  refine ⟨C * B + 1, by positivity, ?_⟩
  intro t Q M hQ hM
  have hQr : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  let scale : ℝ := C * (1 + |t|) ^ (n + 2) /
    ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n)
  have hPointwise : ∀ m : ℤ, M < m.natAbs →
      ‖(Q : ℂ) * typeINormalizedFourier σ t
          ((Q : ℝ) * (m : ℝ))‖ ≤
        scale * ‖1 / (m : ℂ) ^ 2‖ := by
    intro m hm
    have hmNatPos : 0 < m.natAbs := hM.trans hm
    have hmNe : m ≠ 0 := Int.natAbs_ne_zero.mp hmNatPos.ne'
    have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hmNe
    have hmAbsPos : 0 < |(m : ℝ)| := abs_pos.mpr hmReal
    have hmAbs : (M : ℝ) ≤ |(m : ℝ)| := by
      have hcast : (M : ℝ) ≤ (m.natAbs : ℝ) := by
        exact_mod_cast (Nat.le_of_lt hm)
      simpa using hcast
    have hFreqAbs : |(Q : ℝ) * (m : ℝ)| =
        (Q : ℝ) * |(m : ℝ)| := by
      rw [abs_mul, abs_of_pos hQr]
    have hFreqPos : 0 < |(Q : ℝ) * (m : ℝ)| := by
      rw [hFreqAbs]
      positivity
    have hFourier :
        ‖typeINormalizedFourier σ t ((Q : ℝ) * (m : ℝ))‖ ≤
          C₀ * (1 + |t|) ^ (n + 2) /
            |(Q : ℝ) * (m : ℝ)| ^ (n + 2) := by
      rw [le_div_iff₀ (pow_pos hFreqPos (n + 2))]
      simpa [mul_comm] using hDecay t ((Q : ℝ) * (m : ℝ))
    have hpow : (M : ℝ) ^ n * |(m : ℝ)| ^ 2 ≤
        |(m : ℝ)| ^ (n + 2) := by
      calc
        (M : ℝ) ^ n * |(m : ℝ)| ^ 2 ≤
            |(m : ℝ)| ^ n * |(m : ℝ)| ^ 2 := by gcongr
        _ = |(m : ℝ)| ^ (n + 2) := by rw [pow_add]
    have hDenSmall : 0 < (Q : ℝ) ^ (n + 1) *
        ((M : ℝ) ^ n * |(m : ℝ)| ^ 2) := by positivity
    have hDenLarge : 0 < (Q : ℝ) ^ (n + 1) *
        |(m : ℝ)| ^ (n + 2) := by positivity
    rw [norm_mul, Complex.norm_natCast, norm_div, norm_one, norm_pow,
      Complex.norm_intCast]
    calc
      (Q : ℝ) *
          ‖typeINormalizedFourier σ t ((Q : ℝ) * (m : ℝ))‖ ≤
        (Q : ℝ) * (C₀ * (1 + |t|) ^ (n + 2) /
          |(Q : ℝ) * (m : ℝ)| ^ (n + 2)) := by gcongr
      _ = C₀ * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * |(m : ℝ)| ^ (n + 2)) := by
        rw [hFreqAbs, mul_pow]
        field_simp [hQr.ne']
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ]
        ring
      _ ≤ C * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * |(m : ℝ)| ^ (n + 2)) := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith)
            (by positivity)) hDenLarge.le
      _ ≤ C * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) *
            ((M : ℝ) ^ n * |(m : ℝ)| ^ 2)) := by
        exact div_le_div_of_nonneg_left (by positivity) hDenSmall
          (mul_le_mul_of_nonneg_left hpow (by positivity))
      _ = scale * (1 / |(m : ℝ)| ^ 2) := by
        dsimp only [scale]
        field_simp [hQr.ne', hMr.ne', hmAbsPos.ne']
  have hComparison : ∀ m : ℤ,
      ‖if M < m.natAbs then
          (Q : ℂ) * typeINormalizedFourier σ t
            ((Q : ℝ) * (m : ℝ)) else 0‖ ≤
        scale * ‖1 / (m : ℂ) ^ 2‖ := by
    intro m
    by_cases hm : M < m.natAbs
    · simpa only [if_pos hm] using hPointwise m hm
    · have hscale : 0 ≤ scale := by dsimp only [scale]; positivity
      rw [if_neg hm, norm_zero]
      exact mul_nonneg hscale (norm_nonneg _)
  have hScaledSummable : Summable
      (fun m : ℤ => scale * ‖1 / (m : ℂ) ^ 2‖) :=
    hPSeries.mul_left scale
  have hBound := tsum_of_norm_bounded hScaledSummable.hasSum hComparison
  rw [tsum_mul_left] at hBound
  change ‖typeINormalizedFarTail σ t Q M‖ ≤ scale * B at hBound
  have hDen : 0 < (Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n := by positivity
  calc
    ‖typeINormalizedFarTail σ t Q M‖ ≤ scale * B := hBound
    _ ≤ (C * B + 1) * (1 + |t|) ^ (n + 2) /
          ((Q : ℝ) ^ (n + 1) * (M : ℝ) ^ n) := by
      dsimp only [scale]
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hDen).2
      have hpowNonneg : 0 ≤ (1 + |t|) ^ (n + 2) := by positivity
      nlinarith

/-! ## Exact scaled Poisson assembly -/

/-- The `typeINormalizedScaledKernel` definition used by the source-facing construction in `TypeIReflection`. -/
noncomputable def typeINormalizedScaledKernel
    (σ t Q x : ℝ) : ℂ :=
  typeINormalizedKernel σ t (x / Q)

private theorem contDiff_typeINormalizedScaledKernel
    (σ t Q : ℝ) :
    ContDiff ℝ ∞ (typeINormalizedScaledKernel σ t Q) := by
  unfold typeINormalizedScaledKernel
  exact (contDiff_typeINormalizedKernel σ t).comp
    (contDiff_id.div_const Q)

private theorem hasCompactSupport_typeINormalizedScaledKernel
    (σ t Q : ℝ) (hQ : 0 < Q) :
    HasCompactSupport (typeINormalizedScaledKernel σ t Q) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (Q / 2) (2 * Q)))
  intro x hx
  have hOutside : x / Q ∉ Set.Icc (1 / 2 : ℝ) 2 := by
    intro hScaled
    apply hx
    rw [Set.mem_Icc] at hScaled ⊢
    constructor
    · have := (le_div_iff₀ hQ).mp hScaled.1
      linarith
    · exact (div_le_iff₀ hQ).mp hScaled.2
  have hcut : typeIDyadicCutoff (x / Q) = 0 := by
    by_cases hhalf : x / Q ≤ 1 / 2
    · exact typeIDyadicCutoff_eq_zero_of_le_half hhalf
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      exact le_of_not_ge fun htwo => hOutside ⟨le_of_not_ge hhalf, htwo⟩
  simp [typeINormalizedScaledKernel, typeINormalizedKernel,
    typeINormalizedAmplitude, hcut]

/-- The `typeINormalizedScaledKernelSchwartz` definition used by the source-facing construction in `TypeIReflection`. -/
noncomputable def typeINormalizedScaledKernelSchwartz
    (σ t Q : ℝ) (hQ : 0 < Q) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeINormalizedScaledKernel σ t Q hQ).toSchwartzMap
    (contDiff_typeINormalizedScaledKernel σ t Q)

@[simp]
theorem typeINormalizedScaledKernelSchwartz_apply
    (σ t Q x : ℝ) (hQ : 0 < Q) :
    typeINormalizedScaledKernelSchwartz σ t Q hQ x =
      typeINormalizedKernel σ t (x / Q) := rfl

theorem typeINormalizedScaledKernel_fourier
    (σ t Q ξ : ℝ) (hQ : 0 < Q) :
    𝓕 (typeINormalizedScaledKernelSchwartz σ t Q hQ) ξ =
      (Q : ℂ) * typeINormalizedFourier σ t (Q * ξ) := by
  let g : ℝ → ℂ := fun y =>
    Complex.exp (((-2 * Real.pi * y * (Q * ξ) : ℝ) : ℂ) * I) *
      typeINormalizedKernel σ t y
  have hChange := Measure.integral_comp_div g Q
  rw [abs_of_pos hQ] at hChange
  rw [SchwartzMap.fourier_coe, Real.fourier_eq', typeINormalizedFourier,
    SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [Real.inner_apply, typeINormalizedScaledKernelSchwartz_apply,
    typeINormalizedKernelSchwartz_apply, smul_eq_mul]
  calc
    (∫ x : ℝ,
        Complex.exp (((-2 * Real.pi * (x * ξ) : ℝ) : ℂ) * I) *
          typeINormalizedKernel σ t (x / Q)) =
        ∫ x : ℝ, g (x / Q) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [g]
      have hphase : -2 * Real.pi * (x / Q) * (Q * ξ) =
          -2 * Real.pi * (x * ξ) := by
        field_simp [hQ.ne']
      rw [hphase]
    _ = Q • ∫ y : ℝ, g y := hChange
    _ = (Q : ℂ) * ∫ y : ℝ,
        Complex.exp (((-2 * Real.pi * (y * (Q * ξ)) : ℝ) : ℂ) * I) *
          typeINormalizedKernel σ t y := by
      change (Q : ℂ) * ∫ y : ℝ, g y = _
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [g]
      congr 2
      push_cast
      ring

/-- Poisson summation for the normalized medium Type-I kernel at physical
scale `Q`. -/
theorem typeINormalizedKernel_poisson
    (σ t Q : ℝ) (hQ : 0 < Q) :
    ∑' n : ℤ, typeINormalizedKernel σ t ((n : ℝ) / Q) =
      ∑' m : ℤ,
        (Q : ℂ) * typeINormalizedFourier σ t (Q * (m : ℝ)) := by
  have hPoisson := SchwartzMap.tsum_eq_tsum_fourier
    (typeINormalizedScaledKernelSchwartz σ t Q hQ) 0
  simpa [typeINormalizedScaledKernel_fourier σ t Q _ hQ] using hPoisson

/-- The finite symmetric retained-mode contribution, represented as a
finitely supported integer series. -/
noncomputable def typeINormalizedCentralModes
    (σ t : ℝ) (Q M : ℕ) : ℂ :=
  ∑' m : ℤ, if m.natAbs ≤ M then
    (Q : ℂ) * typeINormalizedFourier σ t
      ((Q : ℝ) * (m : ℝ)) else 0

private theorem typeINormalizedScaledFourier_summable
    (σ t Q : ℝ) (hQ : 0 < Q) :
    Summable (fun m : ℤ =>
      (Q : ℂ) * typeINormalizedFourier σ t (Q * (m : ℝ))) := by
  let F : 𝓢(ℝ, ℂ) :=
    𝓕 (typeINormalizedScaledKernelSchwartz σ t Q hQ)
  have hBigO := F.isBigO_cocompact_rpow (-2)
  have hSummable : Summable (fun m : ℤ => F (m : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hBigO.comp_tendsto Int.tendsto_coe_cofinite)
  simpa [F, typeINormalizedScaledKernel_fourier σ t Q _ hQ] using hSummable

theorem typeINormalizedPoisson_split
    (σ t : ℝ) (Q M : ℕ) (hQ : 0 < Q) :
    (∑' n : ℤ,
        typeINormalizedKernel σ t ((n : ℝ) / (Q : ℝ))) =
      typeINormalizedCentralModes σ t Q M +
        typeINormalizedFarTail σ t Q M := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [typeINormalizedKernel_poisson σ t (Q : ℝ) hQr]
  let f : ℤ → ℂ := fun m =>
    (Q : ℂ) * typeINormalizedFourier σ t
      ((Q : ℝ) * (m : ℝ))
  have hf : Summable f := by
    simpa only [f] using typeINormalizedScaledFourier_summable
      σ t (Q : ℝ) hQr
  have hcentral : Summable (fun m : ℤ =>
      if m.natAbs ≤ M then f m else 0) := by
    have hi := hf.indicator {m : ℤ | m.natAbs ≤ M}
    convert hi using 1
    funext m
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  have hfar : Summable (fun m : ℤ =>
      if M < m.natAbs then f m else 0) := by
    have hi := hf.indicator {m : ℤ | M < m.natAbs}
    convert hi using 1
    funext m
    simp only [Set.indicator_apply, Set.mem_setOf_eq]
  change (∑' m : ℤ, f m) =
    (∑' m : ℤ, if m.natAbs ≤ M then f m else 0) +
      ∑' m : ℤ, if M < m.natAbs then f m else 0
  rw [← hcentral.tsum_add hfar]
  congr 1
  funext m
  by_cases hm : m.natAbs ≤ M
  · simp [hm, Nat.not_lt_of_ge hm, f]
  · have hm' : M < m.natAbs := Nat.lt_of_not_ge hm
    simp [hm, hm', f]

/-- Complete kernel-checked medium Type-I B-process package: exact Poisson
conversion to a finite symmetric dual window plus an explicitly summed
uniform far-mode remainder.  The retained negative modes are identified
with the exact common Mellin polynomial by
`sum_typeIDyadicPhysicalIntegral_eq_reflectedMellinPolynomial`; the source
boundary is removed by
`typeIReflectionKernel_eq_dyadicPhysical_of_interior`. -/
theorem mediumTypeIExactBProcess_native (σ : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (t : ℝ) (Q M : ℕ),
      0 < Q → 0 < M →
      (∑' n : ℤ,
          typeINormalizedKernel σ t ((n : ℝ) / (Q : ℝ))) =
        typeINormalizedCentralModes σ t Q M +
          typeINormalizedFarTail σ t Q M ∧
      ‖typeINormalizedFarTail σ t Q M‖ ≤
        K * (1 + |t|) ^ 102 /
          ((Q : ℝ) ^ 101 * (M : ℝ) ^ 100) := by
  obtain ⟨K, hK, hTail⟩ := typeINormalizedFarTail_bound σ
  refine ⟨K, hK, ?_⟩
  intro t Q M hQ hM
  exact ⟨typeINormalizedPoisson_split σ t Q M hQ,
    hTail t Q M hQ hM⟩

end RiemannZeta.GuthMaynard
