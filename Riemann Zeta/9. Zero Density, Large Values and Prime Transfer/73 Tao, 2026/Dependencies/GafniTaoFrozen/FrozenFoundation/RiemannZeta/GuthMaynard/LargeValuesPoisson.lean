import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.MellinInversion
import RiemannZeta.GuthMaynard.TraceDispersion

open Complex Filter MeasureTheory Real Set
open scoped ContDiff FourierTransform SchwartzMap Topology

namespace RiemannZeta.GuthMaynard

/-!
# Fourier kernels for the Guth--Maynard trace expansion

This module starts the source Lemmas 4.3--4.5 from the actual cutoff used by
the sampling matrix.  In particular, the oscillatory kernel is a genuine
compactly supported smooth function and its Fourier transform is obtained
from Mathlib's Schwartz-space Fourier transform.
-/

/-- The source kernel `h_t(u) = w(u)^2 u^(it)`.  `Real.log` is harmless at
zero because the cutoff vanishes on a neighborhood of zero. -/
noncomputable def gmTraceKernel (cutoff : GMSmoothCutoff) (t x : ℝ) : ℂ :=
  (cutoff x : ℂ) ^ 2 *
    Complex.exp ((((t * Real.log x : ℝ) : ℂ) * I))

lemma gmSmoothCutoff_eq_zero_of_lt_one (cutoff : GMSmoothCutoff)
    {x : ℝ} (hx : x < 1) : cutoff x = 0 := by
  by_contra hne
  have hxSupport : x ∈ Function.support cutoff := hne
  have hxIcc := cutoff.support hxSupport
  exact (not_le_of_gt hx) hxIcc.1

theorem gmSmoothCutoff_eq_zero_at_one (cutoff : GMSmoothCutoff) :
    cutoff 1 = 0 := by
  by_contra hne
  have hSupportNhd : Function.support cutoff ∈ 𝓝 (1 : ℝ) :=
    cutoff.smooth.continuous.isOpen_support.mem_nhds hne
  have hIccNhd : Set.Icc (1 : ℝ) 2 ∈ 𝓝 (1 : ℝ) :=
    Filter.mem_of_superset hSupportNhd cutoff.support
  have hInterior : (1 : ℝ) ∈ interior (Set.Icc (1 : ℝ) 2) :=
    mem_interior_iff_mem_nhds.mpr hIccNhd
  rw [interior_Icc] at hInterior
  exact (lt_irrefl (1 : ℝ)) hInterior.1

theorem gmSmoothCutoff_eq_zero_at_two (cutoff : GMSmoothCutoff) :
    cutoff 2 = 0 := by
  by_contra hne
  have hSupportNhd : Function.support cutoff ∈ 𝓝 (2 : ℝ) :=
    cutoff.smooth.continuous.isOpen_support.mem_nhds hne
  have hIccNhd : Set.Icc (1 : ℝ) 2 ∈ 𝓝 (2 : ℝ) :=
    Filter.mem_of_superset hSupportNhd cutoff.support
  have hInterior : (2 : ℝ) ∈ interior (Set.Icc (1 : ℝ) 2) :=
    mem_interior_iff_mem_nhds.mpr hIccNhd
  rw [interior_Icc] at hInterior
  exact (lt_irrefl (2 : ℝ)) hInterior.2

theorem gmSmoothCutoff_eq_zero_of_le_one (cutoff : GMSmoothCutoff)
    {x : ℝ} (hx : x ≤ 1) : cutoff x = 0 := by
  rcases hx.eq_or_lt with rfl | hx
  · exact gmSmoothCutoff_eq_zero_at_one cutoff
  · exact gmSmoothCutoff_eq_zero_of_lt_one cutoff hx

theorem gmSmoothCutoff_eq_zero_of_two_le (cutoff : GMSmoothCutoff)
    {x : ℝ} (hx : 2 ≤ x) : cutoff x = 0 := by
  rcases hx.eq_or_lt with rfl | hx
  · exact gmSmoothCutoff_eq_zero_at_two cutoff
  · by_contra hne
    have hxSupport := cutoff.support hne
    exact (not_le_of_gt hx) hxSupport.2

theorem contDiff_gmTraceKernel (cutoff : GMSmoothCutoff) (t : ℝ) :
    ContDiff ℝ ∞ (gmTraceKernel cutoff t) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    have hEventually : gmTraceKernel cutoff t =ᶠ[𝓝 0] 0 := by
      filter_upwards [Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with y hy
      simp [gmTraceKernel, gmSmoothCutoff_eq_zero_of_lt_one cutoff hy]
    exact contDiffAt_const.congr_of_eventuallyEq hEventually
  · have hcut : ContDiffAt ℝ ∞ (fun y : ℝ => (cutoff y : ℂ) ^ 2) x := by
      have hcutReal : ContDiffAt ℝ ∞ cutoff x := cutoff.smooth.contDiffAt
      have hcutComplex : ContDiffAt ℝ ∞ (fun y : ℝ => (cutoff y : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp x hcutReal
      exact hcutComplex.pow 2
    have hphase : ContDiffAt ℝ ∞
        (fun y : ℝ => Complex.exp ((((t * Real.log y : ℝ) : ℂ) * I))) x := by
      apply ContDiffAt.cexp
      have hlog : ContDiffAt ℝ ∞ Real.log x := Real.contDiffAt_log.2 hx
      have hscaled : ContDiffAt ℝ ∞ (fun y : ℝ => t * Real.log y) x :=
        contDiffAt_const.mul hlog
      have hcast : ContDiffAt ℝ ∞
          (fun y : ℝ => ((t * Real.log y : ℝ) : ℂ)) x :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp x hscaled
      exact hcast.mul contDiffAt_const
    exact hcut.mul hphase

theorem hasCompactSupport_gmTraceKernel (cutoff : GMSmoothCutoff) (t : ℝ) :
    HasCompactSupport (gmTraceKernel cutoff t) := by
  apply HasCompactSupport.intro isCompact_Icc
  intro x hx
  have hcut : cutoff x = 0 := by
    by_contra hne
    exact hx (cutoff.support hne)
  simp [gmTraceKernel, hcut]

/-- The trace kernel as a Schwartz function. -/
noncomputable def gmTraceKernelSchwartz (cutoff : GMSmoothCutoff) (t : ℝ) :
    𝓢(ℝ, ℂ) :=
  (hasCompactSupport_gmTraceKernel cutoff t).toSchwartzMap
    (contDiff_gmTraceKernel cutoff t)

@[simp]
theorem gmTraceKernelSchwartz_apply (cutoff : GMSmoothCutoff) (t x : ℝ) :
    gmTraceKernelSchwartz cutoff t x = gmTraceKernel cutoff t x := rfl

/-- The Fourier coefficient `h-hat_t(ξ)` appearing in Lemmas 4.3--4.5. -/
noncomputable def gmTraceFourier (cutoff : GMSmoothCutoff) (t ξ : ℝ) : ℂ :=
  𝓕 (gmTraceKernelSchwartz cutoff t) ξ

/-- For every fixed ordinate, the source Fourier kernel has arbitrary-order
decay in the frequency.  The uniform polynomial dependence on `t` is proved
separately for the full two-parameter form of Lemma 4.3. -/
theorem gmTraceFourier_fixed_t_decay (cutoff : GMSmoothCutoff) (t : ℝ)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ,
      |ξ| ^ j * ‖gmTraceFourier cutoff t ξ‖ ≤ C := by
  let F : 𝓢(ℝ, ℂ) := 𝓕 (gmTraceKernelSchwartz cutoff t)
  obtain ⟨C, hC, hbound⟩ := F.decay j 0
  refine ⟨C, hC, ?_⟩
  intro ξ
  simpa [F, gmTraceFourier, Real.norm_eq_abs] using hbound ξ

/-- At zero Fourier frequency, the trace kernel is the Mellin transform of
the fixed squared cutoff on the vertical line `Re s = 1`. -/
theorem gmTraceFourier_zero_eq_mellin (cutoff : GMSmoothCutoff) (t : ℝ) :
    gmTraceFourier cutoff t 0 =
      mellin (fun x : ℝ => ((cutoff x : ℂ) ^ 2))
        ((1 : ℂ) + (t : ℂ) * I) := by
  have hIntegrable : Integrable (gmTraceKernel cutoff t) :=
    (gmTraceKernelSchwartz cutoff t).integrable
  have hOutside :
      ∫ x : ℝ in (Set.Ioi 0)ᶜ, gmTraceKernel cutoff t x = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hxNonpos : x ≤ 0 := by simpa using hx
    simp [gmTraceKernel,
      gmSmoothCutoff_eq_zero_of_lt_one cutoff (hxNonpos.trans_lt zero_lt_one)]
  have hWhole :
      ∫ x : ℝ, gmTraceKernel cutoff t x =
        ∫ x : ℝ in Set.Ioi 0, gmTraceKernel cutoff t x := by
    have hSplit := integral_add_compl (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))
      hIntegrable
    rw [hOutside, add_zero] at hSplit
    exact hSplit.symm
  rw [gmTraceFourier, SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [inner_zero_right, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, gmTraceKernelSchwartz_apply]
  rw [hWhole, mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hxPos : 0 < x := hx
  have hxNe : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxPos.ne'
  change (cutoff x : ℂ) ^ 2 * Complex.exp (((t * Real.log x : ℝ) : ℂ) * I) =
    (x : ℂ) ^ ((1 : ℂ) + (t : ℂ) * I - 1) * (cutoff x : ℂ) ^ 2
  rw [Complex.cpow_def_of_ne_zero hxNe]
  rw [Complex.ofReal_mul, Complex.ofReal_log hxPos.le]
  simp only [add_sub_cancel_left, mul_comm (t : ℂ) I]
  ring_nf

/-- The squared Guth--Maynard cutoff is absolutely Mellin convergent on the
source line `Re s = 1`.  At this line the Mellin density is just `w²`, so the
claim follows directly from compact support and continuity. -/
theorem mellinConvergent_gmCutoffSq_one (cutoff : GMSmoothCutoff) :
    MellinConvergent (fun x : ℝ => ((cutoff x : ℂ) ^ 2)) (1 : ℂ) := by
  rw [MellinConvergent]
  have hContinuous : Continuous (fun x : ℝ => ((cutoff x : ℂ) ^ 2)) := by
    exact (Complex.ofRealCLM.continuous.comp cutoff.smooth.continuous).pow 2
  have hCompact : HasCompactSupport (fun x : ℝ => ((cutoff x : ℂ) ^ 2)) := by
    apply HasCompactSupport.intro isCompact_Icc
    intro x hx
    have hcut : cutoff x = 0 := by
      by_contra hne
      exact hx (cutoff.support hne)
    simp [hcut]
  simpa using (hContinuous.integrable_of_hasCompactSupport hCompact).integrableOn

/-- The fixed logarithmic-coordinate kernel whose Fourier transform is the
zero-frequency coefficient `ĥ_t(0)`. -/
noncomputable def gmMellinKernel (cutoff : GMSmoothCutoff) (u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) * (cutoff (Real.exp (-u)) : ℂ) ^ 2

theorem contDiff_gmMellinKernel (cutoff : GMSmoothCutoff) :
    ContDiff ℝ ∞ (gmMellinKernel cutoff) := by
  have hExp : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) :=
    Real.contDiff_exp.comp contDiff_neg
  have hExpComplex : ContDiff ℝ ∞
      (fun u : ℝ => (Real.exp (-u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hExp
  have hCut : ContDiff ℝ ∞
      (fun u : ℝ => (cutoff (Real.exp (-u)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (cutoff.smooth.comp hExp)
  exact hExpComplex.mul (hCut.pow 2)

theorem hasCompactSupport_gmMellinKernel (cutoff : GMSmoothCutoff) :
    HasCompactSupport (gmMellinKernel cutoff) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (-Real.log 2) 0))
  intro u hu
  have hcut : cutoff (Real.exp (-u)) = 0 := by
    by_contra hne
    have hRange := cutoff.support hne
    apply hu
    rw [Set.mem_Icc]
    constructor
    · have hLog : -u ≤ Real.log 2 := by
        apply (Real.exp_le_exp).mp
        rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        exact hRange.2
      linarith
    · have hZero : (0 : ℝ) ≤ -u := by
        rw [← Real.exp_le_exp]
        simpa using hRange.1
      linarith
  simp [gmMellinKernel, hcut]

/-- The logarithmic-coordinate kernel as a Schwartz function. -/
noncomputable def gmMellinKernelSchwartz (cutoff : GMSmoothCutoff) :
    𝓢(ℝ, ℂ) :=
  (hasCompactSupport_gmMellinKernel cutoff).toSchwartzMap
    (contDiff_gmMellinKernel cutoff)

@[simp]
theorem gmMellinKernelSchwartz_apply (cutoff : GMSmoothCutoff) (u : ℝ) :
    gmMellinKernelSchwartz cutoff u = gmMellinKernel cutoff u := rfl

/-- The Mellin transform of the squared cutoff is integrable on the complete
vertical line `Re s = 1`.  The proof identifies that line with a rescaled
Fourier transform of the compactly supported logarithmic kernel. -/
theorem verticalIntegrable_mellin_gmCutoffSq_one (cutoff : GMSmoothCutoff) :
    VerticalIntegrable (mellin (fun x : ℝ => ((cutoff x : ℂ) ^ 2))) 1 := by
  rw [VerticalIntegrable]
  let F : 𝓢(ℝ, ℂ) := 𝓕 (gmMellinKernelSchwartz cutoff)
  have hFourier : Integrable (F : ℝ → ℂ) := F.integrable
  have hScaled : Integrable
      (fun u : ℝ => 𝓕 (gmMellinKernelSchwartz cutoff) (u / (2 * Real.pi))) := by
    simpa [F, div_eq_mul_inv] using
      hFourier.comp_mul_right' (show (2 * Real.pi)⁻¹ ≠ 0 by positivity)
  apply hScaled.congr
  filter_upwards with u
  rw [mellin_eq_fourier, SchwartzMap.fourier_coe]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, zero_add, one_mul, mul_one, neg_mul]
  congr 2

/-- Exact pointwise Mellin inversion of the squared source cutoff.  This is
the checked form of the Mellin representation used at the start of
Guth--Maynard Lemma 6.2. -/
theorem gmCutoffSq_mellinInversion (cutoff : GMSmoothCutoff)
    {x : ℝ} (hx : 0 < x) :
    mellinInv 1 (mellin (fun y : ℝ => ((cutoff y : ℂ) ^ 2))) x =
      (cutoff x : ℂ) ^ 2 := by
  exact mellinInv_mellin_eq 1 (fun y : ℝ => ((cutoff y : ℂ) ^ 2)) hx
    (mellinConvergent_gmCutoffSq_one cutoff)
    (verticalIntegrable_mellin_gmCutoffSq_one cutoff)
    ((Complex.ofRealCLM.continuous.comp cutoff.smooth.continuous).pow 2).continuousAt

/-- Substitution of the exact Mellin inversion formula into the oscillatory
trace kernel.  This is the non-asymptotic starting identity for the rescaling
argument in Guth--Maynard Lemma 6.2. -/
theorem gmTraceKernel_mellinInversion (cutoff : GMSmoothCutoff)
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    gmTraceKernel cutoff t x =
      mellinInv 1 (mellin (fun y : ℝ => ((cutoff y : ℂ) ^ 2))) x *
        Complex.exp ((((t * Real.log x : ℝ) : ℂ) * I)) := by
  rw [gmTraceKernel, gmCutoffSq_mellinInversion cutoff hx]

/-- The source coefficient at Fourier frequency zero is a sample of one
fixed Schwartz transform at frequency `t/(2π)`. -/
theorem gmTraceFourier_zero_eq_mellinKernel_fourier
    (cutoff : GMSmoothCutoff) (t : ℝ) :
    gmTraceFourier cutoff t 0 =
      𝓕 (gmMellinKernelSchwartz cutoff) (t / (2 * Real.pi)) := by
  rw [gmTraceFourier_zero_eq_mellin, mellin_eq_fourier,
    SchwartzMap.fourier_coe]
  simp
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (t / (2 * Real.pi)))
  funext u
  rw [gmMellinKernelSchwartz_apply]
  simp [gmMellinKernel, Complex.ofReal_exp]

/-- The zero-frequency half of Lemma 4.3(2), with the harmless Fourier
normalization `2π` left visible.  Its constant is independent of `t`. -/
theorem gmTraceFourier_zero_uniform_decay (cutoff : GMSmoothCutoff)
    (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |t / (2 * Real.pi)| ^ j * ‖gmTraceFourier cutoff t 0‖ ≤ C := by
  obtain ⟨C, hC, hBound⟩ := (𝓕 (gmMellinKernelSchwartz cutoff)).decay j 0
  refine ⟨C, hC, ?_⟩
  intro t
  rw [gmTraceFourier_zero_eq_mellinKernel_fourier]
  change ‖t / (2 * Real.pi)‖ ^ j *
    ‖𝓕 (gmMellinKernelSchwartz cutoff) (t / (2 * Real.pi))‖ ≤ C
  simpa only [norm_iteratedFDeriv_zero] using
    hBound (t / (2 * Real.pi))

/-- Lemma 4.3(2) at `ξ = 0` in the paper's unscaled `t` variable. -/
theorem gmTraceFourier_zero_uniform_decay_source
    (cutoff : GMSmoothCutoff) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |t| ^ j * ‖gmTraceFourier cutoff t 0‖ ≤ C := by
  obtain ⟨C, hC, hBound⟩ := gmTraceFourier_zero_uniform_decay cutoff j
  let scale : ℝ := 2 * Real.pi
  have hScale : 0 < scale := by dsimp [scale]; positivity
  refine ⟨scale ^ j * C, mul_pos (pow_pos hScale j) hC, ?_⟩
  intro t
  have hAbs : |t| = scale * |t / scale| := by
    rw [abs_div, abs_of_pos hScale]
    field_simp [hScale.ne']
  rw [hAbs, mul_pow]
  calc
    scale ^ j * |t / scale| ^ j * ‖gmTraceFourier cutoff t 0‖ =
        scale ^ j *
          (|t / scale| ^ j * ‖gmTraceFourier cutoff t 0‖) := by ring
    _ ≤ scale ^ j * C :=
      mul_le_mul_of_nonneg_left (hBound t) (pow_nonneg hScale.le j)

/-- The source trace kernel after dilation by the Dirichlet-polynomial
length.  Integer samples of this function are exactly `h_t(n / N)`. -/
noncomputable def gmScaledTraceKernel
    (cutoff : GMSmoothCutoff) (t N x : ℝ) : ℂ :=
  gmTraceKernel cutoff t (x / N)

theorem contDiff_gmScaledTraceKernel (cutoff : GMSmoothCutoff) (t N : ℝ) :
    ContDiff ℝ ∞ (gmScaledTraceKernel cutoff t N) := by
  unfold gmScaledTraceKernel
  exact (contDiff_gmTraceKernel cutoff t).comp
    (contDiff_id.div_const N)

theorem hasCompactSupport_gmScaledTraceKernel (cutoff : GMSmoothCutoff)
    (t N : ℝ) (hN : 0 < N) :
    HasCompactSupport (gmScaledTraceKernel cutoff t N) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc N (2 * N)))
  intro x hx
  have hNotScaled : x / N ∉ Set.Icc (1 : ℝ) 2 := by
    intro hScaled
    apply hx
    rw [Set.mem_Icc] at hScaled ⊢
    constructor
    · simpa using (le_div_iff₀ hN).mp hScaled.1
    · exact (div_le_iff₀ hN).mp hScaled.2
  have hcut : cutoff (x / N) = 0 := by
    by_contra hne
    exact hNotScaled (cutoff.support hne)
  simp [gmScaledTraceKernel, gmTraceKernel, hcut]

/-- The dilated trace kernel as a Schwartz function. -/
noncomputable def gmScaledTraceKernelSchwartz (cutoff : GMSmoothCutoff)
    (t N : ℝ) (hN : 0 < N) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_gmScaledTraceKernel cutoff t N hN).toSchwartzMap
    (contDiff_gmScaledTraceKernel cutoff t N)

@[simp]
theorem gmScaledTraceKernelSchwartz_apply (cutoff : GMSmoothCutoff)
    (t N x : ℝ) (hN : 0 < N) :
    gmScaledTraceKernelSchwartz cutoff t N hN x =
      gmTraceKernel cutoff t (x / N) := rfl

/-- Fourier dilation for the source kernel, with Mathlib's `2π` Fourier
normalization. -/
theorem gmScaledTraceKernel_fourier (cutoff : GMSmoothCutoff)
    (t N ξ : ℝ) (hN : 0 < N) :
    𝓕 (gmScaledTraceKernelSchwartz cutoff t N hN) ξ =
      (N : ℂ) * gmTraceFourier cutoff t (N * ξ) := by
  let g : ℝ → ℂ := fun y =>
    Complex.exp (((-2 * Real.pi * y * (N * ξ) : ℝ) : ℂ) * I) *
      gmTraceKernel cutoff t y
  have hChange := Measure.integral_comp_div g N
  rw [abs_of_pos hN] at hChange
  rw [SchwartzMap.fourier_coe, Real.fourier_eq', gmTraceFourier,
    SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [Real.inner_apply, gmScaledTraceKernelSchwartz_apply,
    gmTraceKernelSchwartz_apply, smul_eq_mul]
  calc
    (∫ x : ℝ,
        Complex.exp (((-2 * Real.pi * (x * ξ) : ℝ) : ℂ) * I) *
          gmTraceKernel cutoff t (x / N)) =
        ∫ x : ℝ, g (x / N) := by
      apply integral_congr_ae
      filter_upwards with x
      dsimp only [g]
      have hphase : -2 * Real.pi * (x / N) * (N * ξ) =
          -2 * Real.pi * (x * ξ) := by
        field_simp [hN.ne']
      rw [hphase]
    _ = N • ∫ y : ℝ, g y := hChange
    _ = (N : ℂ) * ∫ y : ℝ,
        Complex.exp (((-2 * Real.pi * (y * (N * ξ)) : ℝ) : ℂ) * I) *
          gmTraceKernel cutoff t y := by
      change (N : ℂ) * ∫ y : ℝ, g y = _
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [g]
      have hphase : -2 * Real.pi * y * (N * ξ) =
          -2 * Real.pi * (y * (N * ξ)) := by ring
      rw [hphase]

/-- Literal Poisson summation for the dilated source trace kernel.  This is
the analytic equality used before separating the zero and nonzero Fourier
frequencies in Guth--Maynard Lemmas 4.4--4.5. -/
theorem gmScaledTraceKernel_poisson (cutoff : GMSmoothCutoff)
    (t N : ℝ) (hN : 0 < N) :
    ∑' n : ℤ, gmTraceKernel cutoff t ((n : ℝ) / N) =
      ∑' m : ℤ, 𝓕 (gmScaledTraceKernelSchwartz cutoff t N hN) (m : ℝ) := by
  simpa using
    (SchwartzMap.tsum_eq_tsum_fourier
      (gmScaledTraceKernelSchwartz cutoff t N hN) 0)

/-- Poisson summation in the source normalization: the `m`-th dual
coefficient is `N ĥ_t(Nm)`. -/
theorem gmTraceKernel_poisson (cutoff : GMSmoothCutoff)
    (t N : ℝ) (hN : 0 < N) :
    ∑' n : ℤ, gmTraceKernel cutoff t ((n : ℝ) / N) =
      ∑' m : ℤ, (N : ℂ) * gmTraceFourier cutoff t (N * (m : ℝ)) := by
  rw [gmScaledTraceKernel_poisson cutoff t N hN]
  congr 1
  funext m
  exact gmScaledTraceKernel_fourier cutoff t N m hN

/-- Compact support converts the integer series in Poisson summation into
the literal finite block `(N,2N)`.  The omitted right endpoint contributes
zero because a smooth function supported in `[1,2]` vanishes at `2`. -/
theorem gmTraceKernel_tsum_eq_intBlock (cutoff : GMSmoothCutoff)
    (t N : ℝ) (hN : 0 < N) :
    ∑' n : ℤ, gmTraceKernel cutoff t ((n : ℝ) / N) =
      ∑ n ∈ Finset.Ioc (Int.floor N) (Int.floor (2 * N)),
        gmTraceKernel cutoff t ((n : ℝ) / N) := by
  rw [tsum_eq_sum (s := Finset.Ioc (Int.floor N) (Int.floor (2 * N))) ?_]
  intro n hn
  rw [Finset.mem_Ioc, not_and_or] at hn
  rcases hn with hnLower | hnUpper
  · have hnCast : (n : ℝ) ≤ N := by
      exact (Int.le_floor).mp (le_of_not_gt hnLower)
    have hRatio : (n : ℝ) / N ≤ 1 := (div_le_one hN).mpr hnCast
    simp [gmTraceKernel, gmSmoothCutoff_eq_zero_of_le_one cutoff hRatio]
  · have hnCast : 2 * N < (n : ℝ) := by
      exact (Int.floor_lt).mp (lt_of_not_ge hnUpper)
    have hRatio : 2 ≤ (n : ℝ) / N := by
      exact (le_div_iff₀ hN).mpr (le_of_lt hnCast)
    simp [gmTraceKernel, gmSmoothCutoff_eq_zero_of_two_le cutoff hRatio]

/-! ## Hilbert--Schmidt first-trace expansion -/

/-- The squared `L²` mass of the fixed real cutoff. -/
noncomputable def gmCutoffL2Sq (cutoff : GMSmoothCutoff) : ℝ :=
  ∫ x : ℝ, cutoff x ^ 2

/-- The zero Fourier mode of `h₀ = w²` is exactly the squared `L²` mass
of the cutoff. -/
theorem gmTraceFourier_zero_zero_eq_cutoffL2Sq (cutoff : GMSmoothCutoff) :
    gmTraceFourier cutoff 0 0 = (gmCutoffL2Sq cutoff : ℂ) := by
  rw [gmTraceFourier, SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [inner_zero_right, mul_zero, ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, gmTraceKernelSchwartz_apply]
  unfold gmCutoffL2Sq
  let L : ℝ := ∫ x : ℝ, cutoff x ^ 2
  change (∫ x : ℝ, gmTraceKernel cutoff 0 x) = (L : ℂ)
  calc
    (∫ x : ℝ, gmTraceKernel cutoff 0 x) =
        ∫ x : ℝ, ((cutoff x ^ 2 : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards with x
      simp [gmTraceKernel]
    _ = (L : ℂ) := by
      dsimp only [L]
      exact integral_ofReal

/-- At zero ordinate, compact support identifies the integer Poisson sum with
the literal natural-number matrix columns `(N,2N]`. -/
theorem gmTraceKernel_zero_tsum_eq_column_sum (cutoff : GMSmoothCutoff)
    (N : ℕ) (hN : 0 < N) :
    ∑' n : ℤ, gmTraceKernel cutoff 0 ((n : ℝ) / N) =
      ∑ n : GMColumn N, (cutoff ((n : ℝ) / N) ^ 2 : ℂ) := by
  rw [gmTraceKernel_tsum_eq_intBlock cutoff 0 (N : ℝ) (by exact_mod_cast hN)]
  have hFloorN : Int.floor (N : ℝ) = (N : ℤ) := by simp
  have hFloorTwoN : Int.floor (2 * (N : ℝ)) = ((2 * N : ℕ) : ℤ) := by
    calc
      Int.floor (2 * (N : ℝ)) = Int.floor (((2 * N : ℕ) : ℝ)) := by
        congr 1
        norm_num
      _ = ((2 * N : ℕ) : ℤ) := Int.floor_natCast (R := ℝ) (2 * N)
  rw [hFloorN, hFloorTwoN]
  have hInterval :
      Finset.Ioc (N : ℤ) ((2 * N : ℕ) : ℤ) =
        (Finset.Ioc N (2 * N)).map Nat.castEmbedding := by
    ext z
    simp only [Finset.mem_Ioc, Finset.mem_map]
    constructor
    · intro hz
      have hzNonneg : 0 ≤ z := by omega
      have hzCast : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzNonneg
      refine ⟨z.toNat, ?_, ?_⟩
      · constructor <;> omega
      · change (z.toNat : ℤ) = z
        exact hzCast
    · rintro ⟨n, hn, rfl⟩
      change (N : ℤ) < (n : ℤ) ∧ (n : ℤ) ≤ (2 * N : ℤ)
      exact_mod_cast hn
  rw [hInterval, Finset.sum_map]
  have hAttach :
      (∑ n : GMColumn N, (cutoff ((n : ℝ) / N) ^ 2 : ℂ)) =
        ∑ n ∈ dyadicInterval N, (cutoff ((n : ℝ) / N) ^ 2 : ℂ) := by
    conv_rhs => rw [← Finset.sum_attach]
    rw [Finset.univ_eq_attach (dyadicInterval N)]
  rw [hAttach]
  apply Finset.sum_congr rfl
  intro n hn
  simp [gmTraceKernel]

/-- The first Gram trace is the row cardinality times the common diagonal
cutoff sum. -/
theorem gmMatrix_gram_trace_eq_cutoff_sum (cutoff : GMSmoothCutoff)
    (N : ℕ) (W : Finset ℝ) :
    Matrix.trace (gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose) =
      (W.card : ℂ) *
        ∑ n : GMColumn N, (cutoff ((n : ℝ) / N) ^ 2 : ℂ) := by
  simp only [Matrix.trace, Matrix.diag_apply]
  simp_rw [gmMatrix_gram_apply_eq_phase_sum]
  simp only [sub_self, zero_mul, Complex.cpow_zero, mul_one]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe]
  simp only [nsmul_eq_mul]

/-- The scaled Fourier samples in the source Poisson formula are absolutely
summable. -/
theorem gmScaledTraceFourier_summable (cutoff : GMSmoothCutoff)
    (t N : ℝ) (hN : 0 < N) :
    Summable (fun m : ℤ ↦
      (N : ℂ) * gmTraceFourier cutoff t (N * (m : ℝ))) := by
  let F : 𝓢(ℝ, ℂ) :=
    SchwartzMap.fourierTransformCLM ℂ
      (gmScaledTraceKernelSchwartz cutoff t N hN)
  have hBigO := F.isBigO_cocompact_rpow (-2)
  have hSummable : Summable (fun m : ℤ ↦ F (m : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (hBigO.comp_tendsto Int.tendsto_coe_cofinite)
  simpa only [F, SchwartzMap.fourierTransformCLM_apply,
    gmScaledTraceKernel_fourier cutoff t N _ hN] using hSummable

/-- The full nonzero-frequency contribution in the first-trace Poisson
expansion. -/
noncomputable def gmTraceNonzeroTail (cutoff : GMSmoothCutoff) (N : ℕ) : ℂ :=
  ∑' m : ℤ, if m = 0 then 0 else
    (N : ℂ) * gmTraceFourier cutoff 0 ((N : ℝ) * (m : ℝ))

/-- Pointwise comparison of a nonzero scaled Fourier coefficient with the
integer `j`-series. -/
theorem gmTraceFourier_zero_nonzero_pointwise_bound (cutoff : GMSmoothCutoff)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 0 < N → ∀ (m : ℤ), m ≠ 0 →
      ‖(N : ℂ) * gmTraceFourier cutoff 0 ((N : ℝ) * (m : ℝ))‖ ≤
        C / (N : ℝ) ^ (j - 1) * ‖1 / (m : ℂ) ^ j‖ := by
  obtain ⟨C, hC, hDecay⟩ := gmTraceFourier_fixed_t_decay cutoff 0 j
  refine ⟨C, hC, ?_⟩
  intro N hN m hm
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hmReal : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hmAbs : 0 < |(m : ℝ)| := abs_pos.mpr hmReal
  have hFreqAbs : |(N : ℝ) * (m : ℝ)| = (N : ℝ) * |(m : ℝ)| := by
    rw [abs_mul, abs_of_pos hNr]
  have hDenom : 0 < |(N : ℝ) * (m : ℝ)| ^ j := by positivity
  have hFourier :
      ‖gmTraceFourier cutoff 0 ((N : ℝ) * (m : ℝ))‖ ≤
        C / |(N : ℝ) * (m : ℝ)| ^ j := by
    apply (le_div_iff₀ hDenom).2
    simpa [mul_comm] using hDecay ((N : ℝ) * (m : ℝ))
  rw [norm_mul, Complex.norm_natCast, norm_div, norm_one, norm_pow,
    Complex.norm_intCast]
  calc
    (N : ℝ) * ‖gmTraceFourier cutoff 0 ((N : ℝ) * (m : ℝ))‖ ≤
        (N : ℝ) * (C / |(N : ℝ) * (m : ℝ)| ^ j) := by
      gcongr
    _ = C / (N : ℝ) ^ (j - 1) * (1 / |(m : ℝ)| ^ j) := by
      rw [hFreqAbs, mul_pow]
      have hjEq : j = (j - 1) + 1 := by omega
      rw [hjEq, pow_succ]
      field_simp
      congr 1

/-- Arbitrary-order uniform bound for the complete nonzero-frequency tail.
The constant is independent of the scale `N`. -/
theorem gmTraceFourier_zero_nonzero_tail_bound (cutoff : GMSmoothCutoff)
    (j : ℕ) (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ), 0 < N →
      ‖gmTraceNonzeroTail cutoff N‖ ≤ K / (N : ℝ) ^ (j - 1) := by
  obtain ⟨C, hC, hPointwise⟩ :=
    gmTraceFourier_zero_nonzero_pointwise_bound cutoff j hj
  have hPSeries : Summable (fun m : ℤ ↦ ‖1 / (m : ℂ) ^ j‖) := by
    have hNorm : (fun m : ℤ ↦ ‖1 / (m : ℂ) ^ j‖) =
        fun m : ℤ ↦ |1 / (m : ℝ) ^ j| := by
      funext m
      simp only [norm_div, norm_one, norm_pow, Complex.norm_intCast,
        abs_div, abs_one, pow_abs]
    rw [hNorm, summable_abs_iff]
    exact Real.summable_one_div_int_pow.mpr (by omega)
  let B : ℝ := ∑' m : ℤ, ‖1 / (m : ℂ) ^ j‖
  have hB : 0 ≤ B := tsum_nonneg fun m ↦ norm_nonneg _
  refine ⟨C * B + 1, by positivity, ?_⟩
  intro N hN
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  let scale : ℝ := C / (N : ℝ) ^ (j - 1)
  have hComparison : ∀ m : ℤ,
      ‖if m = 0 then 0 else
          (N : ℂ) * gmTraceFourier cutoff 0 ((N : ℝ) * (m : ℝ))‖ ≤
        scale * ‖1 / (m : ℂ) ^ j‖ := by
    intro m
    by_cases hm : m = 0
    · have hjZero : j ≠ 0 := by omega
      simp [hm, hjZero]
    · simpa only [if_false, hm, scale] using hPointwise N hN m hm
  have hScaledSummable : Summable (fun m : ℤ ↦ scale * ‖1 / (m : ℂ) ^ j‖) :=
    hPSeries.mul_left scale
  have hBound := tsum_of_norm_bounded hScaledSummable.hasSum hComparison
  rw [tsum_mul_left] at hBound
  change ‖gmTraceNonzeroTail cutoff N‖ ≤ scale * B at hBound
  calc
    ‖gmTraceNonzeroTail cutoff N‖ ≤ scale * B := hBound
    _ ≤ (C * B + 1) / (N : ℝ) ^ (j - 1) := by
      dsimp only [scale]
      have hPow : 0 < (N : ℝ) ^ (j - 1) := by positivity
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hPow).2
      exact le_add_of_nonneg_right zero_le_one

/-- Exact first-trace Poisson expansion with the zero Fourier mode isolated. -/
theorem gmMatrix_gram_trace_poisson_expand (cutoff : GMSmoothCutoff)
    (N : ℕ) (hN : 0 < N) (W : Finset ℝ) :
    Matrix.trace (gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose) =
      (W.card : ℂ) *
        ((N : ℂ) * gmTraceFourier cutoff 0 0 + gmTraceNonzeroTail cutoff N) := by
  rw [gmMatrix_gram_trace_eq_cutoff_sum]
  rw [← gmTraceKernel_zero_tsum_eq_column_sum cutoff N hN]
  rw [gmTraceKernel_poisson cutoff 0 (N : ℝ) (by exact_mod_cast hN)]
  have hCast : (((N : ℝ) : ℂ)) = (N : ℂ) := by norm_num
  simp_rw [hCast]
  have hSummable : Summable (fun m : ℤ ↦
      (N : ℂ) * gmTraceFourier cutoff 0 ((N : ℝ) * (m : ℝ))) := by
    simpa only [hCast] using
      gmScaledTraceFourier_summable cutoff 0 (N : ℝ) (by exact_mod_cast hN)
  rw [hSummable.tsum_eq_add_tsum_ite 0]
  simp only [Int.cast_zero, mul_zero, gmTraceNonzeroTail]

/-- Source-faithful Guth--Maynard Hilbert--Schmidt estimate with the hidden
polynomial-cardinality exponent made explicit. -/
theorem gmMatrix_hilbertSchmidt_trace_estimate (cutoff : GMSmoothCutoff)
    (A J : ℕ) (hJ : 1 ≤ J) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ), 0 < N →
      (W.card : ℝ) ≤ (N : ℝ) ^ A →
      ‖Matrix.trace (gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose) -
          (N : ℂ) * (W.card : ℂ) * (gmCutoffL2Sq cutoff : ℂ)‖ ≤
        K / (N : ℝ) ^ J := by
  let j : ℕ := A + J + 1
  have hj : 2 ≤ j := by dsimp only [j]; omega
  obtain ⟨K, hK, hTail⟩ := gmTraceFourier_zero_nonzero_tail_bound cutoff j hj
  refine ⟨K, hK, ?_⟩
  intro N W hN hCard
  have hDifference :
      Matrix.trace (gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose) -
          (N : ℂ) * (W.card : ℂ) * (gmCutoffL2Sq cutoff : ℂ) =
        (W.card : ℂ) * gmTraceNonzeroTail cutoff N := by
    rw [gmMatrix_gram_trace_poisson_expand cutoff N hN W,
      gmTraceFourier_zero_zero_eq_cutoffL2Sq]
    ring
  rw [hDifference, norm_mul, Complex.norm_natCast]
  calc
    (W.card : ℝ) * ‖gmTraceNonzeroTail cutoff N‖ ≤
        (N : ℝ) ^ A * (K / (N : ℝ) ^ (j - 1)) := by
      exact mul_le_mul hCard (hTail N hN) (norm_nonneg _) (by positivity)
    _ = K / (N : ℝ) ^ J := by
      have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hjSub : j - 1 = A + J := by dsimp only [j]; omega
      rw [hjSub, pow_add]
      field_simp

/-- Literal `O(N⁻¹⁰⁰)` form of Guth--Maynard Lemma 4.4. -/
theorem gmMatrix_hilbertSchmidt_trace_estimate_hundred
    (cutoff : GMSmoothCutoff) (A : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (N : ℕ) (W : Finset ℝ), 0 < N →
      (W.card : ℝ) ≤ (N : ℝ) ^ A →
      ‖Matrix.trace (gmMatrix cutoff N W * (gmMatrix cutoff N W).conjTranspose) -
          (N : ℂ) * (W.card : ℂ) * (gmCutoffL2Sq cutoff : ℂ)‖ ≤
        K / (N : ℝ) ^ 100 := by
  exact gmMatrix_hilbertSchmidt_trace_estimate cutoff A 100 (by norm_num)

end RiemannZeta.GuthMaynard
