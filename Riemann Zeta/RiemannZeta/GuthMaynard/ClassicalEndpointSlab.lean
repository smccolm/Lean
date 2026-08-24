import RiemannZeta.GuthMaynard.ClassicalDichotomy
import RiemannZeta.GuthMaynard.TypeIFiniteWindow
import RiemannZeta.GuthMaynard.TypeISmoothing
import RiemannZeta.GuthMaynard.TypeIReflection
import RiemannZeta.GuthMaynard.TypeIFourierDeweight
import RiemannZeta.GuthMaynard.DFIDivisorEpsilon

open Complex Finset MeasureTheory Real Set Filter Asymptotics Topology
open scoped BigOperators ContDiff FourierTransform SchwartzMap

namespace RiemannZeta.GuthMaynard

/-!
# Finite branch-to-slab assembly for the classical density endpoints

This file contains the final consumer of the finite classical detector
dichotomy.  The preliminary lemmas below make the power selection and the
sub-polynomial losses explicit; they are used by the Type-I and Type-II
witness consumers later in the file.
-/

/-! ## The nonstationary zero Poisson mode -/

/-- Fixed logarithmic Mellin kernel for the zero Poisson mode of an
interior Type-I block.  Its dependence on the zero-density line is explicit,
while it is independent of the physical scale and ordinate. -/
noncomputable def typeIZeroMellinKernel (σ u : ℝ) : ℂ :=
  (Real.exp (-u) : ℂ) *
    typeINormalizedAmplitude σ (Real.exp (-u))

theorem contDiff_typeIZeroMellinKernel (σ : ℝ) :
    ContDiff ℝ ∞ (typeIZeroMellinKernel σ) := by
  have hExp : ContDiff ℝ ∞ (fun u : ℝ => Real.exp (-u)) :=
    Real.contDiff_exp.comp contDiff_neg
  exact (Complex.ofRealCLM.contDiff.comp hExp).mul
    ((contDiff_typeINormalizedAmplitude σ).comp hExp)

theorem hasCompactSupport_typeIZeroMellinKernel (σ : ℝ) :
    HasCompactSupport (typeIZeroMellinKernel σ) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact
      (Set.Icc (-Real.log 2) (Real.log 2)))
  intro u hu
  have hcut : typeIDyadicCutoff (Real.exp (-u)) = 0 := by
    by_cases hLow : u < -Real.log 2
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      apply Real.exp_le_exp.mpr
      linarith
    · have hHigh : Real.log 2 < u := by
        exact lt_of_not_ge fun hu' => hu ⟨le_of_not_gt hLow, hu'⟩
      apply typeIDyadicCutoff_eq_zero_of_le_half
      rw [show (1 / 2 : ℝ) = Real.exp (-Real.log 2) by
        rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        norm_num]
      exact Real.exp_le_exp.mpr (by linarith)
  simp [typeIZeroMellinKernel, typeINormalizedAmplitude, hcut]

/-- Schwartz realization of the fixed zero-mode Mellin kernel. -/
noncomputable def typeIZeroMellinKernelSchwartz (σ : ℝ) : 𝓢(ℝ, ℂ) :=
  (hasCompactSupport_typeIZeroMellinKernel σ).toSchwartzMap
    (contDiff_typeIZeroMellinKernel σ)

@[simp]
theorem typeIZeroMellinKernelSchwartz_apply (σ u : ℝ) :
    typeIZeroMellinKernelSchwartz σ u = typeIZeroMellinKernel σ u := rfl

/-- The zero spatial Fourier coefficient is the Mellin transform of the
fixed normalized amplitude on the vertical line with ordinate `-t`. -/
theorem typeINormalizedFourier_zero_eq_mellin (σ t : ℝ) :
    typeINormalizedFourier σ t 0 =
      mellin (typeINormalizedAmplitude σ)
        ((1 : ℂ) - (t : ℂ) * Complex.I) := by
  have hIntegrable : Integrable (typeINormalizedKernel σ t) :=
    (typeINormalizedKernelSchwartz σ t).integrable
  have hOutside :
      ∫ x : ℝ in (Set.Ioi 0)ᶜ, typeINormalizedKernel σ t x = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    have hxNonpos : x ≤ 0 := by simpa using hx
    have hcut : typeIDyadicCutoff x = 0 :=
      typeIDyadicCutoff_eq_zero_of_le_half (hxNonpos.trans (by norm_num))
    simp [typeINormalizedKernel, typeINormalizedAmplitude, hcut]
  have hWhole :
      ∫ x : ℝ, typeINormalizedKernel σ t x =
        ∫ x : ℝ in Set.Ioi 0, typeINormalizedKernel σ t x := by
    have hSplit := integral_add_compl
      (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ))) hIntegrable
    rw [hOutside, add_zero] at hSplit
    exact hSplit.symm
  rw [typeINormalizedFourier, SchwartzMap.fourier_coe, Real.fourier_eq']
  simp only [Real.inner_apply, mul_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul, typeINormalizedKernelSchwartz_apply]
  rw [hWhole, mellin]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  have hxPos : 0 < x := hx
  have hxNe : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hxPos.ne'
  change typeINormalizedAmplitude σ x *
      Complex.exp ((((-t * Real.log x : ℝ) : ℂ) * Complex.I)) =
    (x : ℂ) ^ ((1 : ℂ) - (t : ℂ) * Complex.I - 1) *
      typeINormalizedAmplitude σ x
  rw [Complex.cpow_def_of_ne_zero hxNe]
  rw [← Complex.ofReal_log hxPos.le]
  rw [mul_comm (typeINormalizedAmplitude σ x)]
  apply congrArg (fun z : ℂ => z * typeINormalizedAmplitude σ x)
  apply congrArg Complex.exp
  push_cast
  ring

/-- Exact logarithmic Fourier representation of the zero Poisson mode. -/
theorem typeINormalizedFourier_zero_eq_mellinKernel_fourier (σ t : ℝ) :
    typeINormalizedFourier σ t 0 =
      𝓕 (typeIZeroMellinKernelSchwartz σ)
        (-t / (2 * Real.pi)) := by
  rw [typeINormalizedFourier_zero_eq_mellin, mellin_eq_fourier,
    SchwartzMap.fourier_coe]
  simp only [Complex.sub_re, Complex.one_re, Complex.mul_re,
    Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im,
    mul_zero, sub_zero, Complex.sub_im, Complex.one_im,
    mul_one, zero_sub]
  have hfreq : -(((t : ℂ) * Complex.I).im) / (2 * Real.pi) =
      -t / (2 * Real.pi) := by
    simp
  rw [hfreq]
  apply congrArg (fun f : ℝ → ℂ => 𝓕 f (-t / (2 * Real.pi)))
  funext u
  rw [typeIZeroMellinKernelSchwartz_apply]
  unfold typeIZeroMellinKernel
  rw [show -1 * u = -u by ring, Complex.real_smul]

/-- Arbitrary polynomial decay of the zero Poisson mode, uniformly in the
ordinate.  This is the term that must be removed before a large smooth
source block can force a genuinely nonzero reflected frequency. -/
theorem typeINormalizedFourier_zero_uniform_decay (σ : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |t| ^ j * ‖typeINormalizedFourier σ t 0‖ ≤ C := by
  obtain ⟨C, hC, hBound⟩ :=
    (𝓕 (typeIZeroMellinKernelSchwartz σ)).decay j 0
  let scale : ℝ := 2 * Real.pi
  have hScale : 0 < scale := by dsimp only [scale]; positivity
  refine ⟨scale ^ j * C, mul_pos (pow_pos hScale j) hC, ?_⟩
  intro t
  rw [typeINormalizedFourier_zero_eq_mellinKernel_fourier]
  have hAbs : |t| = scale * |-t / scale| := by
    rw [abs_div, abs_neg, abs_of_pos hScale]
    field_simp [hScale.ne']
  rw [hAbs, mul_pow]
  calc
    scale ^ j * |-t / scale| ^ j *
          ‖𝓕 (typeIZeroMellinKernelSchwartz σ) (-t / scale)‖ =
        scale ^ j *
          (‖-t / scale‖ ^ j *
            ‖𝓕 (typeIZeroMellinKernelSchwartz σ) (-t / scale)‖) := by
              rw [Real.norm_eq_abs]
              ring
    _ ≤ scale ^ j * C := by
      gcongr
      simpa only [norm_iteratedFDeriv_zero] using hBound (-t / scale)

/-! ## A fixed logarithmic kernel for interior Type-I blocks -/

/-- After the artificial detector boundary has disappeared, every smooth
Type-I block is a translate and scalar multiple of this one fixed logarithmic
Schwartz profile.  Keeping the profile independent of the physical scale is
what makes its Fourier `L¹` norm a legitimate endpoint constant. -/
noncomputable def typeIInteriorLogProfile (σ u : ℝ) : ℂ :=
  (typeIDyadicCutoff (Real.exp u) : ℂ) *
    Complex.exp ((((-σ * u : ℝ) : ℂ)))

theorem contDiff_typeIInteriorLogProfile (σ : ℝ) :
    ContDiff ℝ ∞ (typeIInteriorLogProfile σ) := by
  unfold typeIInteriorLogProfile
  have hcut : ContDiff ℝ ∞ (fun u : ℝ =>
      (typeIDyadicCutoff (Real.exp u) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (contDiff_typeIDyadicCutoff.comp Real.contDiff_exp)
  have hpow : ContDiff ℝ ∞ (fun u : ℝ =>
      Complex.exp ((((-σ * u : ℝ) : ℂ)))) := by
    have hinside : ContDiff ℝ ∞ (fun u : ℝ => -σ * u) :=
      contDiff_const.mul contDiff_id
    exact Complex.contDiff_exp.comp
      (Complex.ofRealCLM.contDiff.comp hinside)
  exact hcut.mul hpow

theorem hasCompactSupport_typeIInteriorLogProfile (σ : ℝ) :
    HasCompactSupport (typeIInteriorLogProfile σ) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact
      (Set.Icc (Real.log (1 / 2 : ℝ)) (Real.log 2)))
  intro u hu
  rw [Set.mem_Icc, not_and_or] at hu
  have hcut : typeIDyadicCutoff (Real.exp u) = 0 := by
    rcases hu with hu | hu
    · apply typeIDyadicCutoff_eq_zero_of_le_half
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2)]
      exact Real.exp_le_exp.mpr (le_of_lt (lt_of_not_ge hu))
    · apply typeIDyadicCutoff_eq_zero_of_two_le
      rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      exact Real.exp_le_exp.mpr (le_of_lt (lt_of_not_ge hu))
  unfold typeIInteriorLogProfile
  rw [hcut]
  simp

/-- Schwartz realization of the scale-independent interior log profile. -/
noncomputable def typeIInteriorLogProfileSchwartz (σ : ℝ) :
    SchwartzMap ℝ ℂ :=
  (hasCompactSupport_typeIInteriorLogProfile σ).toSchwartzMap
    (contDiff_typeIInteriorLogProfile σ)

@[simp]
theorem typeIInteriorLogProfileSchwartz_apply (σ u : ℝ) :
    typeIInteriorLogProfileSchwartz σ u =
      typeIInteriorLogProfile σ u := rfl

/-- The finite, positive Fourier `L¹` constant of the fixed log profile.
It may depend on the fixed vertical line `σ`, but not on `T`, the dyadic
scale, the selected block, or the ordinate. -/
noncomputable def typeIInteriorFourierL1 (σ : ℝ) : ℝ :=
  1 + ∫ ξ : ℝ, ‖𝓕 (typeIInteriorLogProfileSchwartz σ) ξ‖

theorem typeIInteriorFourierL1_pos (σ : ℝ) :
    0 < typeIInteriorFourierL1 σ := by
  unfold typeIInteriorFourierL1
  have hnonneg : 0 ≤ ∫ ξ : ℝ,
      ‖𝓕 (typeIInteriorLogProfileSchwartz σ) ξ‖ :=
    integral_nonneg fun _ => norm_nonneg _
  linarith

theorem integral_norm_fourier_typeIInteriorLogProfile_le (σ : ℝ) :
    (∫ ξ : ℝ, ‖𝓕 (typeIInteriorLogProfileSchwartz σ) ξ‖) ≤
      typeIInteriorFourierL1 σ := by
  unfold typeIInteriorFourierL1
  linarith

/-- Exact scale normalization of the fixed logarithmic profile. -/
theorem typeIInteriorLogProfile_scale_identity
    {Q n : ℕ} {σ : ℝ} (hQ : 0 < Q) (hn : 0 < n) :
    (((Q : ℝ) ^ (-σ) : ℝ) : ℂ) *
        typeIInteriorLogProfile σ
          (Real.log (n : ℝ) - Real.log (Q : ℝ)) =
      (typeIDyadicCutoff ((n : ℝ) / Q) : ℂ) *
        (n : ℂ) ^ (-(σ : ℂ)) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hQne : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hnne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnbase : (n : ℂ) = ((n : ℝ) : ℂ) := by norm_num
  unfold typeIInteriorLogProfile
  have hexp : Real.exp (Real.log (n : ℝ) - Real.log (Q : ℝ)) =
      (n : ℝ) / Q := by
    rw [Real.exp_sub, Real.exp_log hnr, Real.exp_log hQr]
  rw [hexp]
  rw [hnbase, Complex.cpow_def_of_ne_zero (hnbase ▸ hnne),
    ← Complex.ofReal_log hnr.le]
  rw [Real.rpow_def_of_pos hQr, Complex.ofReal_exp]
  calc
    Complex.exp (((Real.log (Q : ℝ) * -σ : ℝ) : ℂ)) *
          ((typeIDyadicCutoff ((n : ℝ) / Q) : ℂ) *
            Complex.exp ((((-σ *
              (Real.log (n : ℝ) - Real.log (Q : ℝ)) : ℝ) : ℂ)))) =
        (typeIDyadicCutoff ((n : ℝ) / Q) : ℂ) *
          (Complex.exp (((Real.log (Q : ℝ) * -σ : ℝ) : ℂ)) *
            Complex.exp ((((-σ *
              (Real.log (n : ℝ) - Real.log (Q : ℝ)) : ℝ) : ℂ)))) := by
            ring
    _ = (typeIDyadicCutoff ((n : ℝ) / Q) : ℂ) *
          Complex.exp
            ((((Real.log (Q : ℝ) * -σ -
              σ * (Real.log (n : ℝ) - Real.log (Q : ℝ)) : ℝ) : ℂ))) := by
            rw [← Complex.exp_add]
            congr 2
            push_cast
            ring
    _ = (typeIDyadicCutoff ((n : ℝ) / Q) : ℂ) *
          Complex.exp (((Real.log (n : ℝ) : ℂ) * -(σ : ℂ))) := by
            congr 2
            push_cast
            ring

/-- Fourier inversion after a logarithmic translation.  The translation
contributes only a unit-modulus common factor, so the same fixed Fourier
`L¹` constant works at every physical dyadic scale. -/
theorem fourierDeweightFiniteBlock_logShift_native
    (f : SchwartzMap ℝ ℂ) (S : Finset ℕ) (t a : ℝ)
    (hS : ∀ n ∈ S, 0 < n) :
    (∑ n ∈ S, f (Real.log n - a) *
        (n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ∫ ξ : ℝ, 𝓕 f ξ *
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)) *
          ∑ n ∈ S,
            (n : ℂ) ^
              (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I) := by
  have hinversion (u : ℝ) :
      f u = ∫ ξ : ℝ,
        Complex.exp (((2 * Real.pi * (ξ * u) : ℝ) : ℂ) * Complex.I) *
          𝓕 f ξ := by
    have hpairMap : 𝓕⁻ (𝓕 f) = f :=
      FourierTransform.fourierInv_fourier_eq f
    have hpair := congrArg (fun g : SchwartzMap ℝ ℂ => g u) hpairMap
    change (𝓕⁻ (𝓕 f)) u = f u at hpair
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq'] at hpair
    simpa only [Real.inner_apply, smul_eq_mul] using hpair.symm
  have hintegrable (n : ℕ) (hn : 0 < n) : Integrable
      (fun ξ : ℝ => 𝓕 f ξ *
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)) *
          (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)) := by
    have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    have hcontinuous : Continuous (fun ξ : ℝ =>
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)) *
          (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)) := by
      apply Continuous.mul
      · fun_prop
      · apply Continuous.const_cpow
        · fun_prop
        · exact Or.inl hnNe
    have hfIntegrable : Integrable (fun ξ : ℝ => 𝓕 f ξ) :=
      (𝓕 f).integrable
    have hbound : ∀ᵐ ξ : ℝ ∂MeasureTheory.volume,
        ‖Complex.exp
              (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)) *
            (n : ℂ) ^
              (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)‖ ≤ 1 := by
      filter_upwards with ξ
      rw [norm_mul, Complex.norm_exp,
        Complex.norm_natCast_cpow_of_pos hn]
      simp
    have hInt := hfIntegrable.mul_bdd (c := 1)
      hcontinuous.aestronglyMeasurable hbound
    simpa only [mul_assoc] using hInt
  calc
    (∑ n ∈ S, f (Real.log n - a) *
        (n : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ∑ n ∈ S, ∫ ξ : ℝ, 𝓕 f ξ *
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)) *
          (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro n hnS
      have hn := hS n hnS
      have hnNe : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [hinversion]
      rw [← MeasureTheory.integral_mul_const]
      apply integral_congr_ae
      filter_upwards with ξ
      have hphase :
          Complex.exp
                (((2 * Real.pi *
                  (ξ * (Real.log n - a)) : ℝ) : ℂ) * Complex.I) *
              (n : ℂ) ^ (-(t : ℂ) * Complex.I) =
            Complex.exp
                (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)) *
              (n : ℂ) ^
                (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I) := by
        rw [Complex.cpow_def_of_ne_zero hnNe,
          Complex.cpow_def_of_ne_zero hnNe]
        have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
        have hlog : Complex.log (n : ℂ) =
            (Real.log (n : ℝ) : ℂ) :=
          (Complex.ofReal_log hnReal.le).symm
        rw [hlog, ← Complex.exp_add, ← Complex.exp_add]
        congr 1
        push_cast
        ring
      calc
        (Complex.exp
              (((2 * Real.pi *
                (ξ * (Real.log n - a)) : ℝ) : ℂ) * Complex.I) *
            𝓕 f ξ) * (n : ℂ) ^ (-(t : ℂ) * Complex.I) =
          𝓕 f ξ *
            (Complex.exp
                (((2 * Real.pi *
                  (ξ * (Real.log n - a)) : ℝ) : ℂ) * Complex.I) *
              (n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by ring
        _ = 𝓕 f ξ *
            (Complex.exp
                (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)) *
              (n : ℂ) ^
                (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)) := by
              rw [hphase]
        _ = 𝓕 f ξ *
            Complex.exp
                (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)) *
              (n : ℂ) ^
                (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I) := by
              ring
    _ = ∫ ξ : ℝ, ∑ n ∈ S, 𝓕 f ξ *
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)) *
          (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I) := by
      rw [integral_finsetSum]
      intro n hn
      exact hintegrable n (hS n hn)
    _ = ∫ ξ : ℝ, 𝓕 f ξ *
        Complex.exp (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)) *
          ∑ n ∈ S,
            (n : ℂ) ^
              (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I) := by
      apply integral_congr_ae
      filter_upwards with ξ
      simpa only [mul_assoc] using
        (Finset.mul_sum S
          (fun n : ℕ => (n : ℂ) ^
            (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I))
          (𝓕 f ξ *
            Complex.exp
              (-(((2 * Real.pi * ξ * a : ℝ) : ℂ) * Complex.I)))).symm

/-- Exact Fourier representation of an actual interior smooth Type-I block.
The only scale factor outside the integral is the mathematically required
`Q^(-σ)`; the polynomial inside has literal coefficient one and contains no
ordinate-dependent coefficients. -/
theorem typeISourceSmoothBlock_eq_interior_fourier_deweight
    {Y A r : ℕ} {σ t : ℝ} (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A) :
    typeISourceSmoothBlock Y A r σ t =
      ((((2 ^ r * Y : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
        ∫ ξ : ℝ, 𝓕 (typeIInteriorLogProfileSchwartz σ) ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * Real.log (2 ^ r * Y : ℕ) : ℝ) : ℂ) *
              Complex.I)) *
            ∑ n ∈ Finset.Icc 1 (A + 1),
              (n : ℂ) ^
                (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I) := by
  let Q : ℕ := 2 ^ r * Y
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hPositive : ∀ n ∈ Finset.Icc 1 (A + 1), 0 < n := by
    intro n hn
    exact Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1
  have hFourier := fourierDeweightFiniteBlock_logShift_native
    (typeIInteriorLogProfileSchwartz σ) (Finset.Icc 1 (A + 1)) t
      (Real.log (Q : ℝ)) hPositive
  unfold typeISourceSmoothBlock
  calc
    ∑ n ∈ Finset.Icc 1 (A + 1),
        (typeISourceSmoothWeight Y A r n : ℂ) *
          (n : ℂ) ^ (-(σ : ℂ)) *
            (n : ℂ) ^ (-(t : ℂ) * Complex.I) =
      ((((Q : ℝ) ^ (-σ) : ℝ) : ℂ) *
        ∑ n ∈ Finset.Icc 1 (A + 1),
          typeIInteriorLogProfileSchwartz σ
              (Real.log n - Real.log (Q : ℝ)) *
            (n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
      calc
        ∑ n ∈ Finset.Icc 1 (A + 1),
            (typeISourceSmoothWeight Y A r n : ℂ) *
              (n : ℂ) ^ (-(σ : ℂ)) *
                (n : ℂ) ^ (-(t : ℂ) * Complex.I) =
          ∑ n ∈ Finset.Icc 1 (A + 1),
            (((Q : ℝ) ^ (-σ) : ℝ) : ℂ) *
              (typeIInteriorLogProfileSchwartz σ
                  (Real.log n - Real.log (Q : ℝ)) *
                (n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
          apply Finset.sum_congr rfl
          intro n hn
          have hnPos := hPositive n hn
          rw [typeIInteriorLogProfileSchwartz_apply]
          have hScale := typeIInteriorLogProfile_scale_identity
            (Q := Q) (n := n) (σ := σ) hQ hnPos
          rw [typeISourceSmoothWeight_eq_dyadic_of_interior hLower hUpper]
          simpa only [Q, mul_assoc] using congrArg
            (fun z : ℂ => z *
              (n : ℂ) ^ (-(t : ℂ) * Complex.I)) hScale.symm
        _ = (((Q : ℝ) ^ (-σ) : ℝ) : ℂ) *
            ∑ n ∈ Finset.Icc 1 (A + 1),
              typeIInteriorLogProfileSchwartz σ
                  (Real.log n - Real.log (Q : ℝ)) *
                (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
          exact (Finset.mul_sum _ _ _).symm
    _ = ((((Q : ℝ) ^ (-σ) : ℝ) : ℂ) *
        ∫ ξ : ℝ, 𝓕 (typeIInteriorLogProfileSchwartz σ) ξ *
          Complex.exp
            (-(((2 * Real.pi * ξ * Real.log (Q : ℝ) : ℝ) : ℂ) *
              Complex.I)) *
            ∑ n ∈ Finset.Icc 1 (A + 1),
              (n : ℂ) ^
                (-(((t - 2 * Real.pi * ξ : ℝ) : ℂ)) * Complex.I)) := by
      rw [hFourier]
    _ = _ := by rfl

/-- Every physical scale at least `4τ₀/3` can be returned to the basic
endpoint window by a positive integral power.  This is the finite form of
the interval covering used in ANTEDB Corollaries 11.7--11.8. -/
theorem exists_positive_power_scale_reduction
    {τ₀ τ : ℝ} (hτ₀ : 0 < τ₀) (hτ : 4 * τ₀ / 3 ≤ τ) :
    ∃ k : ℕ, 0 < k ∧ 2 * τ₀ / 3 ≤ τ / k ∧ τ / k ≤ τ₀ := by
  by_cases hUpper : τ ≤ 2 * τ₀
  · refine ⟨2, by omega, ?_, ?_⟩
    · norm_num
      linarith
    · norm_num
      linarith
  · let y : ℝ := 3 * τ / (2 * τ₀)
    let k : ℕ := ⌊y⌋₊
    have hτPos : 0 < τ := lt_of_lt_of_le (by positivity : 0 < 4 * τ₀ / 3) hτ
    have hyNonneg : 0 ≤ y := by
      dsimp [y]
      positivity
    have hyThree : 3 < y := by
      dsimp [y]
      rw [lt_div_iff₀ (by positivity : 0 < 2 * τ₀)]
      nlinarith
    have hkThree : 3 ≤ k := by
      dsimp [k]
      exact (Nat.le_floor_iff hyNonneg).2 hyThree.le
    have hkPos : 0 < k := by omega
    have hkUpper : (k : ℝ) ≤ y := Nat.floor_le hyNonneg
    have hyLt : y < (k : ℝ) + 1 := by
      exact_mod_cast Nat.lt_floor_add_one y
    have hτkUpper : τ / k ≤ τ₀ := by
      rw [div_le_iff₀ (by exact_mod_cast hkPos : (0 : ℝ) < k)]
      have hTwo : 2 * τ₀ < τ := lt_of_not_ge hUpper
      have hyLt' : 3 * τ < ((k : ℝ) + 1) * (2 * τ₀) := by
        apply (div_lt_iff₀ (by positivity : 0 < 2 * τ₀)).1
        simpa only [y] using hyLt
      nlinarith
    have hτkLower : 2 * τ₀ / 3 ≤ τ / k := by
      rw [le_div_iff₀ (by exact_mod_cast hkPos : (0 : ℝ) < k)]
      have hkUpper' : (k : ℝ) * (2 * τ₀) ≤ 3 * τ := by
        apply (le_div_iff₀ (by positivity : 0 < 2 * τ₀)).1
        simpa only [y] using hkUpper
      nlinarith
    exact ⟨k, hkPos, hτkLower, hτkUpper⟩

/-- The dyadic pigeonhole count is logarithmic, with an explicit real
majorant.  Keeping this estimate separate prevents a hidden power loss when
the dichotomy's multiplicity inequality is converted to an epsilon bound. -/
theorem natCast_clog_two_le_one_add_log (n : ℕ) (hn : 1 ≤ n) :
    (Nat.clog 2 n : ℝ) ≤ 1 + Real.log n / Real.log 2 := by
  by_cases hnOne : n = 1
  · subst n
    simp
  · have hnTwo : 1 < n := by omega
    have hkPos : 0 < Nat.clog 2 n :=
      Nat.clog_pos Nat.one_lt_two hnTwo
    have hpowNat : 2 ^ (Nat.clog 2 n - 1) < n :=
      Nat.pow_pred_clog_lt_self Nat.one_lt_two hnTwo
    have hpow : (0 : ℝ) < (2 ^ (Nat.clog 2 n - 1) : ℕ) := by positivity
    have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hnTwo)
    have hlog := Real.strictMonoOn_log (Set.mem_Ioi.mpr hpow)
      (Set.mem_Ioi.mpr hnPos) (by exact_mod_cast hpowNat)
    rw [Nat.cast_pow, Real.log_pow] at hlog
    have hcastSub : ((Nat.clog 2 n - 1 : ℕ) : ℝ) =
        (Nat.clog 2 n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num [Real.rpow_natCast]
    rw [hcastSub] at hlog
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hdiv : (Nat.clog 2 n : ℝ) - 1 ≤ Real.log n / Real.log 2 := by
      rw [le_div_iff₀ hlogTwo]
      simpa using hlog.le
    linarith

/-- Explicit logarithmic upper bound for the number of sharp-zeta dyadic
blocks. -/
theorem sharp_cutoff_clog_le_log_majorant (T : ℝ) (hT : 8 ≤ T) :
    (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) ≤
      1 + (Real.log 6 + Real.log T) / Real.log 2 := by
  have hTPos : 0 < T := by linarith
  have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
    linarith [four_mul_lt_sharpZetaCutoff T]
  have hAOne : 1 ≤ ⌊sharpZetaCutoff T⌋₊ := by
    apply (Nat.le_floor_iff hCutNonneg).2
    norm_num only [Nat.cast_one]
    exact (calc
      (1 : ℝ) ≤ 4 * T := by nlinarith
      _ < sharpZetaCutoff T := four_mul_lt_sharpZetaCutoff T).le
  have hFloor : (⌊sharpZetaCutoff T⌋₊ : ℝ) ≤ 6 * T := by
    exact (Nat.floor_le hCutNonneg).trans
      (sharpZetaCutoff_le_six_mul (by linarith))
  have hFloorPos : (0 : ℝ) < ⌊sharpZetaCutoff T⌋₊ := by exact_mod_cast hAOne
  have hLog : Real.log (⌊sharpZetaCutoff T⌋₊ : ℝ) ≤ Real.log (6 * T) :=
    Real.log_le_log hFloorPos hFloor
  rw [Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hTPos.ne'] at hLog
  exact (natCast_clog_two_le_one_add_log _ hAOne).trans (by
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    gcongr)

/-- The natural ceiling used for the displacement radius costs at most one
more than the underlying real power. -/
theorem natCast_ceil_rpow_lt_add_one
    (T δ : ℝ) (hT : 0 ≤ T) : (⌈T ^ δ⌉₊ : ℝ) < T ^ δ + 1 := by
  exact Nat.ceil_lt_add_one (Real.rpow_nonneg hT _)

/-- The Jensen multiplicity cap is an explicit affine function of `log T`,
up to the single unit introduced by the natural ceiling. -/
theorem localMultiplicityCap_lt_log_majorant (T : ℝ) (hT : 8 ≤ T) :
    (classicalLocalMultiplicityCap T : ℝ) <
      (Real.log (500 / 3 : ℝ) + 3 * Real.log T) /
          Real.log (35 / 32 : ℝ) + 1 := by
  have hTPos : 0 < T := by linarith
  have hConst : (0 : ℝ) < 500 / 3 := by norm_num
  have hArg : (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) =
      (500 / 3 : ℝ) * T ^ (3 : ℝ) := by ring
  have hLogPow : Real.log (T ^ (3 : ℝ)) = 3 * Real.log T := by
    rw [Real.log_rpow hTPos]
  have hArgOne : 1 ≤ (100 * T ^ (3 : ℝ)) / (0.6 : ℝ) := by
    rw [hArg]
    have hPowOne : 1 ≤ T ^ (3 : ℝ) :=
      Real.one_le_rpow (by linarith) (by norm_num)
    nlinarith
  have hDenNonneg : 0 ≤ Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) :=
    Real.log_nonneg (by norm_num)
  have hRatioNonneg : 0 ≤
      Real.log ((100 * T ^ (3 : ℝ)) / (0.6 : ℝ)) /
        Real.log ((7 / 4 : ℝ) / (8 / 5 : ℝ)) :=
    div_nonneg (Real.log_nonneg hArgOne) hDenNonneg
  have hCeil := Nat.ceil_lt_add_one hRatioNonneg
  have hDenEq : (7 / 4 : ℝ) / (8 / 5 : ℝ) = 35 / 32 := by norm_num
  simpa only [classicalLocalMultiplicityCap, hArg,
    Real.log_mul hConst.ne' (Real.rpow_pos_of_pos hTPos _).ne', hLogPow,
    hDenEq] using hCeil

/-- A positive value of an actual sharp Type-I block forces its dyadic
starting point to lie strictly below the sharp cutoff. -/
theorem typeI_start_lt_cutoff_of_positive_large_value
    (C N : ℕ) (σ t V : ℝ) (hV : 0 < V)
    (hLarge : V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) :
    N < C := by
  by_contra hNC
  have hZero : dirichletPoly N (classicalZetaLongLineCoeff C σ) t = 0 := by
    unfold dirichletPoly classicalZetaLongLineCoeff
    apply Finset.sum_eq_zero
    intro n hn
    have hnC : C < n := lt_of_le_of_lt (le_of_not_gt hNC)
      (Finset.mem_Ioc.mp hn).1
    rw [if_neg (Nat.not_le_of_lt hnC), zero_mul]
  rw [hZero, norm_zero] at hLarge
  linarith

/-- Number of nonzero terms in the actual sharp-cutoff Type-I block.  The
minimum is needed because the cutoff may either end inside the dyadic block
or after its right endpoint. -/
def actualTypeISharpLength (C N : ℕ) : ℕ := min N (C - N)

/-- The literal Type-I polynomial returned by the classical dichotomy is a
weighted Weyl block, with no smoothing or coefficient replacement.  This is
the finite source-entry bridge needed by the exceptional zeta-polynomial
route. -/
theorem dirichletPoly_classicalZetaLongLineCoeff_eq_weightedWeylBlock
    (C N : ℕ) (σ t : ℝ) (hN : 0 < N) (hNC : N < C) :
    dirichletPoly N (classicalZetaLongLineCoeff C σ) t =
      weightedWeylBlock σ t (N + 1) (actualTypeISharpLength C N) := by
  rw [dirichletPoly_classicalZetaLongLineCoeff_eq_terminal C N σ t hN]
  unfold weightedWeylBlock actualTypeISharpLength
  simp only [Nat.cast_add, Nat.cast_one]
  symm
  have hSubset : Finset.range (min N (C - N)) ⊆ Finset.range N := by
    intro i hi
    have hiL : i < min N (C - N) := Finset.mem_range.mp hi
    exact Finset.mem_range.mpr (lt_of_lt_of_le hiL (min_le_left _ _))
  calc
    ∑ i ∈ Finset.range (min N (C - N)),
        ((N : ℝ) + 1 + (i : ℝ)) ^ (-σ) •
          unitaryPhase (logarithmicPhase t ((N : ℝ) + 1 + (i : ℝ))) =
      ∑ i ∈ Finset.range (min N (C - N)),
        if N + 1 + i ≤ C then
          ((N : ℝ) + 1 + (i : ℝ)) ^ (-σ) •
            unitaryPhase (logarithmicPhase t ((N : ℝ) + 1 + (i : ℝ))) else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        have hiL : i < min N (C - N) := Finset.mem_range.mp hi
        have hiDiff : i < C - N := lt_of_lt_of_le hiL (min_le_right _ _)
        have hCut : N + 1 + i ≤ C := by omega
        rw [if_pos hCut]
    _ = ∑ i ∈ Finset.range N,
        if N + 1 + i ≤ C then
          ((N : ℝ) + 1 + (i : ℝ)) ^ (-σ) •
            unitaryPhase (logarithmicPhase t ((N : ℝ) + 1 + (i : ℝ))) else 0 := by
        apply Finset.sum_subset hSubset
        intro i hiN hiL
        have hiDiff : C - N ≤ i := by
          by_contra h
          have hiN' : i < N := Finset.mem_range.mp hiN
          have hiDiff' : i < C - N := lt_of_not_ge h
          exact hiL (Finset.mem_range.mpr (lt_min hiN' hiDiff'))
        have hCut : ¬ N + 1 + i ≤ C := by omega
        rw [if_neg hCut]

/-- Source-facing Weyl bound for the exact sharp Type-I witness at an
arbitrary positive ordinate.  The cube-root substitution is carried out in
the theorem, so downstream code does not replace the physical ordinate by an
unrelated parameter. -/
theorem norm_actual_typeI_block_le_weyl
    (C N : ℕ) (σ t : ℝ) (hσ : 0 ≤ σ) (hN : 0 < N) (hNC : N < C)
    (htOne : 1 ≤ t) (hNt : ((N + 1 : ℕ) : ℝ) ^ (2 : ℕ) ≤ t)
    (htN : t ≤ ((N + 1 : ℕ) : ℝ) ^ (3 : ℕ)) :
    ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖ ≤
      ((N + 1 : ℕ) : ℝ) ^ (-σ) *
        (30 * Real.sqrt (((N + 1 : ℕ) : ℝ) * t ^ (1 / 3 : ℝ))) := by
  let Y : ℝ := t ^ (1 / 3 : ℝ)
  let L : ℕ := actualTypeISharpLength C N
  have htPos : 0 < t := zero_lt_one.trans_le htOne
  have hYOne : 1 ≤ Y := by
    dsimp only [Y]
    exact Real.one_le_rpow htOne (by norm_num)
  have hYcube : Y ^ (3 : ℕ) = t := by
    dsimp only [Y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul htPos.le]
    norm_num
  have hYUpper : Y ≤ ((N + 1 : ℕ) : ℝ) := by
    have hRoot := Real.rpow_le_rpow htPos.le htN (by norm_num : (0 : ℝ) ≤ 1 / 3)
    have hBasePos : (0 : ℝ) < (N + 1 : ℕ) := by positivity
    have hRight :
        ((((N + 1 : ℕ) : ℝ) ^ (3 : ℕ)) ^ (1 / 3 : ℝ)) =
          ((N + 1 : ℕ) : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hBasePos.le]
      norm_num
    simpa only [Y, hRight] using hRoot
  have hLPos : 0 < L := by
    dsimp only [L, actualTypeISharpLength]
    exact lt_min hN (Nat.sub_pos_of_lt hNC)
  have hLUpper : L ≤ N + 1 := by
    dsimp only [L, actualTypeISharpLength]
    exact (min_le_left _ _).trans (Nat.le_succ _)
  rw [dirichletPoly_classicalZetaLongLineCoeff_eq_weightedWeylBlock
    C N σ t hN hNC]
  have hWeyl := actual_typeI_weyl_route_native σ Y (N + 1) L hσ hYOne
    (by omega) hLPos hYUpper (by simpa only [hYcube] using hNt) hLUpper
  simpa only [Y, hYcube] using hWeyl

/-- Exact tail-difference representation of the sharp Type-I block.  This is
the entry point for the smooth dyadic decomposition: both tails on the right
have the globally smooth expansion proved in `TypeISmoothing`. -/
theorem dirichletPoly_classicalZetaLongLineCoeff_eq_tail_sub_tail
    (C N : ℕ) (σ t : ℝ) (hN : 0 < N) :
    dirichletPoly N (classicalZetaLongLineCoeff C σ) t =
      classicalZetaLongTail N C ((σ : ℂ) + Complex.I * (t : ℂ)) -
        classicalZetaLongTail (2 * N) C
          ((σ : ℂ) + Complex.I * (t : ℂ)) := by
  classical
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  let f : ℕ → ℂ := fun n => (n : ℂ) ^ (-s)
  have hSub : Finset.Ioc (2 * N) C ⊆ Finset.Ioc N C := by
    intro n hn
    have h := Finset.mem_Ioc.mp hn
    exact Finset.mem_Ioc.mpr ⟨by omega, h.2⟩
  have hDiff : Finset.Ioc N C \ Finset.Ioc (2 * N) C =
      Finset.Ioc N (min (2 * N) C) := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Ioc, not_and_or]
    constructor
    · rintro ⟨⟨hNn, hnC⟩, hnTwo | hnC'⟩
      · exact ⟨hNn, le_min (by omega) hnC⟩
      · exact (hnC' hnC).elim
    · intro hn
      exact ⟨⟨hn.1, le_trans hn.2 (min_le_right _ _)⟩,
        Or.inl (by omega)⟩
  have hTail :
      (∑ n ∈ Finset.Ioc N (min (2 * N) C), f n) =
        (∑ n ∈ Finset.Ioc N C, f n) -
          ∑ n ∈ Finset.Ioc (2 * N) C, f n := by
    have hSplit := Finset.sum_sdiff hSub (f := f)
    rw [hDiff] at hSplit
    rw [← hSplit]
    ring
  rw [show classicalZetaLongTail N C ((σ : ℂ) + Complex.I * (t : ℂ)) =
      ∑ n ∈ Finset.Ioc N C, f n by rfl,
    show classicalZetaLongTail (2 * N) C
        ((σ : ℂ) + Complex.I * (t : ℂ)) =
      ∑ n ∈ Finset.Ioc (2 * N) C, f n by rfl,
    ← hTail]
  unfold dirichletPoly dyadicInterval
  symm
  have hSmall : Finset.Ioc N (min (2 * N) C) ⊆
      Finset.Ioc N (2 * N) := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      le_trans (Finset.mem_Ioc.mp hn).2 (min_le_left _ _)⟩
  calc
    (∑ n ∈ Finset.Ioc N (min (2 * N) C), f n) =
        ∑ n ∈ Finset.Ioc N (min (2 * N) C),
          classicalZetaLongLineCoeff C σ n *
            (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnData := Finset.mem_Ioc.mp hn
      have hnPos : 0 < n := lt_of_le_of_lt (Nat.zero_le N) hnData.1
      have hnC : n ≤ C := le_trans hnData.2 (min_le_right _ _)
      symm
      simpa only [f, s] using
        classicalZetaLongLineCoeff_term C n σ t hnPos hnC
    _ = ∑ n ∈ Finset.Ioc N (2 * N),
          classicalZetaLongLineCoeff C σ n *
            (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
      apply Finset.sum_subset hSmall
      intro n hnBlock hnSmall
      have hnData := Finset.mem_Ioc.mp hnBlock
      have hnC : C < n := by
        by_contra h
        exact hnSmall (Finset.mem_Ioc.mpr
          ⟨hnData.1, le_min hnData.2 (le_of_not_gt h)⟩)
      simp [classicalZetaLongLineCoeff, Nat.not_le_of_lt hnC]

/-- Localized form of the preceding tail identity.  The sharp Type-I block
is one finite tail ending at `min (2N) C`; it is therefore decomposed into
only two smooth source blocks, both at a scale comparable with the original
physical block.  This avoids the spurious long-tail scales introduced by
separating the two tails before smoothing. -/
theorem dirichletPoly_classicalZetaLongLineCoeff_eq_local_tail
    (C N : ℕ) (σ t : ℝ) (hN : 0 < N) :
    dirichletPoly N (classicalZetaLongLineCoeff C σ) t =
      classicalZetaLongTail N (min (2 * N) C)
        ((σ : ℂ) + Complex.I * (t : ℂ)) := by
  classical
  let s : ℂ := (σ : ℂ) + Complex.I * (t : ℂ)
  let f : ℕ → ℂ := fun n => (n : ℂ) ^ (-s)
  rw [dirichletPoly_classicalZetaLongLineCoeff_eq_tail_sub_tail C N σ t hN]
  change (∑ n ∈ Finset.Ioc N C, f n) -
      ∑ n ∈ Finset.Ioc (2 * N) C, f n =
    ∑ n ∈ Finset.Ioc N (min (2 * N) C), f n
  have hSub : Finset.Ioc (2 * N) C ⊆ Finset.Ioc N C := by
    intro n hn
    have hnData := Finset.mem_Ioc.mp hn
    have hNleTwoN : N ≤ 2 * N := by omega
    exact Finset.mem_Ioc.mpr ⟨hNleTwoN.trans_lt hnData.1, hnData.2⟩
  have hDiff : Finset.Ioc N C \ Finset.Ioc (2 * N) C =
      Finset.Ioc N (min (2 * N) C) := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_Ioc, not_and_or]
    constructor
    · rintro ⟨⟨hNn, hnC⟩, hnTwo | hnC'⟩
      · exact ⟨hNn, le_min (by omega) hnC⟩
      · exact (hnC' hnC).elim
    · intro hn
      exact ⟨⟨hn.1, hn.2.trans (min_le_right _ _)⟩,
        Or.inl (by omega)⟩
  have hSplit := Finset.sum_sdiff hSub (f := f)
  rw [hDiff] at hSplit
  exact sub_eq_iff_eq_add.mpr hSplit.symm

/-- Exact two-block smooth decomposition of the actual sharp Type-I
polynomial.  Both blocks retain the original starting scale `N`; no
uncontrolled scale from the full zeta tail appears. -/
theorem dirichletPoly_classicalZetaLongLineCoeff_eq_two_source_blocks
    (C N : ℕ) (σ t : ℝ) (hN : 0 < N) :
    dirichletPoly N (classicalZetaLongLineCoeff C σ) t =
      ∑ r ∈ Finset.range 2,
        typeISourceSmoothBlock N (min (2 * N) C) r σ t := by
  rw [dirichletPoly_classicalZetaLongLineCoeff_eq_local_tail C N σ t hN]
  exact classicalZetaLongTail_eq_sum_sourceSmoothBlocks
    N (min (2 * N) C) 1 σ t hN
      (by simpa only [pow_one] using min_le_left (2 * N) C)

/-- Multiplicity-safe family extraction from the localized two-block
decomposition.  Unlike the earlier long-tail extraction, the selected
source block has scale exactly `N` or `2N`, so the physical logarithmic
scale remains tied to the dichotomy witness. -/
theorem exists_common_local_typeISourceSmoothBlock_of_sharp_large
    (C N : ℕ) (σ V : ℝ) (W : Finset ℝ)
    (hN : 0 < N) (hW : W.Nonempty)
    (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) :
    ∃ r ∈ Finset.range 2, ∃ W' : Finset ℝ,
      W' ⊆ W ∧ IsSeparated 1 W' ∧
      W.card ≤ 2 * W'.card ∧
      (∀ t ∈ W', V / 2 ≤
        ‖typeISourceSmoothBlock N (min (2 * N) C) r σ t‖) := by
  have hTailLarge : ∀ t ∈ W,
      V ≤ ‖classicalZetaLongTail N (min (2 * N) C)
        ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
    intro t ht
    rw [← dirichletPoly_classicalZetaLongLineCoeff_eq_local_tail
      C N σ t hN]
    exact hLarge t ht
  obtain ⟨r, hr, W', hW', hSep', hLarge', hCard⟩ :=
    exists_common_typeISmoothBlock_large N (min (2 * N) C) 1 σ V W
      hN (by simpa only [pow_one] using min_le_left (2 * N) C)
      hW hSeparated hTailLarge
  refine ⟨r, by simpa using hr, W', hW', hSep', ?_, ?_⟩
  · simpa using hCard
  · intro t ht
    simpa using hLarge' t ht

/-- A sharp Type-I witness selects one of the two genuine tail terms in its
tail-difference formula.  The selected side is uniform on a subfamily losing
at most a factor two.  This is the finite family bridge needed before the
source-faithful smooth dyadic extraction. -/
theorem exists_common_large_typeI_tail_of_sharp_block
    (C N : ℕ) (σ V : ℝ) (W : Finset ℝ)
    (hN : 0 < N) (hW : W.Nonempty)
    (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) :
    ∃ b ∈ Finset.range 2, ∃ W' : Finset ℝ,
      W' ⊆ W ∧ IsSeparated 1 W' ∧
      W.card ≤ 2 * W'.card ∧
      (∀ t ∈ W', V / 2 ≤
        ‖classicalZetaLongTail ((b + 1) * N) C
          ((σ : ℂ) + Complex.I * (t : ℂ))‖) := by
  classical
  have hEach : ∀ t ∈ W, ∃ b ∈ Finset.range 2,
      V / 2 ≤ ‖classicalZetaLongTail ((b + 1) * N) C
        ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
    intro t ht
    have hSharp := hLarge t ht
    rw [dirichletPoly_classicalZetaLongLineCoeff_eq_tail_sub_tail C N σ t hN]
      at hSharp
    have hTriangle := norm_sub_le
      (classicalZetaLongTail N C ((σ : ℂ) + Complex.I * (t : ℂ)))
      (classicalZetaLongTail (2 * N) C
        ((σ : ℂ) + Complex.I * (t : ℂ)))
    by_cases hFirst : V / 2 ≤
        ‖classicalZetaLongTail N C
          ((σ : ℂ) + Complex.I * (t : ℂ))‖
    · exact ⟨0, by simp, by simpa using hFirst⟩
    · have hSecond : V / 2 ≤
          ‖classicalZetaLongTail (2 * N) C
            ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
        by_contra hSecond'
        have hFirst' := lt_of_not_ge hFirst
        have hSecond'' := lt_of_not_ge hSecond'
        linarith
      exact ⟨1, by simp, by simpa [two_mul] using hSecond⟩
  let side : ℝ → ℕ := fun t =>
    if ht : t ∈ W then Classical.choose (hEach t ht) else 0
  have hSide : ∀ t ∈ W, side t ∈ Finset.range 2 := by
    intro t ht
    simp only [side, dif_pos ht]
    exact (Classical.choose_spec (hEach t ht)).1
  obtain ⟨b, hb, hcard⟩ := weighted_finite_pigeonhole W
    (Finset.range 2) (fun _ => 1) side hW hSide
  let W' := W.filter (fun t => side t = b)
  have hSubset : W' ⊆ W := Finset.filter_subset _ _
  have hSep' : IsSeparated 1 W' := by
    intro x hx y hy hxy
    exact hSeparated x (hSubset hx) y (hSubset hy) hxy
  have hLarge' : ∀ t ∈ W', V / 2 ≤
      ‖classicalZetaLongTail ((b + 1) * N) C
        ((σ : ℂ) + Complex.I * (t : ℂ))‖ := by
    intro t ht
    have htData := Finset.mem_filter.mp ht
    have hchosen := (Classical.choose_spec (hEach t htData.1)).2
    have hsideEq : Classical.choose (hEach t htData.1) = b := by
      simpa only [side, dif_pos htData.1] using htData.2
    simpa only [hsideEq] using hchosen
  refine ⟨b, hb, W', hSubset, hSep', ?_, hLarge'⟩
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.card_range, W'] using hcard

/-- Combining the exact tail selection with the smooth source decomposition
selects one side and one smooth dyadic scale uniformly over a subfamily.  All
losses are explicit natural cardinality factors. -/
theorem exists_common_typeISourceSmoothBlock_of_sharp_large
    (C N k : ℕ) (σ V : ℝ) (W : Finset ℝ)
    (hN : 0 < N) (hW : W.Nonempty)
    (hC : C ≤ 2 ^ k * N)
    (hSeparated : IsSeparated 1 W)
    (hLarge : ∀ t ∈ W,
      V ≤ ‖dirichletPoly N (classicalZetaLongLineCoeff C σ) t‖) :
    ∃ b ∈ Finset.range 2, ∃ r ∈ Finset.range (k + 1),
      ∃ W' : Finset ℝ, W' ⊆ W ∧ IsSeparated 1 W' ∧
        W.card ≤ 2 * (k + 1) * W'.card ∧
        (∀ t ∈ W', V / (2 * (k + 1 : ℕ)) ≤
          ‖typeISourceSmoothBlock ((b + 1) * N) C r σ t‖) := by
  obtain ⟨b, hb, Wb, hWb, hSepb, hCardb, hLargeb⟩ :=
    exists_common_large_typeI_tail_of_sharp_block C N σ V W
      hN hW hSeparated hLarge
  have hWbNonempty : Wb.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hEmpty
    have hWcardPos : 0 < W.card := Finset.card_pos.mpr hW
    have hWbcard : Wb.card = 0 := by simp [hEmpty]
    omega
  have hStart : 1 ≤ (b + 1) * N := by
    exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) hN.ne')
  have hCStart : C ≤ 2 ^ k * ((b + 1) * N) := by
    calc
      C ≤ 2 ^ k * N := hC
      _ ≤ 2 ^ k * ((b + 1) * N) := by
        gcongr
        exact Nat.le_mul_of_pos_left N (by omega)
  obtain ⟨r, hr, W', hW', hSep', hLarge', hCard'⟩ :=
    exists_common_typeISmoothBlock_large ((b + 1) * N) C k σ (V / 2)
      Wb hStart hCStart hWbNonempty hSepb hLargeb
  refine ⟨b, hb, r, hr, W', hW'.trans hWb, hSep', ?_, ?_⟩
  · calc
      W.card ≤ 2 * Wb.card := hCardb
      _ ≤ 2 * ((k + 1) * W'.card) := by gcongr
      _ = 2 * (k + 1) * W'.card := by ring
  · intro t ht
    have htLarge := hLarge' t ht
    simpa only [div_div, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_add,
      Nat.cast_one] using htLarge

/-! ## Exact algebra of the reflected finite polynomial -/

/-- The fixed-coefficient polynomial carried by the retained negative
Poisson modes.  The original ordinate occurs only through the ordinary
Dirichlet phase; the coefficients `m^sigma` are independent of it. -/
noncomputable def typeIReflectedFixedPolynomial
    (sigma u : ℝ) (M : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    (((m : ℝ) ^ sigma : ℝ) : ℂ) *
      (m : ℂ) ^ (((u : ℂ) * Complex.I))

/-- Exact removal of the ordinate from the coefficients in the Mellin
polynomial produced by the B-process.  The remaining scalar is common to
all retained modes and therefore does not compromise a large-values
argument. -/
theorem typeIReflectedMellinPolynomial_eq_fixed
    (sigma t Q : ℝ) (M : ℕ) (r : ℝ) (hQ : 0 < Q) :
    typeIReflectedMellinPolynomial sigma t Q M r =
      (Q : ℂ) * (Q : ℂ) ^ ((r : ℂ) * Complex.I) *
        typeIReflectedFixedPolynomial sigma (t + r) M := by
  unfold typeIReflectedMellinPolynomial typeIReflectedFixedPolynomial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hm).1
  have hmRealPos : (0 : ℝ) < m := by exact_mod_cast hmPos
  have hmComplex : (m : ℂ) ≠ 0 := by exact_mod_cast hmPos.ne'
  have hQComplex : (Q : ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hmLog : Complex.log (m : ℂ) = (Real.log (m : ℝ) : ℂ) :=
    (Complex.ofReal_log hmRealPos.le).symm
  have hQLog : Complex.log (Q : ℂ) = (Real.log Q : ℂ) :=
    (Complex.ofReal_log hQ.le).symm
  have hmSigma : ((((m : ℝ) ^ sigma : ℝ) : ℂ)) =
      Complex.exp (((sigma * Real.log (m : ℝ) : ℝ) : ℂ)) := by
    rw [Real.rpow_def_of_pos hmRealPos, Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hMulCast : ((((m : ℝ) * Q : ℝ) : ℂ)) = (m : ℂ) * (Q : ℂ) := by
    exact Complex.ofReal_mul (m : ℝ) Q
  have hMulPow : ((((m : ℝ) * Q : ℝ) : ℂ)) ^ ((r : ℂ) * Complex.I) =
      (m : ℂ) ^ ((r : ℂ) * Complex.I) *
        (Q : ℂ) ^ ((r : ℂ) * Complex.I) := by
    rw [hMulCast]
    exact Complex.mul_cpow_ofReal_nonneg hmRealPos.le hQ.le _
  unfold typeIReflectionScaleFactor
  rw [hMulPow, hMulCast, hmSigma,
    Complex.cpow_def_of_ne_zero hmComplex,
    Complex.cpow_def_of_ne_zero hQComplex,
    Complex.cpow_def_of_ne_zero hmComplex, hmLog, hQLog]
  field_simp [hmComplex]
  calc
    Complex.exp (((Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) *
          (m : ℂ) *
          Complex.exp (Complex.I * (Real.log (m : ℝ) : ℂ) * (r : ℂ)) =
        (m : ℂ) *
          (Complex.exp (((Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) *
            Complex.exp (Complex.I * (Real.log (m : ℝ) : ℂ) * (r : ℂ))) := by
      ring

    _ = (m : ℂ) * Complex.exp
          ((((Real.log (m : ℝ) * t : ℝ) : ℂ) * Complex.I) +
            Complex.I * (Real.log (m : ℝ) : ℂ) * (r : ℂ)) := by
      rw [Complex.exp_add]
    _ = (m : ℂ) * Complex.exp
          (Complex.I * (Real.log (m : ℝ) : ℂ) * ((t + r : ℝ) : ℂ)) := by
      congr 2
      push_cast
      ring

/-! ## Source-facing Poisson entry -/

/-- The bilateral source-kernel sum is exactly the finite smooth Type-I
block.  This closes the discrete entry edge into Poisson summation: negative
integers and zero vanish by the left source cutoff, while integers beyond
`A + 1` vanish by the right source cutoff. -/
theorem tsum_typeIReflectionKernel_eq_typeISourceSmoothBlock
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) :
    (∑' n : ℤ, typeIReflectionKernel Y A r σ t n) =
      typeISourceSmoothBlock Y A r σ t := by
  classical
  rw [tsum_eq_sum (s := Finset.Icc (1 : ℤ) (A + 1))]
  · unfold typeISourceSmoothBlock
    symm
    refine Finset.sum_bij
      (s := Finset.Icc 1 (A + 1))
      (t := Finset.Icc (1 : ℤ) (A + 1))
      (fun n _ => (n : ℤ)) ?_ ?_ ?_ ?_
    · intro n hn
      have hnData := Finset.mem_Icc.mp hn
      have hnLower : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hnData.1
      have hnUpper : (n : ℤ) ≤ (A + 1 : ℕ) := by exact_mod_cast hnData.2
      exact Finset.mem_Icc.mpr ⟨hnLower, hnUpper⟩
    · intro a₁ ha₁ a₂ ha₂ h
      exact Int.ofNat_inj.mp h
    · intro z hz
      have hzData := Finset.mem_Icc.mp hz
      have hzNonneg : 0 ≤ z := by omega
      refine ⟨z.toNat, ?_, ?_⟩
      · exact Finset.mem_Icc.mpr ⟨by
          exact Int.ofNat_le.mp (by
            simpa [Int.ofNat_toNat, hzNonneg] using hzData.1), by
          exact Int.ofNat_le.mp (by
            simpa [Int.ofNat_toNat, hzNonneg] using hzData.2)⟩
      · exact Int.toNat_of_nonneg hzNonneg
    · intro n hn
      have hnPos : 0 < n :=
        lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hn).1
      simpa using
        (typeIReflectionKernel_natCast Y A r n σ t hnPos).symm
  · intro z hz
    have hzOutside : z < 1 ∨ (A + 1 : ℤ) < z := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hz
    rcases hzOutside with hzLow | hzHigh
    · have hzReal : (z : ℝ) < (Y : ℝ) := by
        have hYReal : (1 : ℝ) ≤ Y := by exact_mod_cast hY
        exact_mod_cast hzLow.trans_le (by exact_mod_cast hYReal)
      have hleft : Real.smoothTransition ((z : ℝ) - (Y : ℝ)) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      have hweight : typeISourceSmoothWeight Y A r (z : ℝ) = 0 := by
        unfold typeISourceSmoothWeight typeITailBoundary
        rw [hleft, zero_mul, zero_mul]
      simp [typeIReflectionKernel, hweight]
    · have hzReal : (((A + 1 : ℕ) : ℝ)) ≤ (z : ℝ) := by
        exact_mod_cast hzHigh.le
      have hright : Real.smoothTransition
          (((A + 1 : ℕ) : ℝ) - (z : ℝ)) = 0 :=
        Real.smoothTransition.zero_of_nonpos (by linarith)
      have hweight : typeISourceSmoothWeight Y A r (z : ℝ) = 0 := by
        unfold typeISourceSmoothWeight typeITailBoundary
        rw [hright, mul_zero, zero_mul]
      simp [typeIReflectionKernel, hweight]

/-- Exact source-facing Poisson identity for a finite smooth Type-I block. -/
theorem typeISourceSmoothBlock_eq_poisson
    (Y A r : ℕ) (σ t : ℝ) (hY : 0 < Y) :
    typeISourceSmoothBlock Y A r σ t =
      ∑' m : ℤ, typeIReflectionFourier Y A r σ t hY m := by
  rw [← tsum_typeIReflectionKernel_eq_typeISourceSmoothBlock Y A r σ t hY]
  exact typeIReflection_poisson Y A r σ t hY

/-- The explicit scalar relating a physical Type-I block at scale `Q` to
the boundary-free normalized kernel on `[1/2,2]`. -/
noncomputable def typeISourceNormalizationScalar
    (σ t Q : ℝ) : ℂ :=
  Complex.exp (((-σ * Real.log Q : ℝ) : ℂ)) *
    Complex.exp ((((-t * Real.log Q : ℝ) : ℂ) * Complex.I))

theorem norm_typeISourceNormalizationScalar
    (σ t Q : ℝ) (hQ : 0 < Q) :
    ‖typeISourceNormalizationScalar σ t Q‖ = Q ^ (-σ) := by
  unfold typeISourceNormalizationScalar
  rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, mul_zero, Complex.I_im]
  norm_num
  rw [Real.rpow_def_of_pos hQ]
  congr 1
  ring

/-- Exact dilation identity between the physical logarithmic phase and the
normalized kernel.  No stationary approximation is used here. -/
theorem typeIDyadicPhysicalIntegrand_eq_sourceScalar_mul_normalized
    (σ t m Q x : ℝ) (hQ : 0 < Q) :
    typeIDyadicPhysicalIntegrand σ t m Q x =
      typeISourceNormalizationScalar σ t Q *
        (typeINormalizedKernel σ t (x / Q) *
          Complex.exp ((((2 * Real.pi * m * x : ℝ) : ℂ) * Complex.I))) := by
  by_cases hcut : typeIDyadicCutoff (x / Q) = 0
  · simp [typeIDyadicPhysicalIntegrand, typeINormalizedKernel,
      typeINormalizedAmplitude, hcut]
  · have hxQ : 0 < x / Q := by
      by_contra h
      exact hcut (typeIDyadicCutoff_eq_zero_of_le_half (by linarith))
    have hx : 0 < x := by
      have hmul : 0 < (x / Q) * Q := mul_pos hxQ hQ
      rwa [div_mul_cancel₀ x hQ.ne'] at hmul
    have hlog : Real.log (x / Q) = Real.log x - Real.log Q :=
      Real.log_div hx.ne' hQ.ne'
    have hpow :
        Complex.exp (((-σ * Real.log x : ℝ) : ℂ)) =
          Complex.exp (((-σ * Real.log Q : ℝ) : ℂ)) *
            Complex.exp (((-σ * (Real.log x - Real.log Q) : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hphase :
        Complex.exp
            (-((((t * Real.log x - 2 * Real.pi * m * x : ℝ) : ℂ) * Complex.I))) =
          Complex.exp ((((-t * Real.log Q : ℝ) : ℂ) * Complex.I)) *
            Complex.exp ((((-t * (Real.log x - Real.log Q) : ℝ) : ℂ) * Complex.I)) *
              Complex.exp ((((2 * Real.pi * m * x : ℝ) : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    unfold typeIDyadicPhysicalIntegrand typeISourceNormalizationScalar
      typeINormalizedKernel typeINormalizedAmplitude gmReflectionPowerWeight
    rw [hlog]
    rw [hpow, hphase]
    ring

/-- The interior source block is exactly the normalized lattice sum times
the explicit physical scalar. -/
theorem typeISourceSmoothBlock_eq_scaled_normalized_tsum_of_interior
    {Y A r : ℕ} {σ t : ℝ}
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A) :
    typeISourceSmoothBlock Y A r σ t =
      typeISourceNormalizationScalar σ t (2 ^ r * Y : ℕ) *
        ∑' n : ℤ,
          typeINormalizedKernel σ t
            ((n : ℝ) / ((2 ^ r * Y : ℕ) : ℝ)) := by
  let Q : ℕ := 2 ^ r * Y
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [← tsum_typeIReflectionKernel_eq_typeISourceSmoothBlock Y A r σ t hY]
  rw [typeIReflectionKernel_eq_dyadicPhysical_of_interior hLower hUpper]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [typeIDyadicPhysicalIntegrand_eq_sourceScalar_mul_normalized
    σ t 0 (Q : ℝ) (n : ℝ) hQr]
  norm_num [Q]

/-! ## Finite negative-mode extraction for the medium Type-I branch -/

/-- The physical dyadic integrand is supported on `[Q/2,2Q]`, uniformly in
the Fourier mode. -/
theorem integral_typeIDyadicPhysicalIntegrand_eq_dyadicInterval
    {sigma t m Q : ℝ} (hQ : 0 < Q) :
    (∫ x : ℝ, typeIDyadicPhysicalIntegrand sigma t m Q x) =
      ∫ x in Q / 2..2 * Q,
        typeIDyadicPhysicalIntegrand sigma t m Q x := by
  symm
  apply intervalIntegral.integral_eq_integral_of_support_subset
  intro x hx
  have hcut : typeIDyadicCutoff (x / Q) ≠ 0 := by
    intro hzero
    apply hx
    simp [typeIDyadicPhysicalIntegrand, hzero]
  have hlower : 1 / 2 < x / Q := by
    by_contra hnot
    exact hcut (typeIDyadicCutoff_eq_zero_of_le_half (le_of_not_gt hnot))
  have hupper : x / Q < 2 := by
    by_contra hnot
    exact hcut (typeIDyadicCutoff_eq_zero_of_two_le (le_of_not_gt hnot))
  rw [Set.mem_Ioc]
  constructor
  · have := (lt_div_iff₀ hQ).mp hlower
    nlinarith
  · exact ((div_lt_iff₀ hQ).mp hupper).le

/-- A negative normalized Poisson mode is exactly its physical oscillatory
integral after multiplication by the explicit source scalar. -/
theorem sourceScalar_mul_normalizedFourier_neg_eq_physicalIntegral
    (sigma t Q : ℝ) (m : ℕ) (hQ : 0 < Q) :
    typeISourceNormalizationScalar sigma t Q *
        ((Q : ℂ) * typeINormalizedFourier sigma t
          (Q * (-(m : ℝ)))) =
      ∫ x in Q / 2..2 * Q,
        typeIDyadicPhysicalIntegrand sigma t (m : ℝ) Q x := by
  have hScaled := typeINormalizedScaledKernel_fourier
    sigma t Q (-(m : ℝ)) hQ
  rw [SchwartzMap.fourier_coe, Real.fourier_eq'] at hScaled
  simp only [Real.inner_apply, typeINormalizedScaledKernelSchwartz_apply,
    smul_eq_mul] at hScaled
  rw [← integral_typeIDyadicPhysicalIntegrand_eq_dyadicInterval hQ]
  rw [← hScaled, ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  rw [typeIDyadicPhysicalIntegrand_eq_sourceScalar_mul_normalized
    sigma t (m : ℝ) Q x hQ]
  congr 1
  have hphase :
      Complex.exp
          (((-2 * Real.pi * (x * (-(m : ℝ))) : ℝ) : ℂ) * Complex.I) =
        Complex.exp
          ((((2 * Real.pi * (m : ℝ) * x : ℝ) : ℂ) * Complex.I)) := by
    congr 1
    push_cast
    ring
  rw [hphase]
  ring

/-- The finite retained negative-frequency contribution. -/
noncomputable def typeINormalizedNegativeModes
    (sigma t : ℝ) (Q M : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    (Q : ℂ) * typeINormalizedFourier sigma t
      ((Q : ℝ) * (-(m : ℝ)))

/-- The retained positive-frequency contribution. -/
noncomputable def typeINormalizedPositiveModes
    (sigma t : ℝ) (Q M : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 M,
    (Q : ℂ) * typeINormalizedFourier sigma t
      ((Q : ℝ) * (m : ℝ))

/-- Reversing the normalized Fourier frequency conjugates the kernel and
reverses the ordinate. -/
theorem typeINormalizedFourier_neg_eq_conj
    (sigma t ξ : ℝ) :
    typeINormalizedFourier sigma t (-ξ) =
      star (typeINormalizedFourier sigma (-t) ξ) := by
  rw [typeINormalizedFourier, SchwartzMap.fourier_coe, Real.fourier_eq',
    typeINormalizedFourier, SchwartzMap.fourier_coe, Real.fourier_eq']
  let f : ℝ → ℂ := fun x =>
    Complex.exp (((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I) •
      typeINormalizedKernelSchwartz sigma (-t) x
  have hConj : (∫ x : ℝ, star (f x)) = star (∫ x : ℝ, f x) := by
    simpa only using (integral_conj (f := f))
  rw [← hConj]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  dsimp only [f]
  simp only [Real.inner_apply, typeINormalizedKernelSchwartz_apply,
    Complex.star_def, smul_eq_mul]
  unfold typeINormalizedKernel typeINormalizedAmplitude
  rw [map_mul, map_mul, map_mul, ← Complex.exp_conj,
    ← Complex.exp_conj, ← Complex.exp_conj]
  push_cast
  ring_nf
  simp only [map_neg, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

theorem star_typeISourceNormalizationScalar
    (sigma t Q : ℝ) :
    star (typeISourceNormalizationScalar sigma (-t) Q) =
      typeISourceNormalizationScalar sigma t Q := by
  unfold typeISourceNormalizationScalar
  simp only [Complex.star_def, map_mul, ← Complex.exp_conj]
  push_cast
  ring_nf
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring_nf

/-- The retained positive modes are the conjugate of the retained negative
modes at the reversed ordinate. -/
theorem typeINormalizedPositiveModes_eq_conj_negative
    (sigma t : ℝ) (Q M : ℕ) :
    typeINormalizedPositiveModes sigma t Q M =
      star (typeINormalizedNegativeModes sigma (-t) Q M) := by
  unfold typeINormalizedPositiveModes typeINormalizedNegativeModes
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro m hm
  change (Q : ℂ) * typeINormalizedFourier sigma t ((Q : ℝ) * (m : ℝ)) =
    (starRingEnd ℂ) ((Q : ℂ) * typeINormalizedFourier sigma (-t)
      ((Q : ℝ) * (-(m : ℝ))))
  rw [map_mul]
  have hF := typeINormalizedFourier_neg_eq_conj sigma t
    (-((Q : ℝ) * (m : ℝ)))
  simp only [neg_neg] at hF
  change typeINormalizedFourier sigma t ((Q : ℝ) * (m : ℝ)) =
    (starRingEnd ℂ) (typeINormalizedFourier sigma (-t)
      (-((Q : ℝ) * (m : ℝ)))) at hF
  have harg : (Q : ℝ) * (-(m : ℝ)) = -((Q : ℝ) * (m : ℝ)) := by
    ring
  rw [harg]
  rw [hF]
  simp only [map_natCast]

/-- Elementary uniform bound for the fixed reflected polynomial. -/
theorem norm_typeIReflectedFixedPolynomial_le
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u : ℝ) (M : ℕ) :
    ‖typeIReflectedFixedPolynomial sigma u M‖ ≤
      (M : ℝ) * (M : ℝ) ^ sigma := by
  rw [typeIReflectedFixedPolynomial]
  calc
    ‖∑ m ∈ Finset.Icc 1 M,
        (((m : ℝ) ^ sigma : ℝ) : ℂ) *
          (m : ℂ) ^ (((u : ℂ) * Complex.I))‖ ≤
      ∑ m ∈ Finset.Icc 1 M,
        ‖(((m : ℝ) ^ sigma : ℝ) : ℂ) *
          (m : ℂ) ^ (((u : ℂ) * Complex.I))‖ := norm_sum_le _ _
    _ ≤ ∑ _m ∈ Finset.Icc 1 M, (M : ℝ) ^ sigma := by
      apply Finset.sum_le_sum
      intro m hm
      have hmData := Finset.mem_Icc.mp hm
      have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hmData.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
        Complex.norm_natCast_cpow_of_pos hmPos]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, sub_self, Real.rpow_zero,
        mul_one]
      have hmReal : (m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hmData.2
      exact Real.rpow_le_rpow (Nat.cast_nonneg m) hmReal hsigma
    _ = (M : ℝ) * (M : ℝ) ^ sigma := by
      simp

/-! ## Normalized reflected blocks

The medium Type-I consumer needs the output of the exact Mellin reflection
in the coefficient-uniform form required by Montgomery--Halász--Huxley.
The cutoff at `M` is part of the coefficient, so extending the prefix to the
next dyadic endpoint introduces no mathematical remainder. -/

/-- Finite Abel summation in a form tailored to reflected coefficient
deweighting. -/
theorem weighted_sum_eq_endpoint_sub_differences
    (w : ℕ → ℂ) (a : ℕ → ℂ) (M : ℕ) :
    (∑ m ∈ Finset.Icc 1 M, w m * a m) =
      w (M + 1) * (∑ m ∈ Finset.Icc 1 M, a m) -
        ∑ j ∈ Finset.Icc 1 M,
          (w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m) := by
  induction M with
  | zero => simp
  | succ M ih =>
      change (∑ m ∈ Finset.Icc 1 (M + 1), w m * a m) =
        w ((M + 1) + 1) * (∑ m ∈ Finset.Icc 1 (M + 1), a m) -
          ∑ j ∈ Finset.Icc 1 (M + 1),
            (w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m)
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1),
        Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih]
      ring

theorem sum_successive_differences (v : ℕ → ℝ) (M : ℕ) :
    (∑ j ∈ Finset.Icc 1 M, (v (j + 1) - v j)) = v (M + 1) - v 1 := by
  induction M with
  | zero => simp
  | succ M ih =>
      change (∑ j ∈ Finset.Icc 1 (M + 1), (v (j + 1) - v j)) =
        v ((M + 1) + 1) - v 1
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih]
      ring

theorem norm_weighted_sum_le_of_partial_sum
    (w : ℕ → ℂ) (a : ℕ → ℂ) (M : ℕ) (R W D : ℝ)
    (hR : 0 ≤ R)
    (hpartial : ∀ j ∈ Finset.Icc 1 M,
      ‖∑ m ∈ Finset.Icc 1 j, a m‖ ≤ R)
    (hendpoint : ‖w (M + 1)‖ ≤ W)
    (hdifference : (∑ j ∈ Finset.Icc 1 M, ‖w (j + 1) - w j‖) ≤ D) :
    ‖∑ m ∈ Finset.Icc 1 M, w m * a m‖ ≤ (W + D) * R := by
  have hpartialM : ‖∑ m ∈ Finset.Icc 1 M, a m‖ ≤ R := by
    by_cases hM : M = 0
    · subst M
      simpa using hR
    · exact hpartial M (Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩)
  have hW : 0 ≤ W := (norm_nonneg (w (M + 1))).trans hendpoint
  rw [weighted_sum_eq_endpoint_sub_differences]
  calc
    ‖w (M + 1) * (∑ m ∈ Finset.Icc 1 M, a m) -
        ∑ j ∈ Finset.Icc 1 M,
          (w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m)‖ ≤
      ‖w (M + 1) * (∑ m ∈ Finset.Icc 1 M, a m)‖ +
        ‖∑ j ∈ Finset.Icc 1 M,
          (w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m)‖ := norm_sub_le _ _
    _ ≤ W * R + ∑ j ∈ Finset.Icc 1 M, ‖w (j + 1) - w j‖ * R := by
      apply add_le_add
      · rw [norm_mul]
        exact mul_le_mul hendpoint hpartialM (norm_nonneg _) hW
      · calc
          ‖∑ j ∈ Finset.Icc 1 M,
              (w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m)‖ ≤
              ∑ j ∈ Finset.Icc 1 M,
                ‖(w (j + 1) - w j) * (∑ m ∈ Finset.Icc 1 j, a m)‖ :=
            norm_sum_le _ _
          _ ≤ ∑ j ∈ Finset.Icc 1 M, ‖w (j + 1) - w j‖ * R := by
            apply Finset.sum_le_sum
            intro j hj
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hpartial j hj) (norm_nonneg _)
    _ = W * R + (∑ j ∈ Finset.Icc 1 M, ‖w (j + 1) - w j‖) * R := by
      rw [Finset.sum_mul]
    _ ≤ W * R + D * R := by gcongr
    _ = (W + D) * R := by ring

/-- A large reflected polynomial yields a large coefficient-one prefix.
This is the exact finite deweighting step; no stationary coefficient is
silently substituted for the source weight. -/
theorem norm_typeIReflectedFixedPolynomial_le_two_mul_max_prefix
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u : ℝ) (M : ℕ) (R : ℝ)
    (hR : 0 ≤ R)
    (hpartial : ∀ j ∈ Finset.Icc 1 M,
      ‖∑ m ∈ Finset.Icc 1 j,
        (m : ℂ) ^ (((u : ℂ) * Complex.I))‖ ≤ R) :
    ‖typeIReflectedFixedPolynomial sigma u M‖ ≤
      2 * (M + 1 : ℝ) ^ sigma * R := by
  let w : ℕ → ℂ := fun m => (((m : ℝ) ^ sigma : ℝ) : ℂ)
  let a : ℕ → ℂ := fun m => (m : ℂ) ^ (((u : ℂ) * Complex.I))
  have hdiffPoint : ∀ j : ℕ,
      ‖w (j + 1) - w j‖ = (j + 1 : ℝ) ^ sigma - (j : ℝ) ^ sigma := by
    intro j
    dsimp only [w]
    push_cast
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact sub_nonneg.mpr (Real.rpow_le_rpow (Nat.cast_nonneg j)
      (show (j : ℝ) ≤ (j : ℝ) + 1 by norm_num) hsigma)
  have hdiff : (∑ j ∈ Finset.Icc 1 M, ‖w (j + 1) - w j‖) ≤
      (M + 1 : ℝ) ^ sigma - 1 := by
    simp_rw [hdiffPoint]
    have htel := sum_successive_differences
      (fun n : ℕ => (n : ℝ) ^ sigma) M
    convert htel.le using 1 <;> norm_num
  have hend : ‖w (M + 1)‖ ≤ (M + 1 : ℝ) ^ sigma := by
    dsimp only [w]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    norm_num
  have hbase := norm_weighted_sum_le_of_partial_sum w a M R
    ((M + 1 : ℝ) ^ sigma) ((M + 1 : ℝ) ^ sigma - 1)
    hR hpartial hend hdiff
  unfold typeIReflectedFixedPolynomial
  change ‖∑ m ∈ Finset.Icc 1 M, w m * a m‖ ≤ _
  calc
    ‖∑ m ∈ Finset.Icc 1 M, w m * a m‖ ≤
      ((M + 1 : ℝ) ^ sigma + ((M + 1 : ℝ) ^ sigma - 1)) * R := hbase
    _ ≤ 2 * (M + 1 : ℝ) ^ sigma * R := by
      have hRpow : 0 ≤ (M + 1 : ℝ) ^ sigma := Real.rpow_nonneg (by positivity) _
      nlinarith

theorem exists_large_reflected_prefix
    {sigma : ℝ} (hsigma : 0 ≤ sigma) (u : ℝ) (M : ℕ) (R : ℝ)
    (hR : 0 ≤ R)
    (hLarge : 2 * (M + 1 : ℝ) ^ sigma * R <
      ‖typeIReflectedFixedPolynomial sigma u M‖) :
    ∃ j ∈ Finset.Icc 1 M, R <
      ‖∑ m ∈ Finset.Icc 1 j,
        (m : ℂ) ^ (((u : ℂ) * Complex.I))‖ := by
  by_contra h
  push Not at h
  exact (not_le_of_gt hLarge)
    (norm_typeIReflectedFixedPolynomial_le_two_mul_max_prefix
      hsigma u M R hR h)

/-- The reflected coefficients, normalized at their right endpoint. -/
noncomputable def normalizedTypeIReflectedCoeff
    (sigma : ℝ) (M m : ℕ) : ℂ :=
  if 1 ≤ m ∧ m ≤ M then
    (((m : ℝ) ^ sigma / (M : ℝ) ^ sigma : ℝ) : ℂ)
  else 0

/-- The normalized reflected coefficients have modulus at most one. -/
theorem norm_normalizedTypeIReflectedCoeff_le_one
    {sigma : ℝ} (hsigma : 0 ≤ sigma) {M m : ℕ} (hM : 0 < M) :
    ‖normalizedTypeIReflectedCoeff sigma M m‖ ≤ 1 := by
  unfold normalizedTypeIReflectedCoeff
  split_ifs with h
  · have hmPos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one h.1
    have hmReal : (0 : ℝ) < m := by exact_mod_cast hmPos
    have hMReal : (0 : ℝ) < M := by exact_mod_cast hM
    have hmM : (m : ℝ) ≤ M := by exact_mod_cast h.2
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.rpow_nonneg hmReal.le _)
        (Real.rpow_nonneg hMReal.le _)), div_le_one (Real.rpow_pos_of_pos hMReal _)]
    exact Real.rpow_le_rpow hmReal.le hmM hsigma
  · simp

/-- Removing the harmless `m = 1` term turns the normalized reflected
prefix into one exact wide dyadic polynomial. -/
theorem wideDirichletPoly_normalizedTypeIReflectedCoeff
    {sigma u : ℝ} {M : ℕ} (hM : 1 < M) :
    wideDirichletPoly 1 (Nat.clog 2 M)
        (normalizedTypeIReflectedCoeff sigma M) (-u) =
      typeIReflectedFixedPolynomial sigma u M /
          (((M : ℝ) ^ sigma : ℝ) : ℂ) -
        (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
  have hMPos : 0 < M := lt_trans Nat.zero_lt_one hM
  have hMReal : (0 : ℝ) < M := by exact_mod_cast hMPos
  have hCover : M ≤ 2 ^ Nat.clog 2 M :=
    (Nat.clog_le_iff_le_pow Nat.one_lt_two).mp le_rfl
  unfold wideDirichletPoly typeIReflectedFixedPolynomial
  have hExtend :
      (∑ m ∈ Finset.Ioc 1 (2 ^ Nat.clog 2 M),
          normalizedTypeIReflectedCoeff sigma M m *
            (m : ℂ) ^ (-((-u : ℝ) : ℂ) * I)) =
        ∑ m ∈ Finset.Ioc 1 M,
          ((((m : ℝ) ^ sigma / (M : ℝ) ^ sigma : ℝ) : ℂ)) *
            (m : ℂ) ^ ((u : ℂ) * I) := by
    have hSubset : Finset.Ioc 1 M ⊆
        Finset.Ioc 1 (2 ^ Nat.clog 2 M) := by
      intro m hm
      exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hm).1,
        (Finset.mem_Ioc.mp hm).2.trans hCover⟩
    calc
      (∑ m ∈ Finset.Ioc 1 (2 ^ Nat.clog 2 M),
          normalizedTypeIReflectedCoeff sigma M m *
            (m : ℂ) ^ (-((-u : ℝ) : ℂ) * I)) =
        ∑ m ∈ Finset.Ioc 1 M,
          normalizedTypeIReflectedCoeff sigma M m *
            (m : ℂ) ^ (-((-u : ℝ) : ℂ) * I) := by
          symm
          apply Finset.sum_subset hSubset
          intro m hmBig hmSmall
          have hmOne : 1 < m := (Finset.mem_Ioc.mp hmBig).1
          have hmM : M < m := by
            by_contra hnot
            exact hmSmall (Finset.mem_Ioc.mpr ⟨hmOne, Nat.le_of_not_gt hnot⟩)
          simp [normalizedTypeIReflectedCoeff, hmOne.le, Nat.not_le_of_gt hmM]
      _ = ∑ m ∈ Finset.Ioc 1 M,
          ((((m : ℝ) ^ sigma / (M : ℝ) ^ sigma : ℝ) : ℂ)) *
            (m : ℂ) ^ ((u : ℂ) * I) := by
          apply Finset.sum_congr rfl
          intro m hm
          have hmData := Finset.mem_Ioc.mp hm
          rw [normalizedTypeIReflectedCoeff, if_pos ⟨hmData.1.le, hmData.2⟩]
          congr 2
          push_cast
          ring
  simp only [mul_one]
  rw [hExtend]
  have hMpow : (((M : ℝ) ^ sigma : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos hMReal sigma).ne'
  have hSplit : Finset.Icc 1 M = insert 1 (Finset.Ioc 1 M) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
    omega
  rw [hSplit, Finset.sum_insert]
  · simp only [Nat.cast_one, Real.one_rpow, Complex.ofReal_one,
      Complex.one_cpow, mul_one]
    have hInv :
        (((M : ℝ) ^ sigma : ℝ) : ℂ)⁻¹ =
          (((M : ℝ) ^ (-sigma) : ℝ) : ℂ) := by
      have hInvReal : ((M : ℝ) ^ sigma)⁻¹ = (M : ℝ) ^ (-sigma) := by
        rw [Real.rpow_neg hMReal.le]
      exact_mod_cast hInvReal
    let S : ℂ := ∑ m ∈ Finset.Ioc 1 M,
      ((((m : ℝ) ^ sigma : ℝ) : ℂ) *
        (m : ℂ) ^ ((u : ℂ) * I))
    have hLeft :
        (∑ m ∈ Finset.Ioc 1 M,
            ((((m : ℝ) ^ sigma / (M : ℝ) ^ sigma : ℝ) : ℂ)) *
              (m : ℂ) ^ ((u : ℂ) * I)) =
          S / (((M : ℝ) ^ sigma : ℝ) : ℂ) := by
      dsimp only [S]
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro m _hm
      push_cast
      ring
    rw [hLeft, div_eq_mul_inv]
    simp_rw [← hInv]
    dsimp only [S]
    ring
  · simp

/-- The finitely supported central-mode `tsum` is the literal integer
interval sum. -/
theorem typeINormalizedCentralModes_eq_sum_Icc
    (sigma t : ℝ) (Q M : ℕ) :
    typeINormalizedCentralModes sigma t Q M =
      ∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (Q : ℂ) * typeINormalizedFourier sigma t
          ((Q : ℝ) * (z : ℝ)) := by
  unfold typeINormalizedCentralModes
  rw [tsum_eq_sum (s := Finset.Icc (-(M : ℤ)) (M : ℤ))]
  · apply Finset.sum_congr rfl
    intro z hz
    rw [if_pos]
    have hzData := Finset.mem_Icc.mp hz
    omega
  · intro z hz
    rw [if_neg]
    intro hzAbs
    have hzOut : z < -(M : ℤ) ∨ (M : ℤ) < z := by
      simpa only [Finset.mem_Icc, not_and_or, not_le] using hz
    omega

/-- Exact sign decomposition of the finite central window. -/
theorem typeINormalizedCentralModes_eq_sign_split
    (sigma t : ℝ) (Q M : ℕ) :
    typeINormalizedCentralModes sigma t Q M =
      (Q : ℂ) * typeINormalizedFourier sigma t 0 +
        typeINormalizedNegativeModes sigma t Q M +
          typeINormalizedPositiveModes sigma t Q M := by
  rw [typeINormalizedCentralModes_eq_sum_Icc]
  induction M with
  | zero =>
      simp [typeINormalizedNegativeModes, typeINormalizedPositiveModes]
  | succ M ih =>
      let f : ℤ → ℂ := fun z =>
        (Q : ℂ) * typeINormalizedFourier sigma t
          ((Q : ℝ) * (z : ℝ))
      simp only [typeINormalizedNegativeModes,
        typeINormalizedPositiveModes] at ih
      have hInt : Finset.Icc (-(M.succ : ℤ)) (M.succ : ℤ) =
          insert (-(M.succ : ℤ))
            (insert (M.succ : ℤ) (Finset.Icc (-(M : ℤ)) (M : ℤ))) := by
        ext z
        simp only [Finset.mem_Icc, Finset.mem_insert, Int.natCast_succ]
        omega
      have hNat : Finset.Icc 1 M.succ = insert M.succ (Finset.Icc 1 M) := by
        ext n
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hInt]
      unfold typeINormalizedNegativeModes typeINormalizedPositiveModes
      rw [hNat]
      have hNegNotInner : -(M.succ : ℤ) ∉
          insert (M.succ : ℤ) (Finset.Icc (-(M : ℤ)) (M : ℤ)) := by
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hPosNot : (M.succ : ℤ) ∉
          Finset.Icc (-(M : ℤ)) (M : ℤ) := by
        simp only [Finset.mem_Icc]
        omega
      have hNatNot : M.succ ∉ Finset.Icc 1 M := by
        simp only [Finset.mem_Icc]
        omega
      rw [Finset.sum_insert hNegNotInner, Finset.sum_insert hPosNot,
        Finset.sum_insert hNatNot, Finset.sum_insert hNatNot]
      change f (-(M.succ : ℤ)) + (f (M.succ : ℤ) +
          ∑ z ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), f z) = _
      rw [ih]
      unfold f
      push_cast
      ring

/-- Complete exact source decomposition into the negative reflected block,
the zero and positive nonstationary modes, and the uniform far tail. -/
theorem typeISourceSmoothBlock_eq_mode_decomposition_of_interior
    {Y A r M : ℕ} {sigma t : ℝ}
    (hY : 0 < Y)
    (hLower : ((Y + 1 : ℕ) : ℝ) ≤ (((2 ^ r * Y : ℕ) : ℝ) / 2))
    (hUpper : (2 * (2 ^ r * Y : ℕ) : ℕ) ≤ A) :
    typeISourceSmoothBlock Y A r sigma t =
      typeISourceNormalizationScalar sigma t (2 ^ r * Y : ℕ) *
        (((2 ^ r * Y : ℕ) : ℂ) * typeINormalizedFourier sigma t 0 +
          typeINormalizedNegativeModes sigma t (2 ^ r * Y) M +
          typeINormalizedPositiveModes sigma t (2 ^ r * Y) M +
          typeINormalizedFarTail sigma t (2 ^ r * Y) M) := by
  have hQ : 0 < 2 ^ r * Y := by positivity
  rw [typeISourceSmoothBlock_eq_scaled_normalized_tsum_of_interior
    hY hLower hUpper]
  rw [(typeINormalizedPoisson_split sigma t (2 ^ r * Y) M hQ)]
  rw [typeINormalizedCentralModes_eq_sign_split]

/-! ## Quantitative nonstationary control -/

/-- Abel integration against any uniformly bounded primitive of the bare
logarithmic reflection kernel.  This separates the analytic integration by
parts from the later sign-specific first-derivative estimate. -/
theorem norm_weighted_gmReflectionIntegral_le_of_prefix
    {tau A B R : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hprefix : ∀ x ∈ Set.Icc A B,
      ‖gmReflectionIntegral tau A x‖ ≤ R)
    (w w' : ℝ → ℂ)
    (hw : ∀ x ∈ Set.Icc A B, HasDerivAt w (w' x) x)
    (hw' : IntervalIntegrable w' MeasureTheory.volume A B) :
    ‖∫ v in A..B, w v *
        ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I)))‖ ≤
      R * (‖w B‖ + ∫ v in A..B, ‖w' v‖) := by
  let k : ℝ → ℂ := fun v =>
    (v : ℂ)⁻¹ * Complex.exp
      ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I))
  let F : ℝ → ℂ := fun x => ∫ v in A..x, k v
  have hkInt : IntervalIntegrable k MeasureTheory.volume A B := by
    simpa only [k] using
      intervalIntegrable_gmReflectionIntegrand (tau := tau) hAB hA
  have hkContinuousPos : ContinuousOn k (Set.Ioi 0) := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hxPos : 0 < x := hx
    have hPhase : ContinuousAt
        (fun y : ℝ => tau * Real.log y - 2 * Real.pi * y) x :=
      (continuousAt_const.mul (Real.continuousAt_log hxPos.ne')).sub
        (continuousAt_const.mul continuousAt_id)
    exact (Complex.continuous_ofReal.continuousAt.comp continuousAt_id).inv₀
        (Complex.ofReal_ne_zero.mpr hxPos.ne') |>.mul
      ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul
        continuousAt_const).cexp
  have hkContinuousAt : ∀ x ∈ Set.Icc A B, ContinuousAt k x := by
    intro x hx
    have hxPos : 0 < x := hA.trans_le hx.1
    exact (hkContinuousPos x hxPos).continuousAt (Ioi_mem_nhds hxPos)
  have hkContinuous : ContinuousOn k (Set.Icc A B) :=
    fun x hx => (hkContinuousAt x hx).continuousWithinAt
  have hFDeriv : ∀ x ∈ Set.Icc A B, HasDerivAt F (k x) x := by
    intro x hx
    have hkAx : IntervalIntegrable k MeasureTheory.volume A x := by
      simpa only [k] using
        intervalIntegrable_gmReflectionIntegrand (tau := tau) hx.1 hA
    exact intervalIntegral.integral_hasDerivAt_right hkAx
      (hkContinuousPos.stronglyMeasurableAtFilter isOpen_Ioi x
        (hA.trans_le hx.1))
      (hkContinuousAt x hx)
  have hFContinuous : ContinuousOn F (Set.Icc A B) :=
    fun x hx => (hFDeriv x hx).continuousAt.continuousWithinAt
  have hFContinuousU : ContinuousOn F (Set.uIcc A B) := by
    simpa only [Set.uIcc_of_le hAB] using hFContinuous
  have hwU : ∀ x ∈ Set.uIcc A B, HasDerivAt w (w' x) x := by
    simpa only [Set.uIcc_of_le hAB] using hw
  have hFDerivU : ∀ x ∈ Set.uIcc A B, HasDerivAt F (k x) x := by
    simpa only [Set.uIcc_of_le hAB] using hFDeriv
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hwU hFDerivU hw' hkInt
  have hFA : F A = 0 := by simp [F]
  have hFB : F B = gmReflectionIntegral tau A B := by rfl
  have hFBound : ∀ x ∈ Set.Icc A B, ‖F x‖ ≤ R := by
    intro x hx
    simpa only [F, k, gmReflectionIntegral] using hprefix x hx
  have hvariationNonneg : 0 ≤ ∫ v in A..B, ‖w' v‖ :=
    intervalIntegral.integral_nonneg hAB fun _ _ => norm_nonneg _
  have hweightedVariation :
      ‖∫ v in A..B, w' v * F v‖ ≤ R * ∫ v in A..B, ‖w' v‖ := by
    calc
      ‖∫ v in A..B, w' v * F v‖ ≤
          |∫ v in A..B, ‖w' v * F v‖| :=
        intervalIntegral.norm_integral_le_abs_integral_norm
      _ = ∫ v in A..B, ‖w' v * F v‖ := by
        rw [abs_of_nonneg]
        exact intervalIntegral.integral_nonneg hAB fun _ _ => norm_nonneg _
      _ ≤ ∫ v in A..B, ‖w' v‖ * R := by
        apply intervalIntegral.integral_mono_on hAB
        · simpa only [norm_mul] using
            (hw'.norm.mul_continuousOn hFContinuousU.norm)
        · exact hw'.norm.mul_const R
        · intro v hv
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left (hFBound v hv) (norm_nonneg _)
      _ = R * ∫ v in A..B, ‖w' v‖ := by
        rw [intervalIntegral.integral_mul_const]
        ring
  rw [hparts, hFA, hFB]
  simp only [mul_zero, sub_zero]
  calc
    ‖w B * gmReflectionIntegral tau A B - ∫ v in A..B, w' v * F v‖ ≤
        ‖w B * gmReflectionIntegral tau A B‖ +
          ‖∫ v in A..B, w' v * F v‖ := norm_sub_le _ _
    _ ≤ ‖w B‖ * R + R * ∫ v in A..B, ‖w' v‖ := by
      gcongr
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hprefix B ⟨hAB, le_rfl⟩)
        (norm_nonneg _)
    _ = R * (‖w B‖ + ∫ v in A..B, ‖w' v‖) := by ring

/-- The first-derivative estimate remains valid after insertion of any
bounded-variation amplitude. -/
theorem norm_weighted_gmReflectionIntegral_le_right
    {tau A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hright : tau < 2 * Real.pi * A)
    (w w' : ℝ → ℂ)
    (hw : ∀ x ∈ Set.Icc A B, HasDerivAt w (w' x) x)
    (hw' : IntervalIntegrable w' MeasureTheory.volume A B) :
    ‖∫ v in A..B, w v *
        ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I)))‖ ≤
      (2 / (2 * Real.pi * A - tau)) *
        (‖w B‖ + ∫ v in A..B, ‖w' v‖) := by
  apply norm_weighted_gmReflectionIntegral_le_of_prefix
    (R := 2 / (2 * Real.pi * A - tau)) hA hAB
  · intro x hx
    exact norm_gmReflectionIntegral_le_right hx.1 hA hright
  · exact hw
  · exact hw'

/-- Total variation of the positive power weight on a positive interval. -/
theorem integral_norm_gmReflectionPowerWeight_deriv_le
    {sigma A B : ℝ} (hsigma : 0 < sigma) (hA : 0 < A) (hAB : A ≤ B) :
    (∫ v in A..B,
        ‖(((-sigma / v : ℝ) : ℂ) * gmReflectionPowerWeight sigma v)‖) ≤
      A ^ (-sigma) := by
  have hzero : (0 : ℝ) ∉ Set.uIcc A B := by
    rw [Set.uIcc_of_le hAB]
    intro h
    linarith [h.1]
  have hpoint : ∀ v ∈ Set.uIcc A B,
      ‖(((-sigma / v : ℝ) : ℂ) * gmReflectionPowerWeight sigma v)‖ =
        sigma * v ^ (-sigma - 1) := by
    intro v hv
    have hvPos : 0 < v := by
      rw [Set.uIcc_of_le hAB] at hv
      exact hA.trans_le hv.1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_neg (div_neg_of_neg_of_pos (neg_lt_zero.mpr hsigma) hvPos),
      norm_gmReflectionPowerWeight hvPos]
    have hpow : v⁻¹ * v ^ (-sigma) = v ^ (-sigma - 1) := by
      rw [← Real.rpow_neg_one, ← Real.rpow_add hvPos]
      congr 1
      ring
    rw [show -(-sigma / v) = sigma * v⁻¹ by field_simp]
    calc
      sigma * v⁻¹ * v ^ (-sigma) = sigma * (v⁻¹ * v ^ (-sigma)) := by ring
      _ = sigma * v ^ (-sigma - 1) := by rw [hpow]
  rw [intervalIntegral.integral_congr hpoint]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_rpow (Or.inr ⟨by linarith, hzero⟩)]
  have hBpow : 0 ≤ B ^ (-sigma) := Real.rpow_nonneg (by linarith) _
  have hsigmaNe : sigma ≠ 0 := hsigma.ne'
  calc
    sigma * ((B ^ (-sigma - 1 + 1) - A ^ (-sigma - 1 + 1)) /
        (-sigma - 1 + 1)) = A ^ (-sigma) - B ^ (-sigma) := by
          field_simp [hsigmaNe]
          ring
    _ ≤ A ^ (-sigma) := by linarith

/-- Nonstationary weighted reflection with its power variation absorbed. -/
theorem norm_powerWeighted_gmReflectionIntegral_le_right
    {tau sigma A B : ℝ} (hsigma : 0 < sigma)
    (hA : 0 < A) (hAB : A ≤ B)
    (hright : tau < 2 * Real.pi * A) :
    ‖typeIPowerReflectionIntegral sigma tau A B‖ ≤
      (4 / (2 * Real.pi * A - tau)) * A ^ (-sigma) := by
  let w' : ℝ → ℂ := fun v =>
    (((-sigma / v : ℝ) : ℂ) * gmReflectionPowerWeight sigma v)
  have hw : ∀ x ∈ Set.Icc A B,
      HasDerivAt (gmReflectionPowerWeight sigma) (w' x) x := by
    intro x hx
    exact hasDerivAt_gmReflectionPowerWeight (hA.trans_le hx.1)
  have hw' : IntervalIntegrable w' MeasureTheory.volume A B := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hxIcc : x ∈ Set.Icc A B := by
      simpa only [Set.uIcc_of_le hAB] using hx
    have hxPos : 0 < x := hA.trans_le hxIcc.1
    exact (Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div continuousAt_id hxPos.ne')).mul
      (hasDerivAt_gmReflectionPowerWeight hxPos).continuousAt
  have hBase := norm_weighted_gmReflectionIntegral_le_right
    hA hAB hright (gmReflectionPowerWeight sigma) w' hw hw'
  have hEnd : ‖gmReflectionPowerWeight sigma B‖ ≤ A ^ (-sigma) := by
    rw [norm_gmReflectionPowerWeight (hA.trans_le hAB)]
    exact Real.rpow_le_rpow_of_nonpos hA hAB (by linarith)
  have hVar := integral_norm_gmReflectionPowerWeight_deriv_le
    hsigma hA hAB
  have hUnstar :
      ‖∫ v in A..B, gmReflectionPowerWeight sigma v *
          ((v : ℂ)⁻¹ * Complex.exp
            ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I)))‖ ≤
        (4 / (2 * Real.pi * A - tau)) * A ^ (-sigma) := hBase.trans (by
    have hden : 0 < 2 * Real.pi * A - tau := by linarith
    calc
      (2 / (2 * Real.pi * A - tau)) *
          (‖gmReflectionPowerWeight sigma B‖ + ∫ v in A..B, ‖w' v‖) ≤
        (2 / (2 * Real.pi * A - tau)) *
          (A ^ (-sigma) + A ^ (-sigma)) := by gcongr
      _ = (4 / (2 * Real.pi * A - tau)) * A ^ (-sigma) := by ring)
  let f : ℝ → ℂ := fun v =>
    gmReflectionPowerWeight sigma v *
      ((v : ℂ)⁻¹ * Complex.exp
        ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I)))
  have hfInt : IntervalIntegrable f MeasureTheory.volume A B := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro v hv
    have hvIcc : v ∈ Set.Icc A B := by
      simpa only [Set.uIcc_of_le hAB] using hv
    have hvPos : 0 < v := hA.trans_le hvIcc.1
    have hPhase : ContinuousAt
        (fun x : ℝ => tau * Real.log x - 2 * Real.pi * x) v :=
      (continuousAt_const.mul (Real.continuousAt_log hvPos.ne')).sub
        (continuousAt_const.mul continuousAt_id)
    exact (hasDerivAt_gmReflectionPowerWeight hvPos).continuousAt.mul
      ((Complex.continuous_ofReal.continuousAt.comp continuousAt_id).inv₀
          (Complex.ofReal_ne_zero.mpr hvPos.ne') |>.mul
        ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul
          continuousAt_const).cexp)
  have hConj := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hfInt
  have hPointwise : (fun v : ℝ => star (f v)) = fun v =>
      gmReflectionPowerWeight sigma v *
        star ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I))) := by
    funext v
    dsimp only [f]
    rw [Complex.star_def, map_mul]
    have hs := star_gmReflectionPowerWeight sigma v
    rw [Complex.star_def] at hs
    rw [hs]
  have hConj' : (∫ v in A..B, star (f v)) =
      star (∫ v in A..B, f v) := by
    simpa only [Complex.conjCLE_apply, Complex.star_def] using hConj
  unfold typeIPowerReflectionIntegral
  rw [← hPointwise, hConj']
  rw [Complex.star_def, Complex.norm_conj]
  exact hUnstar

/-- The companion bounded-variation estimate on an interval strictly to
the left of the stationary point.  This is needed when the physical
reflection interval starts below the stationary window; keeping this piece
separate avoids replacing its true endpoint gain by the weaker global
second-derivative bound. -/
theorem norm_weighted_gmReflectionIntegral_le_left
    {tau A B : ℝ} (hA : 0 < A) (hAB : A ≤ B)
    (hleft : 2 * Real.pi * B < tau)
    (w w' : ℝ → ℂ)
    (hw : ∀ x ∈ Set.Icc A B, HasDerivAt w (w' x) x)
    (hw' : IntervalIntegrable w' MeasureTheory.volume A B) :
    ‖∫ v in A..B, w v *
        ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I)))‖ ≤
      (2 / (tau - 2 * Real.pi * B)) *
        (‖w B‖ + ∫ v in A..B, ‖w' v‖) := by
  apply norm_weighted_gmReflectionIntegral_le_of_prefix
    (R := 2 / (tau - 2 * Real.pi * B)) hA hAB
  · intro x hx
    have hxb := mul_le_mul_of_nonneg_left hx.2
      (by positivity : 0 ≤ 2 * Real.pi)
    have hdenX : 0 < tau - 2 * Real.pi * x := by linarith
    have hdenB : 0 < tau - 2 * Real.pi * B := by linarith
    calc
      ‖gmReflectionIntegral tau A x‖ ≤
          2 / (tau - 2 * Real.pi * x) :=
        norm_gmReflectionIntegral_le_left (tau := tau) (a := A) (b := x)
          hx.1 hA (by linarith)
      _ ≤ 2 / (tau - 2 * Real.pi * B) := by
        exact div_le_div_of_nonneg_left (by norm_num) hdenB
          (by linarith)
  · exact hw
  · exact hw'

/-- Nonstationary power-weighted reflection on the left of the stationary
point. -/
theorem norm_powerWeighted_gmReflectionIntegral_le_left
    {tau sigma A B : ℝ} (hsigma : 0 < sigma)
    (hA : 0 < A) (hAB : A ≤ B)
    (hleft : 2 * Real.pi * B < tau) :
    ‖typeIPowerReflectionIntegral sigma tau A B‖ ≤
      (4 / (tau - 2 * Real.pi * B)) * A ^ (-sigma) := by
  let w' : ℝ → ℂ := fun v =>
    (((-sigma / v : ℝ) : ℂ) * gmReflectionPowerWeight sigma v)
  have hw : ∀ x ∈ Set.Icc A B,
      HasDerivAt (gmReflectionPowerWeight sigma) (w' x) x := by
    intro x hx
    exact hasDerivAt_gmReflectionPowerWeight (hA.trans_le hx.1)
  have hw' : IntervalIntegrable w' MeasureTheory.volume A B := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hxIcc : x ∈ Set.Icc A B := by
      simpa only [Set.uIcc_of_le hAB] using hx
    have hxPos : 0 < x := hA.trans_le hxIcc.1
    exact (Complex.continuous_ofReal.continuousAt.comp
        (continuousAt_const.div continuousAt_id hxPos.ne')).mul
      (hasDerivAt_gmReflectionPowerWeight hxPos).continuousAt
  have hBase := norm_weighted_gmReflectionIntegral_le_left
    hA hAB hleft (gmReflectionPowerWeight sigma) w' hw hw'
  have hEnd : ‖gmReflectionPowerWeight sigma B‖ ≤ A ^ (-sigma) := by
    rw [norm_gmReflectionPowerWeight (hA.trans_le hAB)]
    exact Real.rpow_le_rpow_of_nonpos hA hAB (by linarith)
  have hVar := integral_norm_gmReflectionPowerWeight_deriv_le
    hsigma hA hAB
  have hUnstar :
      ‖∫ v in A..B, gmReflectionPowerWeight sigma v *
          ((v : ℂ)⁻¹ * Complex.exp
            ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I)))‖ ≤
        (4 / (tau - 2 * Real.pi * B)) * A ^ (-sigma) := hBase.trans (by
    have hden : 0 < tau - 2 * Real.pi * B := by linarith
    calc
      (2 / (tau - 2 * Real.pi * B)) *
          (‖gmReflectionPowerWeight sigma B‖ + ∫ v in A..B, ‖w' v‖) ≤
        (2 / (tau - 2 * Real.pi * B)) *
          (A ^ (-sigma) + A ^ (-sigma)) := by gcongr
      _ = (4 / (tau - 2 * Real.pi * B)) * A ^ (-sigma) := by ring)
  let f : ℝ → ℂ := fun v =>
    gmReflectionPowerWeight sigma v *
      ((v : ℂ)⁻¹ * Complex.exp
        ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I)))
  have hfInt : IntervalIntegrable f MeasureTheory.volume A B := by
    apply ContinuousOn.intervalIntegrable
    apply continuousOn_of_forall_continuousAt
    intro v hv
    have hvIcc : v ∈ Set.Icc A B := by
      simpa only [Set.uIcc_of_le hAB] using hv
    have hvPos : 0 < v := hA.trans_le hvIcc.1
    have hPhase : ContinuousAt
        (fun x : ℝ => tau * Real.log x - 2 * Real.pi * x) v :=
      (continuousAt_const.mul (Real.continuousAt_log hvPos.ne')).sub
        (continuousAt_const.mul continuousAt_id)
    exact (hasDerivAt_gmReflectionPowerWeight hvPos).continuousAt.mul
      ((Complex.continuous_ofReal.continuousAt.comp continuousAt_id).inv₀
          (Complex.ofReal_ne_zero.mpr hvPos.ne') |>.mul
        ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul
          continuousAt_const).cexp)
  have hConj := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm hfInt
  have hPointwise : (fun v : ℝ => star (f v)) = fun v =>
      gmReflectionPowerWeight sigma v *
        star ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I))) := by
    funext v
    dsimp only [f]
    rw [Complex.star_def, map_mul]
    have hs := star_gmReflectionPowerWeight sigma v
    rw [Complex.star_def] at hs
    rw [hs]
  have hConj' : (∫ v in A..B, star (f v)) =
      star (∫ v in A..B, f v) := by
    simpa only [Complex.conjCLE_apply, Complex.star_def] using hConj
  unfold typeIPowerReflectionIntegral
  rw [← hPointwise, hConj']
  rw [Complex.star_def, Complex.norm_conj]
  exact hUnstar

private theorem intervalIntegrable_typeIPowerReflectionIntegrand
    {sigma tau A B : ℝ} (hA : 0 < A) (hAB : A ≤ B) :
    IntervalIntegrable
      (fun v : ℝ => gmReflectionPowerWeight sigma v *
        star ((v : ℂ)⁻¹ * Complex.exp
          ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I))))
      MeasureTheory.volume A B := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro v hv
  have hvIcc : v ∈ Set.Icc A B := by
    simpa only [Set.uIcc_of_le hAB] using hv
  have hvPos : 0 < v := hA.trans_le hvIcc.1
  have hPhase : ContinuousAt
      (fun x : ℝ => tau * Real.log x - 2 * Real.pi * x) v :=
    (continuousAt_const.mul (Real.continuousAt_log hvPos.ne')).sub
      (continuousAt_const.mul continuousAt_id)
  exact (hasDerivAt_gmReflectionPowerWeight hvPos).continuousAt.mul
    (((Complex.continuous_ofReal.continuousAt.comp continuousAt_id).inv₀
        (Complex.ofReal_ne_zero.mpr hvPos.ne') |>.mul
      ((Complex.continuous_ofReal.continuousAt.comp hPhase).mul
        continuousAt_const).cexp).star)

/-- Stationary-window refinement of the weighted B-process.  The first
term is the genuinely nonstationary piece below `tau/(4*pi)`; the second is
the stationary contribution with the full `tau^(-sigma-1/2)` gain.  No
asymptotic expansion is postulated: the proof splits the exact interval and
combines the proved first- and second-derivative estimates. -/
theorem norm_typeIPowerReflectionIntegral_le_stationary
    {sigma tau A B : ℝ} (hsigma : 0 < sigma)
    (htau : 1 ≤ tau) (hA : 0 < A) (hAB : A ≤ B) :
    ‖typeIPowerReflectionIntegral sigma tau A B‖ ≤
      (8 / tau) * A ^ (-sigma) +
        (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
          tau ^ (-sigma - 1 / 2) := by
  let L : ℝ := tau / (4 * Real.pi)
  let R : ℝ := tau / Real.pi
  have htauPos : 0 < tau := zero_lt_one.trans_le htau
  have hLPos : 0 < L := by dsimp only [L]; positivity
  have hRPos : 0 < R := by dsimp only [R]; positivity
  have hLR : L < R := by
    dsimp only [L, R]
    rw [div_lt_div_iff₀ (by positivity : 0 < 4 * Real.pi) Real.pi_pos]
    nlinarith [Real.pi_pos]
  have hMainNonneg : 0 ≤
      (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
        tau ^ (-sigma - 1 / 2) := by positivity
  by_cases hEntireLeft : B ≤ L
  · have hleft : 2 * Real.pi * B < tau := by
      have hscaled := mul_le_mul_of_nonneg_left hEntireLeft
        (by positivity : 0 ≤ 2 * Real.pi)
      have hLcalc : 2 * Real.pi * L = tau / 2 := by
        dsimp only [L]
        field_simp [Real.pi_ne_zero]
        norm_num
      rw [hLcalc] at hscaled
      linarith
    have hBound := norm_powerWeighted_gmReflectionIntegral_le_left
      hsigma hA hAB hleft
    have hden : tau / 2 ≤ tau - 2 * Real.pi * B := by
      have hscaled := mul_le_mul_of_nonneg_left hEntireLeft
        (by positivity : 0 ≤ 2 * Real.pi)
      have hLcalc : 2 * Real.pi * L = tau / 2 := by
        dsimp only [L]
        field_simp [Real.pi_ne_zero]
        norm_num
      rw [hLcalc] at hscaled
      linarith
    have hdenPos : 0 < tau - 2 * Real.pi * B := by linarith
    calc
      ‖typeIPowerReflectionIntegral sigma tau A B‖ ≤
          (4 / (tau - 2 * Real.pi * B)) * A ^ (-sigma) := hBound
      _ ≤ (8 / tau) * A ^ (-sigma) := by
        have hfrac : 4 / (tau - 2 * Real.pi * B) ≤ 8 / tau := by
          apply (div_le_div_iff₀ hdenPos htauPos).2
          nlinarith
        exact mul_le_mul_of_nonneg_right hfrac (Real.rpow_nonneg hA.le _)
      _ ≤ (8 / tau) * A ^ (-sigma) +
          (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
            tau ^ (-sigma - 1 / 2) := le_add_of_nonneg_right hMainNonneg
  by_cases hEntireRight : R ≤ A
  · have hright : tau < 2 * Real.pi * A := by
      have hscaled := mul_le_mul_of_nonneg_left hEntireRight
        (by positivity : 0 ≤ 2 * Real.pi)
      have hRcalc : 2 * Real.pi * R = 2 * tau := by
        dsimp only [R]
        field_simp [Real.pi_ne_zero]
      rw [hRcalc] at hscaled
      linarith
    have hBound := norm_powerWeighted_gmReflectionIntegral_le_right
      hsigma hA hAB hright
    have hden : tau ≤ 2 * Real.pi * A - tau := by
      have hscaled := mul_le_mul_of_nonneg_left hEntireRight
        (by positivity : 0 ≤ 2 * Real.pi)
      have hRcalc : 2 * Real.pi * R = 2 * tau := by
        dsimp only [R]
        field_simp [Real.pi_ne_zero]
      rw [hRcalc] at hscaled
      linarith
    have hdenPos : 0 < 2 * Real.pi * A - tau := by linarith
    calc
      ‖typeIPowerReflectionIntegral sigma tau A B‖ ≤
          (4 / (2 * Real.pi * A - tau)) * A ^ (-sigma) := hBound
      _ ≤ (8 / tau) * A ^ (-sigma) := by
        have hfrac : 4 / (2 * Real.pi * A - tau) ≤ 8 / tau := by
          apply (div_le_div_iff₀ hdenPos htauPos).2
          nlinarith
        exact mul_le_mul_of_nonneg_right hfrac (Real.rpow_nonneg hA.le _)
      _ ≤ (8 / tau) * A ^ (-sigma) +
          (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
            tau ^ (-sigma - 1 / 2) := le_add_of_nonneg_right hMainNonneg
  · have hLB : L < B := lt_of_not_ge hEntireLeft
    have hAR : A < R := lt_of_not_ge hEntireRight
    let l : ℝ := max A L
    let r : ℝ := min B R
    have hAl : A ≤ l := le_max_left _ _
    have hlB : l ≤ B := max_le hAB hLB.le
    have hAr : A ≤ r := le_min hAB hAR.le
    have hrB : r ≤ B := min_le_left _ _
    have hlr : l ≤ r := by
      apply max_le
      · exact hAr
      · exact le_min hLB.le hLR.le
    have hlPos : 0 < l := hA.trans_le hAl
    have hrPos : 0 < r := hlPos.trans_le hlr
    have hLeftPiece : ‖typeIPowerReflectionIntegral sigma tau A l‖ ≤
        (8 / tau) * A ^ (-sigma) := by
      by_cases hEq : l = A
      · rw [hEq]
        simp [typeIPowerReflectionIntegral]
        positivity
      · have hAL : A < L := by
          have hnot : ¬ L ≤ A := by
            intro hLA
            apply hEq
            exact max_eq_left hLA
          exact lt_of_not_ge hnot
        have hlEq : l = L := max_eq_right hAL.le
        rw [hlEq]
        have hleft : 2 * Real.pi * L < tau := by
          have hLcalc : 2 * Real.pi * L = tau / 2 := by
            dsimp only [L]
            field_simp [Real.pi_ne_zero]
            norm_num
          rw [hLcalc]
          linarith
        have hBound := norm_powerWeighted_gmReflectionIntegral_le_left
          hsigma hA hAL.le hleft
        have hden : tau - 2 * Real.pi * L = tau / 2 := by
          dsimp only [L]
          field_simp [Real.pi_ne_zero]
          norm_num
        rw [hden] at hBound
        calc
          ‖typeIPowerReflectionIntegral sigma tau A L‖ ≤
              (4 / (tau / 2)) * A ^ (-sigma) := hBound
          _ = (8 / tau) * A ^ (-sigma) := by field_simp; ring
    have hMiddlePiece : ‖typeIPowerReflectionIntegral sigma tau l r‖ ≤
        20 * (4 * Real.pi) ^ sigma * tau ^ (-sigma - 1 / 2) := by
      have hBound := norm_typeIPowerReflectionIntegral_le
        (sigma := sigma) htau hlPos hlr
      have hEnd : r ^ (-sigma) ≤ L ^ (-sigma) := by
        exact Real.rpow_le_rpow_of_nonpos hLPos
          ((le_max_right A L).trans hlr) (by linarith)
      have hVar := integral_norm_gmReflectionPowerWeight_deriv_le
        hsigma hlPos hlr
      have hVarL :
          (∫ v in l..r,
              ‖(((-sigma / v : ℝ) : ℂ) *
                gmReflectionPowerWeight sigma v)‖) ≤ L ^ (-sigma) :=
        hVar.trans (Real.rpow_le_rpow_of_nonpos hLPos
          (le_max_right A L) (by linarith))
      have hLpow : L ^ (-sigma) =
          (4 * Real.pi) ^ sigma * tau ^ (-sigma) := by
        dsimp only [L]
        rw [Real.div_rpow (by positivity) (by positivity)]
        rw [Real.rpow_neg (by positivity : 0 ≤ tau),
          Real.rpow_neg (by positivity : 0 ≤ 4 * Real.pi)]
        field_simp [Real.rpow_pos_of_pos htauPos,
          Real.rpow_pos_of_pos (by positivity : 0 < 4 * Real.pi)]
      have hInvSqrt : (Real.sqrt tau)⁻¹ = tau ^ (-1 / 2 : ℝ) := by
        rw [Real.sqrt_eq_rpow]
        convert (Real.rpow_neg htauPos.le (1 / 2 : ℝ)).symm using 1
        ring
      calc
        ‖typeIPowerReflectionIntegral sigma tau l r‖ ≤
            (10 / Real.sqrt tau) *
              (r ^ (-sigma) +
                ∫ v in l..r,
                  ‖(((-sigma / v : ℝ) : ℂ) *
                    gmReflectionPowerWeight sigma v)‖) := hBound
        _ ≤ (10 / Real.sqrt tau) *
              (L ^ (-sigma) + L ^ (-sigma)) := by
          gcongr
        _ = 20 * (4 * Real.pi) ^ sigma *
              tau ^ (-sigma - 1 / 2) := by
          rw [div_eq_mul_inv, hInvSqrt, hLpow]
          calc
            10 * tau ^ (-1 / 2 : ℝ) *
                ((4 * Real.pi) ^ sigma * tau ^ (-sigma) +
                  (4 * Real.pi) ^ sigma * tau ^ (-sigma)) =
                20 * (4 * Real.pi) ^ sigma *
                  (tau ^ (-1 / 2 : ℝ) * tau ^ (-sigma)) := by ring
            _ = 20 * (4 * Real.pi) ^ sigma *
                  tau ^ (-sigma - 1 / 2) := by
              rw [← Real.rpow_add htauPos]
              congr 2
              ring
    have hRightPiece : ‖typeIPowerReflectionIntegral sigma tau r B‖ ≤
        4 * Real.pi ^ sigma * tau ^ (-sigma - 1 / 2) := by
      by_cases hEq : r = B
      · rw [hEq]
        simp [typeIPowerReflectionIntegral]
        positivity
      · have hRB : R < B := by
          have hnot : ¬ B ≤ R := by
            intro hBR
            apply hEq
            exact min_eq_left hBR
          exact lt_of_not_ge hnot
        have hrEq : r = R := min_eq_right hRB.le
        rw [hrEq]
        have hright : tau < 2 * Real.pi * R := by
          have hRcalc : 2 * Real.pi * R = 2 * tau := by
            dsimp only [R]
            field_simp [Real.pi_ne_zero]
          rw [hRcalc]
          linarith
        have hBound := norm_powerWeighted_gmReflectionIntegral_le_right
          hsigma hRPos hRB.le hright
        have hden : 2 * Real.pi * R - tau = tau := by
          dsimp only [R]
          field_simp [Real.pi_ne_zero]
          norm_num
        have hRpow : R ^ (-sigma) =
            Real.pi ^ sigma * tau ^ (-sigma) := by
          dsimp only [R]
          rw [Real.div_rpow (by positivity) Real.pi_pos.le]
          rw [Real.rpow_neg htauPos.le, Real.rpow_neg Real.pi_pos.le]
          field_simp [Real.rpow_pos_of_pos htauPos,
            Real.rpow_pos_of_pos Real.pi_pos]
        have hTauPow : tau ^ (-sigma - 1) ≤
            tau ^ (-sigma - 1 / 2) :=
          Real.rpow_le_rpow_of_exponent_le htau (by linarith)
        rw [hden, hRpow] at hBound
        calc
          ‖typeIPowerReflectionIntegral sigma tau R B‖ ≤
              (4 / tau) * (Real.pi ^ sigma * tau ^ (-sigma)) := hBound
          _ = 4 * Real.pi ^ sigma * tau ^ (-sigma - 1) := by
            rw [div_eq_mul_inv, ← Real.rpow_neg_one]
            calc
              4 * tau ^ (-1 : ℝ) *
                    (Real.pi ^ sigma * tau ^ (-sigma)) =
                  4 * Real.pi ^ sigma *
                    (tau ^ (-1 : ℝ) * tau ^ (-sigma)) := by ring
              _ = 4 * Real.pi ^ sigma * tau ^ (-sigma - 1) := by
                rw [← Real.rpow_add htauPos]
                congr 2
                ring
          _ ≤ 4 * Real.pi ^ sigma * tau ^ (-sigma - 1 / 2) := by
            gcongr
    let f : ℝ → ℂ := fun v => gmReflectionPowerWeight sigma v *
      star ((v : ℂ)⁻¹ * Complex.exp
        ((((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * Complex.I)))
    have hIntAl : IntervalIntegrable f MeasureTheory.volume A l :=
      intervalIntegrable_typeIPowerReflectionIntegrand hA hAl
    have hIntlR : IntervalIntegrable f MeasureTheory.volume l r :=
      intervalIntegrable_typeIPowerReflectionIntegrand hlPos hlr
    have hIntrB : IntervalIntegrable f MeasureTheory.volume r B :=
      intervalIntegrable_typeIPowerReflectionIntegrand hrPos hrB
    have hSplit : typeIPowerReflectionIntegral sigma tau A B =
        typeIPowerReflectionIntegral sigma tau A l +
          typeIPowerReflectionIntegral sigma tau l r +
            typeIPowerReflectionIntegral sigma tau r B := by
      unfold typeIPowerReflectionIntegral
      rw [← intervalIntegral.integral_add_adjacent_intervals hIntAl
        (hIntlR.trans hIntrB)]
      rw [← intervalIntegral.integral_add_adjacent_intervals hIntlR hIntrB]
      ring
    rw [hSplit]
    calc
      ‖typeIPowerReflectionIntegral sigma tau A l +
          typeIPowerReflectionIntegral sigma tau l r +
            typeIPowerReflectionIntegral sigma tau r B‖ ≤
        ‖typeIPowerReflectionIntegral sigma tau A l‖ +
          ‖typeIPowerReflectionIntegral sigma tau l r‖ +
            ‖typeIPowerReflectionIntegral sigma tau r B‖ := by
          exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ (8 / tau) * A ^ (-sigma) +
          20 * (4 * Real.pi) ^ sigma * tau ^ (-sigma - 1 / 2) +
            4 * Real.pi ^ sigma * tau ^ (-sigma - 1 / 2) := by gcongr
      _ = (8 / tau) * A ^ (-sigma) +
          (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
            tau ^ (-sigma - 1 / 2) := by ring

/-- A phase-blind bound for the reflection integral.  This is deliberately
coarse, but uniform in the vertical parameter; it is used only beyond the
truncated Mellin window, where arbitrary Schwartz decay absorbs every
polynomial factor displayed here. -/
theorem norm_typeIPowerReflectionIntegral_le_trivial
    {sigma tau A B : ℝ} (hsigma : 0 ≤ sigma)
    (hA : 0 < A) (hAB : A ≤ B) :
    ‖typeIPowerReflectionIntegral sigma tau A B‖ ≤
      (B - A) * (A ^ (-sigma) / A) := by
  let f : ℝ → ℂ := fun v => gmReflectionPowerWeight sigma v *
    star ((v : ℂ)⁻¹ * Complex.exp
      (((tau * Real.log v - 2 * Real.pi * v : ℝ) : ℂ) * I))
  have hPoint : ∀ v ∈ Set.uIcc A B, ‖f v‖ ≤ A ^ (-sigma) / A := by
    intro v hv
    have hvIcc : v ∈ Set.Icc A B := by
      simpa only [Set.uIcc_of_le hAB] using hv
    have hvPos : 0 < v := hA.trans_le hvIcc.1
    have hpow : v ^ (-sigma) ≤ A ^ (-sigma) :=
      Real.rpow_le_rpow_of_nonpos hA hvIcc.1 (by linarith)
    have hinv : v⁻¹ ≤ A⁻¹ := (inv_le_inv₀ hvPos hA).2 hvIcc.1
    dsimp only [f]
    rw [norm_mul, norm_star, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hvPos,
      Complex.norm_exp, norm_gmReflectionPowerWeight hvPos]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero, Complex.ofReal_im, Complex.I_im, sub_self, Real.exp_zero,
      mul_one]
    rw [div_eq_mul_inv]
    exact mul_le_mul hpow hinv (inv_nonneg.mpr hvPos.le)
      (Real.rpow_nonneg hA.le _)
  have hPoint' : ∀ v ∈ Set.uIoc A B, ‖f v‖ ≤ A ^ (-sigma) / A := by
    intro v hv
    exact hPoint v (Set.uIoc_subset_uIcc hv)
  have hBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (a := A) (b := B) (C := A ^ (-sigma) / A) hPoint'
  have hDiff : |B - A| = B - A := abs_of_nonneg (sub_nonneg.mpr hAB)
  simpa only [typeIPowerReflectionIntegral, f, hDiff, mul_comm] using hBound

/-- The fixed reflected polynomial is the only non-unit factor in the
Mellin polynomial. -/
theorem norm_typeIReflectedMellinPolynomial_eq_fixed
    (sigma t Q : ℝ) (M : ℕ) (r : ℝ) (hQ : 0 < Q) :
    ‖typeIReflectedMellinPolynomial sigma t Q M r‖ =
      Q * ‖typeIReflectedFixedPolynomial sigma (t + r) M‖ := by
  rw [typeIReflectedMellinPolynomial_eq_fixed sigma t Q M r hQ,
    norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ,
    Complex.norm_cpow_eq_rpow_re_of_pos hQ]
  simp

/-- Integrability of a negative real power outside a symmetric compact
interval.  This local copy keeps the Type-I reflection layer independent of
the later Type-II contour module. -/
theorem integrableOn_abs_rpow_compl_Icc_typeI {a H : ℝ}
    (ha : a < -1) (hH : 0 < H) :
    IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Icc (-H) H)ᶜ := by
  have hPosInt : IntegrableOn (fun u : ℝ => u ^ a) (Set.Ioi H) :=
    integrableOn_Ioi_rpow_of_lt ha hH
  have hPosAbs : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Ioi H) := by
    apply hPosInt.congr_fun
    · intro u hu
      change u ^ a = |u| ^ a
      rw [abs_of_pos (hH.trans hu)]
    · exact measurableSet_Ioi
  have hNegAbs : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Iio (-H)) := by
    have hPosInt' : IntegrableOn (fun u : ℝ => u ^ a) (Set.Ioi (-(-H))) := by
      simpa only [neg_neg] using hPosInt
    have h : IntegrableOn (fun u : ℝ => (-u) ^ a) (Set.Iio (-H)) :=
      hPosInt'.comp_neg_Iio (c := -H)
    apply h.congr_fun
    · intro u hu
      change (-u) ^ a = |u| ^ a
      rw [abs_of_neg (lt_trans hu (neg_neg_of_pos hH))]
    · exact measurableSet_Iio
  have hCompl : (Set.Icc (-H) H)ᶜ = Set.Iio (-H) ∪ Set.Ioi H := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le,
      Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  rw [hCompl]
  exact hNegAbs.union hPosAbs

/-- Exact integral of a negative real power outside a symmetric compact
interval. -/
theorem integral_abs_rpow_compl_Icc_typeI {a H : ℝ}
    (ha : a < -1) (hH : 0 < H) :
    ∫ u : ℝ in (Set.Icc (-H) H)ᶜ, |u| ^ a =
      -2 * H ^ (a + 1) / (a + 1) := by
  have hPosInt : IntegrableOn (fun u : ℝ => u ^ a) (Set.Ioi H) :=
    integrableOn_Ioi_rpow_of_lt ha hH
  have hNegInt : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Iio (-H)) := by
    have hPosInt' : IntegrableOn (fun u : ℝ => u ^ a) (Set.Ioi (-(-H))) := by
      simpa only [neg_neg] using hPosInt
    have h : IntegrableOn (fun u : ℝ => (-u) ^ a) (Set.Iio (-H)) :=
      hPosInt'.comp_neg_Iio (c := -H)
    apply h.congr_fun
    · intro u hu
      change (-u) ^ a = |u| ^ a
      rw [abs_of_neg (lt_trans hu (neg_neg_of_pos hH))]
    · exact measurableSet_Iio
  have hPosAbs : IntegrableOn (fun u : ℝ => |u| ^ a) (Set.Ioi H) := by
    apply hPosInt.congr_fun
    · intro u hu
      change u ^ a = |u| ^ a
      rw [abs_of_pos (hH.trans hu)]
    · exact measurableSet_Ioi
  have hCompl : (Set.Icc (-H) H)ᶜ = Set.Iio (-H) ∪ Set.Ioi H := by
    ext u
    simp only [Set.mem_compl_iff, Set.mem_Icc, not_and_or, not_le,
      Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  have hDisjoint : Disjoint (Set.Iio (-H)) (Set.Ioi H) := by
    rw [Set.disjoint_left]
    intro u hu hv
    rw [Set.mem_Iio] at hu
    rw [Set.mem_Ioi] at hv
    linarith
  rw [hCompl, setIntegral_union hDisjoint measurableSet_Ioi hNegInt hPosAbs]
  have hNegEq :
      ∫ u : ℝ in Set.Iio (-H), |u| ^ a = ∫ u : ℝ in Set.Ioi H, u ^ a := by
    rw [← integral_Iic_eq_integral_Iio]
    rw [← integral_comp_neg_Ioi H (fun u : ℝ => |u| ^ a)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change |-u| ^ a = u ^ a
    rw [abs_neg, abs_of_pos (hH.trans hu)]
  have hPosEq :
      ∫ u : ℝ in Set.Ioi H, |u| ^ a = ∫ u : ℝ in Set.Ioi H, u ^ a := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change |u| ^ a = u ^ a
    rw [abs_of_pos (hH.trans hu)]
  rw [hNegEq, hPosEq, integral_Ioi_rpow_of_lt ha hH]
  ring

/-- The literal Mellin cutoff has a quantitative integrable tail of every
order greater than one. -/
theorem exists_typeIDyadicCutoffMellin_tail_bound (n : ℕ) (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 1 ≤ H →
      ∫ r : ℝ in (Set.Icc (-H) H)ᶜ,
        ‖typeIDyadicCutoffMellin r‖ ≤ C * H ^ (1 - (n : ℝ)) := by
  obtain ⟨C₀, hC₀, hDecay⟩ := typeIDyadicCutoffMellin_polynomial_decay n
  let C : ℝ := max 1 (2 * C₀ / ((n : ℝ) - 1))
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro H hH
  have hHPos : 0 < H := zero_lt_one.trans_le hH
  have hnReal : (1 : ℝ) < n := by exact_mod_cast hn
  have hDomInt : IntegrableOn
      (fun r : ℝ => C₀ * |r| ^ (-(n : ℝ))) (Set.Icc (-H) H)ᶜ :=
    (integrableOn_abs_rpow_compl_Icc_typeI (by linarith) hHPos).const_mul C₀
  have hMellinInt : Integrable typeIDyadicCutoffMellin := by
    simpa only [typeIDyadicCutoffMellin, VerticalIntegrable] using
      verticalIntegrable_typeIDyadicCutoffMellin
  have hPoint : ∀ᵐ r : ℝ ∂volume.restrict (Set.Icc (-H) H)ᶜ,
      ‖typeIDyadicCutoffMellin r‖ ≤ C₀ * |r| ^ (-(n : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc.compl] with r hr
    have hAbs : H < |r| := by
      by_contra hnot
      exact hr (abs_le.mp (le_of_not_gt hnot))
    have hAbsPos : 0 < |r| := hHPos.trans hAbs
    have hRaw := hDecay r
    rw [show |r| ^ (-(n : ℝ)) = (|r| ^ n)⁻¹ by
      rw [Real.rpow_neg hAbsPos.le]
      norm_num]
    rw [le_mul_inv_iff₀ (pow_pos hAbsPos n)]
    simpa only [mul_comm] using hRaw
  calc
    ∫ r : ℝ in (Set.Icc (-H) H)ᶜ, ‖typeIDyadicCutoffMellin r‖ ≤
        ∫ r : ℝ in (Set.Icc (-H) H)ᶜ, C₀ * |r| ^ (-(n : ℝ)) := by
          exact integral_mono_ae hMellinInt.norm.integrableOn hDomInt hPoint
    _ = (2 * C₀ / ((n : ℝ) - 1)) * H ^ (1 - (n : ℝ)) := by
      rw [integral_const_mul,
        integral_abs_rpow_compl_Icc_typeI (by linarith) hHPos]
      rw [show -(n : ℝ) + 1 = -((n : ℝ) - 1) by ring,
        show 1 - (n : ℝ) = -((n : ℝ) - 1) by ring]
      field_simp [show (n : ℝ) - 1 ≠ 0 by linarith]
    _ ≤ C * H ^ (1 - (n : ℝ)) := by
      exact mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg hHPos.le _)

/-- Exact identification of all retained negative modes with the common
Mellin-reflection integral and its fixed-coefficient polynomial. -/
theorem sourceScalar_mul_negativeModes_eq_reflectedMellinIntegral
    {sigma t : ℝ} {Q M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedNegativeModes sigma t Q M =
      (1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma t (Q : ℝ) M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (t + r)
                ((Q : ℝ) / 2) (2 * M * Q) := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  rw [typeINormalizedNegativeModes, Finset.mul_sum]
  have hEach : ∀ m ∈ Finset.Icc 1 M,
      typeISourceNormalizationScalar sigma t (Q : ℝ) *
          ((Q : ℂ) * typeINormalizedFourier sigma t
            ((Q : ℝ) * (-(m : ℝ)))) =
        ∫ x in (Q : ℝ) / 2..2 * (Q : ℝ),
          typeIDyadicPhysicalIntegrand sigma t (m : ℝ) (Q : ℝ) x := by
    intro m _hm
    exact sourceScalar_mul_normalizedFourier_neg_eq_physicalIntegral
      sigma t (Q : ℝ) m hQr
  calc
    ∑ m ∈ Finset.Icc 1 M,
        typeISourceNormalizationScalar sigma t (Q : ℝ) *
          ((Q : ℂ) * typeINormalizedFourier sigma t
            ((Q : ℝ) * (-(m : ℝ)))) =
      ∑ m ∈ Finset.Icc 1 M,
        ∫ x in (Q : ℝ) / 2..2 * (Q : ℝ),
          typeIDyadicPhysicalIntegrand sigma t (m : ℝ) (Q : ℝ) x := by
            apply Finset.sum_congr rfl
            exact hEach
    _ = _ := sum_typeIDyadicPhysicalIntegral_eq_reflectedMellinPolynomial
      hsigma hQr hM

/-- Exact positive-mode Mellin formula, obtained from the negative-mode
formula without losing cancellation inside the fixed polynomial. -/
theorem sourceScalar_mul_positiveModes_eq_reflectedMellinIntegral
    {sigma t : ℝ} {Q M : ℕ} (hsigma : 0 ≤ sigma)
    (hQ : 0 < Q) (hM : 1 ≤ M) :
    typeISourceNormalizationScalar sigma t (Q : ℝ) *
        typeINormalizedPositiveModes sigma t Q M =
      star ((1 / (2 * Real.pi) : ℝ) •
        ∫ r : ℝ,
          typeIReflectedMellinPolynomial sigma (-t) (Q : ℝ) M r *
            typeIDyadicCutoffMellin r *
              typeIPowerReflectionIntegral sigma (-t + r)
                ((Q : ℝ) / 2) (2 * M * Q)) := by
  rw [typeINormalizedPositiveModes_eq_conj_negative]
  calc
    typeISourceNormalizationScalar sigma t (Q : ℝ) *
        star (typeINormalizedNegativeModes sigma (-t) Q M) =
      star (typeISourceNormalizationScalar sigma (-t) (Q : ℝ)) *
        star (typeINormalizedNegativeModes sigma (-t) Q M) := by
          rw [star_typeISourceNormalizationScalar]
    _ = star (typeISourceNormalizationScalar sigma (-t) (Q : ℝ) *
        typeINormalizedNegativeModes sigma (-t) Q M) :=
          (map_mul (starRingEnd ℂ)
            (typeISourceNormalizationScalar sigma (-t) (Q : ℝ))
            (typeINormalizedNegativeModes sigma (-t) Q M)).symm
    _ = _ := congrArg star
      (sourceScalar_mul_negativeModes_eq_reflectedMellinIntegral
        (t := -t) hsigma hQ hM)

/-- A single positive normalized Poisson mode is the conjugate of the
corresponding physical integral at the reversed ordinate.  Keeping this
identity termwise is what preserves the denominator `t + pi*m*Q` in the
nonstationary estimate below. -/
theorem sourceScalar_mul_normalizedFourier_pos_eq_conj_physicalIntegral
    (sigma t Q : ℝ) (m : ℕ) (hQ : 0 < Q) :
    typeISourceNormalizationScalar sigma t Q *
        ((Q : ℂ) * typeINormalizedFourier sigma t (Q * (m : ℝ))) =
      star (∫ x in Q / 2..2 * Q,
        typeIDyadicPhysicalIntegrand sigma (-t) (m : ℝ) Q x) := by
  have hneg := sourceScalar_mul_normalizedFourier_neg_eq_physicalIntegral
    sigma (-t) Q m hQ
  have hfreq : Q * (m : ℝ) = -(Q * (-(m : ℝ))) := by ring
  calc
    typeISourceNormalizationScalar sigma t Q *
        ((Q : ℂ) * typeINormalizedFourier sigma t (Q * (m : ℝ))) =
      star (typeISourceNormalizationScalar sigma (-t) Q) *
        ((Q : ℂ) * star (typeINormalizedFourier sigma (-t)
          (Q * (-(m : ℝ))))) := by
            rw [star_typeISourceNormalizationScalar, hfreq,
              typeINormalizedFourier_neg_eq_conj]
    _ = star (typeISourceNormalizationScalar sigma (-t) Q *
        ((Q : ℂ) * typeINormalizedFourier sigma (-t)
          (Q * (-(m : ℝ))))) := by
            calc
              star (typeISourceNormalizationScalar sigma (-t) Q) *
                  ((Q : ℂ) * star (typeINormalizedFourier sigma (-t)
                    (Q * (-(m : ℝ))))) =
                star (typeISourceNormalizationScalar sigma (-t) Q) *
                  star ((Q : ℂ) * typeINormalizedFourier sigma (-t)
                    (Q * (-(m : ℝ)))) := by
                      congr 1
                      change (Q : ℂ) * star (typeINormalizedFourier sigma (-t)
                        (Q * (-(m : ℝ)))) =
                        (starRingEnd ℂ) ((Q : ℂ) *
                          typeINormalizedFourier sigma (-t) (Q * (-(m : ℝ))))
                      rw [map_mul]
                      simp only [Complex.star_def, Complex.conj_ofReal]
              _ = _ := (map_mul (starRingEnd ℂ)
                (typeISourceNormalizationScalar sigma (-t) Q)
                ((Q : ℂ) * typeINormalizedFourier sigma (-t)
                  (Q * (-(m : ℝ))))).symm
    _ = _ := congrArg star hneg

/-- The logarithmic terminal comparison tends to zero whenever the detector
loss exponent is strictly smaller than the fixed line. -/
theorem tendsto_typeI_terminal_ratio
    (σ δ₂ : ℝ) (hδ₂σ : δ₂ < σ) :
    Tendsto
      (fun T : ℝ =>
        (1 + (Real.log 6 + Real.log T) / Real.log 2) *
          T ^ (δ₂ - σ)) atTop (𝓝 0) := by
  let d := σ - δ₂
  have hd : 0 < d := by dsimp [d]; linarith
  have hPow : Tendsto (fun T : ℝ => T ^ (-d)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop hd
  have hLogPow : Tendsto (fun T : ℝ => Real.log T * T ^ (-d))
      atTop (𝓝 0) := by
    have hDiv := (isLittleO_log_rpow_atTop hd).tendsto_div_nhds_zero
    apply hDiv.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Real.rpow_neg hT.le, div_eq_mul_inv]
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  have hExpanded : Tendsto
      (fun T : ℝ =>
        (1 + Real.log 6 / Real.log 2) * T ^ (-d) +
          (1 / Real.log 2) * (Real.log T * T ^ (-d)))
      atTop (𝓝 0) := by
    convert (hPow.const_mul (1 + Real.log 6 / Real.log 2)).add
      (hLogPow.const_mul (1 / Real.log 2)) using 1
    all_goals norm_num
  apply Tendsto.congr' _ hExpanded
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hExp : δ₂ - σ = -d := by dsimp [d]; ring
  rw [hExp]
  field_simp [hlogTwo]
  ring

/-- Uniform terminal comparison for every actual Type-I witness whose scale
has reached its ordinate.  Consequently a positive dichotomy block cannot
remain at or beyond the height. -/
theorem eventually_typeI_start_lt_ordinate
    (σ δ₂ : ℝ) (hσ : 0 ≤ σ) (hδ₂σ : δ₂ < σ) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T t : ℝ) (C N : ℕ), T₀ ≤ T →
      C = ⌊sharpZetaCutoff T⌋₊ → 0 < N → N < C →
      T / 2 ≤ t → t ≤ (N : ℝ) →
      ((N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (N : ℝ) / t) <
        ((3 / 4) * (T ^ (-δ₂) / 2)) / Nat.clog 2 C) := by
  have hTendsto := tendsto_typeI_terminal_ratio σ δ₂ hδ₂σ
  let c : ℝ := 96 * Real.pi * 2 ^ σ
  have hc : 0 < c := by dsimp [c]; positivity
  have hEventually : ∀ᶠ T : ℝ in atTop,
      c * ((1 + (Real.log 6 + Real.log T) / Real.log 2) *
        T ^ (δ₂ - σ)) < 3 / 8 := by
    have hScaled := hTendsto.const_mul c
    exact (tendsto_order.1 hScaled).2 (3 / 8) (by norm_num)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tscale, hTscale⟩ := hEventually
  let T₀ := max 8 Tscale
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T t C N hT hC hN hNC htLower htN
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hTscale' : Tscale ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have htPos : 0 < t := by linarith
  have hNPos : (0 : ℝ) < N := by exact_mod_cast hN
  have hCUpper : (C : ℝ) ≤ 6 * T := by
    subst C
    have hCutNonneg : 0 ≤ sharpZetaCutoff T := by
      linarith [four_mul_lt_sharpZetaCutoff T]
    exact (Nat.floor_le hCutNonneg).trans
      (sharpZetaCutoff_le_six_mul (by linarith))
  have hNUpper : (N : ℝ) ≤ 6 * T := by
    exact (by exact_mod_cast hNC.le : (N : ℝ) ≤ C) |>.trans hCUpper
  have hRatio : (N : ℝ) / t ≤ 12 := by
    rw [div_le_iff₀ htPos]
    nlinarith
  have hWeight : (N + 1 : ℝ) ^ (-σ) ≤ (T / 2) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact htLower.trans (htN.trans (by exact_mod_cast Nat.le_add_right N 1))
    · linarith
  have hTerminal :
      (N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (N : ℝ) / t) ≤
        (T / 2) ^ (-σ) * (72 * Real.pi) := by
    calc
      (N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * (N : ℝ) / t) =
          (N + 1 : ℝ) ^ (-σ) * (6 * Real.pi * ((N : ℝ) / t)) := by ring
      _ ≤ (T / 2) ^ (-σ) * (6 * Real.pi * 12) := by gcongr
      _ = (T / 2) ^ (-σ) * (72 * Real.pi) := by ring
  have hClogPos : 0 < Nat.clog 2 C := by
    apply Nat.clog_pos Nat.one_lt_two
    have hCutLower : (2 : ℝ) ≤ sharpZetaCutoff T := by
      linarith [four_mul_lt_sharpZetaCutoff T]
    subst C
    exact lt_of_lt_of_le (by omega : 1 < 2)
      ((Nat.le_floor_iff (by positivity)).2 hCutLower)
  have hClogBound := sharp_cutoff_clog_le_log_majorant T hTEight
  rw [← hC] at hClogBound
  have hBaseLogPos : 0 <
      1 + (Real.log 6 + Real.log T) / Real.log 2 := by
    have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hlogSix : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have hPowerIdentity : (T / 2) ^ (-σ) * T ^ δ₂ =
      2 ^ σ * T ^ (δ₂ - σ) := by
    rw [Real.div_rpow (by linarith : 0 ≤ T) (by norm_num : (0 : ℝ) ≤ 2),
      div_eq_mul_inv, Real.rpow_neg (by positivity : (0 : ℝ) ≤ 2),
      inv_inv]
    calc
      T ^ (-σ) * 2 ^ σ * T ^ δ₂ =
          2 ^ σ * (T ^ (-σ) * T ^ δ₂) := by ring
      _ = 2 ^ σ * T ^ (δ₂ - σ) := by
        rw [← Real.rpow_add hTPos]
        congr 2
        ring
  have hScaled :
      (72 * Real.pi) * (T / 2) ^ (-σ) *
          (Nat.clog 2 C : ℝ) * T ^ δ₂ < 3 / 8 := by
    calc
      (72 * Real.pi) * (T / 2) ^ (-σ) *
            (Nat.clog 2 C : ℝ) * T ^ δ₂ =
          (72 * Real.pi) * (Nat.clog 2 C : ℝ) *
            ((T / 2) ^ (-σ) * T ^ δ₂) := by ring
      _ = (72 * Real.pi * 2 ^ σ) *
            ((Nat.clog 2 C : ℝ) * T ^ (δ₂ - σ)) := by
          rw [hPowerIdentity]
          ring
      _ ≤ c * ((1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (δ₂ - σ)) := by
          dsimp [c]
          gcongr
          norm_num
      _ < 3 / 8 := hTscale T hTscale'
  have hThreshold :
      (72 * Real.pi) * (T / 2) ^ (-σ) <
        ((3 / 4) * (T ^ (-δ₂) / 2)) / Nat.clog 2 C := by
    have hClogReal : (0 : ℝ) < Nat.clog 2 C := by exact_mod_cast hClogPos
    have hTPow : 0 < T ^ δ₂ := Real.rpow_pos_of_pos hTPos _
    rw [show (3 / 4) * (T ^ (-δ₂) / 2) =
        (3 / 8) / T ^ δ₂ by
      rw [Real.rpow_neg hTPos.le]
      field_simp
      ring]
    rw [div_div, lt_div_iff₀ (mul_pos hTPow hClogReal)]
    nlinarith
  exact hTerminal.trans_lt (by simpa [mul_comm] using hThreshold)

/-- The endpoint certificate forces one of the two classical MHH branches to
control the whole subdivision envelope.  This is the analytic content hidden
in the paper's Corollary 11.10 subdivision: it is derived here from the
certificate at the boundary `τ₀ + σ - 1`, not assumed for the current scale. -/
theorem classicalMHHExponent_le_corollary1110Envelope_of_certificate
    {σ τ₀ τ : ℝ} (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    classicalMHHExponent σ τ ≤ corollary1110Envelope σ τ₀ τ := by
  have hBoundaryNonneg : 0 ≤ τ₀ + σ - 1 := by
    have hBase := hcert.density_base_le_tau0
    linarith
  have hBoundary := hcert.mhh_window (τ₀ + σ - 1)
    hBoundaryNonneg (le_rfl)
  have hMin : min (τ₀ - σ) (τ₀ + 3 - 5 * σ) ≤ 2 - 2 * σ := by
    rw [classicalMHHExponent, max_le_iff] at hBoundary
    convert hBoundary.2 using 1
    all_goals ring_nf
  have hAlternative : τ₀ ≤ 2 - σ ∨ τ₀ ≤ 3 * σ - 1 := by
    rcases le_total (τ₀ - σ) (τ₀ + 3 - 5 * σ) with h | h
    · left
      rw [min_eq_left h] at hMin
      linarith
    · right
      rw [min_eq_right h] at hMin
      linarith
  rw [classicalMHHExponent, corollary1110Envelope, max_le_iff]
  refine ⟨le_max_left _ _, ?_⟩
  rcases hAlternative with hτ₀ | hτ₀
  · have ha : τ + 1 - 2 * σ ≤ 3 - 3 * σ + τ - τ₀ := by linarith
    exact (min_le_left _ _).trans (ha.trans (le_max_right _ _))
  · have hb : τ + 4 - 6 * σ ≤ 3 - 3 * σ + τ - τ₀ := by linarith
    exact (min_le_right _ _).trans (hb.trans (le_max_right _ _))

/-- The endpoint certificate itself forces one of the two classical endpoint
upper bounds for `τ₀`.  This numerical consequence is used to obtain a
strict decay margin in the medium Type-I range. -/
theorem endpointScaleCertificate_tau0_alternative
    {σ τ₀ : ℝ} (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    τ₀ ≤ 2 - σ ∨ τ₀ ≤ 3 * σ - 1 := by
  have hBoundaryNonneg : 0 ≤ τ₀ + σ - 1 := by
    linarith [hcert.density_base_le_tau0]
  have hBoundary := hcert.mhh_window (τ₀ + σ - 1)
    hBoundaryNonneg (le_rfl)
  have hMin : min (τ₀ - σ) (τ₀ + 3 - 5 * σ) ≤ 2 - 2 * σ := by
    rw [classicalMHHExponent, max_le_iff] at hBoundary
    convert hBoundary.2 using 1
    all_goals ring_nf
  rcases le_total (τ₀ - σ) (τ₀ + 3 - 5 * σ) with h | h
  · left
    rw [min_eq_left h] at hMin
    linarith
  · right
    rw [min_eq_right h] at hMin
    linarith

theorem endpointScaleCertificate_tau0_lt_two
    {σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) : τ₀ < 2 := by
  rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
  · linarith
  · linarith

/-- A scale in the basic endpoint window is at least the square root of the
physical height.  This is the exact comparison used to absorb the raw
detector threshold into the normalized Type-I threshold. -/
theorem physical_height_le_sq_of_basic_endpoint_scale
    {T : ℝ} {Q : ℕ} {σ τ₀ : ℝ}
    (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hT : 0 < T) (hQ : 1 < Q)
    (hτUpper : typeILogarithmicScale T Q ≤ τ₀) :
    T ≤ (Q : ℝ) ^ (2 : ℕ) := by
  have hBase : (1 : ℝ) < Q := by exact_mod_cast hQ
  have hTauTwo : typeILogarithmicScale T Q ≤ 2 :=
    hτUpper.trans (endpointScaleCertificate_tau0_lt_two
      hσLower hσUpper hcert).le
  simpa only [Real.rpow_two] using
    (Real.logb_le_iff_le_rpow hBase hT).mp hTauTwo

/-- Explicit reciprocal loss converting the detector's raw Type-I
threshold into the normalized `N^σ` threshold. -/
noncomputable def typeIDirectThresholdLoss (T : ℝ) (A : ℕ) (d : ℝ) : ℝ :=
  1 + (8 / 3 : ℝ) * Nat.clog 2 A * T ^ d

noncomputable def typeIDirectPowerLossConstant : ℝ :=
  max 1 ((2 / 3 : ℝ) * (1 + 2 / Real.log 2))

/-- Coarse but source-faithful envelope for finite-power normalization
losses after the exact `N^σ` cancellation. -/
noncomputable def classicalTypeIIPowerLoss
    (A d T : ℝ) (k Q : ℕ) : ℝ :=
  A * (((2 : ℝ) ^ k) * Q) ^ (2 * d) * (k : ℝ) *
    (4 * Real.log T) ^ k

theorem typeIDirectPowerLossConstant_pos : 0 < typeIDirectPowerLossConstant := by
  unfold typeIDirectPowerLossConstant
  exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem typeI_direct_normalized_threshold_lower
    {T d σ : ℝ} {A N : ℕ}
    (hT : 0 < T) (hA : 1 < A) :
    (N : ℝ) ^ σ / typeIDirectThresholdLoss T A d ≤
      (N : ℝ) ^ σ *
        (((3 / 4 : ℝ) * (T ^ (-d) / 2)) / Nat.clog 2 A) := by
  have hClogNat : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hA
  have hClog : (0 : ℝ) < Nat.clog 2 A := by exact_mod_cast hClogNat
  have hTd : 0 < T ^ d := Real.rpow_pos_of_pos hT _
  let R : ℝ := (8 / 3 : ℝ) * Nat.clog 2 A * T ^ d
  have hR : 0 < R := by dsimp only [R]; positivity
  have hLoss : 0 < typeIDirectThresholdLoss T A d := by
    dsimp only [typeIDirectThresholdLoss]
    positivity
  have hRecip : 1 / typeIDirectThresholdLoss T A d ≤
      ((3 / 4 : ℝ) * (T ^ (-d) / 2)) / Nat.clog 2 A := by
    have hInv : T ^ (-d) = (T ^ d)⁻¹ := Real.rpow_neg hT.le d
    rw [hInv]
    have hRight :
        ((3 / 4 : ℝ) * ((T ^ d)⁻¹ / 2)) / Nat.clog 2 A = 1 / R := by
      dsimp only [R]
      field_simp [hTd.ne', hClog.ne']
      ring
    rw [hRight]
    apply one_div_le_one_div_of_le hR
    dsimp only [typeIDirectThresholdLoss, R]
    linarith
  calc
    (N : ℝ) ^ σ / typeIDirectThresholdLoss T A d =
        (N : ℝ) ^ σ * (1 / typeIDirectThresholdLoss T A d) := by ring
    _ ≤ (N : ℝ) ^ σ *
        (((3 / 4 : ℝ) * (T ^ (-d) / 2)) / Nat.clog 2 A) :=
      mul_le_mul_of_nonneg_left hRecip (Real.rpow_nonneg (Nat.cast_nonneg N) _)

/-- On a basic-window scale the explicit direct-threshold loss is bounded
by the common finite-power loss expression.  The proof derives the cutoff
`clog`, logarithm, and `T ≤ N²` comparisons rather than assuming them. -/
theorem typeIDirectThresholdLoss_le_classicalTypeIIPowerLoss
    {T : ℝ} {A N : ℕ} {d : ℝ}
    (hT : 8 ≤ T) (hd : 0 ≤ d) (hN : 1 < N)
    (hAcut : A ≤ ⌊sharpZetaCutoff T⌋₊)
    (hTN : T ≤ (N : ℝ) ^ (2 : ℕ)) :
    typeIDirectThresholdLoss T A d ≤
      1 + classicalTypeIIPowerLoss typeIDirectPowerLossConstant d T 1 N := by
  have hTPos : 0 < T := by linarith
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLogSixT : Real.log 6 ≤ Real.log T := by
    exact Real.log_le_log (by norm_num) (by linarith)
  have hExpT : Real.exp 1 ≤ T := by
    calc
      Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
      _ ≤ 8 := by norm_num
      _ ≤ T := hT
  have hLogOne : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hExpT
  have hClogRaw := sharp_cutoff_clog_le_log_majorant T hT
  have hClog : (Nat.clog 2 A : ℝ) ≤
      (1 + 2 / Real.log 2) * Real.log T := by
    calc
      (Nat.clog 2 A : ℝ) ≤
          (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) := by
            exact_mod_cast Nat.clog_mono_right 2 hAcut
      _ ≤ 1 + (Real.log 6 + Real.log T) / Real.log 2 := hClogRaw
      _ ≤ (1 + 2 / Real.log 2) * Real.log T := by
        have hNumerator : Real.log 6 + Real.log T ≤ 2 * Real.log T := by
          linarith
        have hFrac : (Real.log 6 + Real.log T) / Real.log 2 ≤
            (2 * Real.log T) / Real.log 2 := by
          exact div_le_div_of_nonneg_right hNumerator hLogTwo.le
        calc
          1 + (Real.log 6 + Real.log T) / Real.log 2 ≤
              1 + (2 * Real.log T) / Real.log 2 := by linarith
          _ ≤ Real.log T + (2 * Real.log T) / Real.log 2 := by linarith
          _ = (1 + 2 / Real.log 2) * Real.log T := by ring
  have hTd : T ^ d ≤ (N : ℝ) ^ (2 * d) := by
    calc
      T ^ d ≤ ((N : ℝ) ^ (2 : ℕ)) ^ d :=
        Real.rpow_le_rpow hTPos.le hTN hd
      _ = (N : ℝ) ^ (2 * d) := by
        rw [← Real.rpow_two, ← Real.rpow_mul (by positivity)]
  have hScale : (N : ℝ) ^ (2 * d) ≤
      ((2 : ℝ) * N) ^ (2 * d) := by
    exact Real.rpow_le_rpow (by positivity) (by nlinarith [show (0 : ℝ) ≤ N by positivity])
      (by positivity)
  have hConst : (8 / 3 : ℝ) * (1 + 2 / Real.log 2) ≤
      typeIDirectPowerLossConstant * 4 := by
    have h := le_max_right 1 ((2 / 3 : ℝ) * (1 + 2 / Real.log 2))
    dsimp only [typeIDirectPowerLossConstant]
    nlinarith
  have hCore : (8 / 3 : ℝ) * (Nat.clog 2 A : ℝ) * T ^ d ≤
      typeIDirectPowerLossConstant *
        (((2 : ℝ) * N) ^ (2 * d)) * (4 * Real.log T) := by
    have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
    have hTdNonneg : 0 ≤ T ^ d := Real.rpow_nonneg hTPos.le _
    have hConstNonneg : 0 ≤ typeIDirectPowerLossConstant * 4 := by
      positivity [typeIDirectPowerLossConstant_pos]
    have hTdScale : T ^ d ≤ ((2 : ℝ) * N) ^ (2 * d) := hTd.trans hScale
    calc
      (8 / 3 : ℝ) * (Nat.clog 2 A : ℝ) * T ^ d ≤
          (8 / 3 : ℝ) *
            ((1 + 2 / Real.log 2) * Real.log T) * T ^ d := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hClog (by norm_num)) hTdNonneg
      _ = ((8 / 3 : ℝ) * (1 + 2 / Real.log 2)) *
            (Real.log T * T ^ d) := by ring
      _ ≤ (typeIDirectPowerLossConstant * 4) *
            (Real.log T * T ^ d) :=
          mul_le_mul_of_nonneg_right hConst (mul_nonneg hLogNonneg hTdNonneg)
      _ ≤ (typeIDirectPowerLossConstant * 4) *
            (Real.log T * ((2 : ℝ) * N) ^ (2 * d)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hTdScale hLogNonneg) hConstNonneg
      _ = typeIDirectPowerLossConstant *
          (((2 : ℝ) * N) ^ (2 * d)) * (4 * Real.log T) := by ring
  unfold typeIDirectThresholdLoss classicalTypeIIPowerLoss
  norm_num
  linarith

/-- Quantitative slack below the basic endpoint window.  The deliberately
small common loss parameter leaves a hundred powers of `T^d` between the
medium B-process bound and the detector threshold. -/
theorem endpoint_medium_exponent_margin
    {σ τ₀ d τ : ℝ} (hσ : 1 / 2 < σ)
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hdGap : d ≤ (σ - 1 / 2) / 1000)
    (hdSmall : d ≤ 1 / (1000 * (1 + τ₀)))
    (hτ : τ < 2 * τ₀ / 3) :
    τ / 2 - σ < -100 * d := by
  have hTauPos := hcert.tau0_pos
  rcases endpointScaleCertificate_tau0_alternative hσUpper hcert with hI | hH
  · have hd : 300 * d ≤ 4 * σ - 2 := by
      calc
        300 * d ≤ 300 * ((σ - 1 / 2) / 1000) := by gcongr
        _ ≤ 4 * σ - 2 := by nlinarith
    nlinarith
  · have hd : 300 * d ≤ 1 := by
      have hden : 0 < 1000 * (1 + τ₀) := by positivity
      have hsmall : d ≤ 1 / 1000 := by
        calc
          d ≤ 1 / (1000 * (1 + τ₀)) := hdSmall
          _ ≤ 1 / 1000 := by
            apply one_div_le_one_div_of_le (by norm_num)
            nlinarith
      nlinarith
    nlinarith

/-- The logarithmic and fixed numerical losses in the medium B-process are
absorbed by the quantitative gap `50 d - u`. -/
theorem tendsto_typeI_medium_detector_ratio
    (d u : ℝ) (hd : 0 < d) (hu : u ≤ d) :
    Tendsto
      (fun T : ℝ =>
        (800 / 3 : ℝ) * Real.sqrt 3 *
          (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (u - 50 * d)) atTop (𝓝 0) := by
  let a : ℝ := 50 * d - u
  have ha : 0 < a := by dsimp only [a]; nlinarith
  have hPow : Tendsto (fun T : ℝ => T ^ (-a)) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop ha
  have hLogPow : Tendsto (fun T : ℝ => Real.log T * T ^ (-a))
      atTop (𝓝 0) := by
    have hDiv := (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero
    apply hDiv.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [Real.rpow_neg hT.le, div_eq_mul_inv]
  let c : ℝ := (800 / 3 : ℝ) * Real.sqrt 3
  have hExpanded : Tendsto
      (fun T : ℝ =>
        c * (1 + Real.log 6 / Real.log 2) * T ^ (-a) +
          (c / Real.log 2) * (Real.log T * T ^ (-a)))
      atTop (𝓝 0) := by
    convert (hPow.const_mul (c * (1 + Real.log 6 / Real.log 2))).add
      (hLogPow.const_mul (c / Real.log 2)) using 1
    norm_num
  apply Tendsto.congr' _ hExpanded
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hExp : u - 50 * d = -a := by dsimp only [a]; ring
  rw [hExp]
  dsimp only [c]
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  field_simp [hlogTwo]
  ring

/-- Uniform scalar form of `tendsto_typeI_medium_detector_ratio`. -/
theorem eventually_typeI_medium_detector_ratio_lt_one
    (d u : ℝ) (hd : 0 < d) (hu : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      (800 / 3 : ℝ) * Real.sqrt 3 *
        (1 + (Real.log 6 + Real.log T) / Real.log 2) *
          T ^ (u - 50 * d) < 1 := by
  have hTendsto := tendsto_typeI_medium_detector_ratio d u hd hu
  have hEventually := (tendsto_order.1 hTendsto).2 (1 : ℝ) (by norm_num)
  rw [eventually_atTop] at hEventually
  obtain ⟨Tscale, hTscale⟩ := hEventually
  let T₀ := max 8 Tscale
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T hT
  exact hTscale T ((le_max_right _ _).trans hT)

/-- Uniform sharp-block contradiction from the numerical B-process margin
`tau / 2 - sigma < -100 d`.  This is the analytic core of the terminal
Type-I route, separated from any particular endpoint-window hypothesis so
that the actual medium consumer can split at the precise point where the
dual scale begins to grow by a fixed positive power. -/
theorem eventually_medium_typeI_majorant_lt_detector_of_margin
    {sigma d u : ℝ} (hsigma : 0 < sigma) (hsigmaUpper : sigma < 1)
    (hd : 0 < d) (huD : u ≤ d) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T t : ℝ) (N : ℕ), T₀ ≤ T →
      1 < N → 0 ≤ t → t ≤ 3 * T →
      typeILogarithmicScale T N / 2 - sigma < -100 * d →
      (N + 1 : ℝ) ^ (-sigma) * (100 * Real.sqrt t) <
        ((3 / 4) * (T ^ (-u) / 2)) /
          Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ := by
  obtain ⟨Tratio, hTratio, hRatio⟩ :=
    eventually_typeI_medium_detector_ratio_lt_one d u hd huD
  let T₀ : ℝ := max Tratio 8
  refine ⟨T₀, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro T t N hT hN htNonneg htUpper hTauMargin
  have hTratio' : Tratio ≤ T := (le_max_left _ _).trans hT
  have hTEight : 8 ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  let tau := typeILogarithmicScale T N
  have hTauTwo : tau < 2 := by
    dsimp only [tau]
    linarith
  have hNReal : (1 : ℝ) < N := by exact_mod_cast hN
  have hScale : (N : ℝ) ^ tau = T := by
    simpa only [tau] using rpow_typeILogarithmicScale_eq hTPos hN
  have hTNsq : T ≤ (N : ℝ) ^ (2 : ℕ) := by
    rw [← hScale, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hNReal.le hTauTwo.le
  have hWeight : (N + 1 : ℝ) ^ (-sigma) ≤ (N : ℝ) ^ (-sigma) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast (Nat.le_add_right N 1)
    · linarith
  have hSqrt : Real.sqrt t ≤ Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt t ≤ Real.sqrt (3 * T) := Real.sqrt_le_sqrt htUpper
      _ = Real.sqrt 3 * Real.sqrt T := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
        congr 1
        exact Real.sqrt_eq_rpow T
  have hScaleHalf : T ^ (1 / 2 : ℝ) = (N : ℝ) ^ (tau / 2) := by
    rw [← hScale, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have hNExponent : (N : ℝ) ^ (tau / 2 - sigma) ≤
      (N : ℝ) ^ (-100 * d) :=
    Real.rpow_le_rpow_of_exponent_le hNReal.le hTauMargin.le
  have hNToT : (N : ℝ) ^ (-100 * d) ≤ T ^ (-50 * d) := by
    have hExpNonpos : -50 * d ≤ 0 := by linarith
    calc
      (N : ℝ) ^ (-100 * d) =
          ((N : ℝ) ^ (2 : ℕ)) ^ (-50 * d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        ring
      _ ≤ T ^ (-50 * d) :=
        Real.rpow_le_rpow_of_nonpos hTPos hTNsq hExpNonpos
  have hMajorant :
      (N + 1 : ℝ) ^ (-sigma) * (100 * Real.sqrt t) ≤
        100 * Real.sqrt 3 * T ^ (-50 * d) := by
    calc
      (N + 1 : ℝ) ^ (-sigma) * (100 * Real.sqrt t) ≤
          (N : ℝ) ^ (-sigma) *
            (100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ))) := by gcongr
      _ = 100 * Real.sqrt 3 *
          ((N : ℝ) ^ (-sigma) * (N : ℝ) ^ (tau / 2)) := by
        rw [hScaleHalf]
        ring
      _ = 100 * Real.sqrt 3 * (N : ℝ) ^ (tau / 2 - sigma) := by
        rw [← Real.rpow_add (by positivity)]
        congr 2
        ring
      _ ≤ 100 * Real.sqrt 3 * (N : ℝ) ^ (-100 * d) := by gcongr
      _ ≤ 100 * Real.sqrt 3 * T ^ (-50 * d) := by gcongr
  let A := ⌊sharpZetaCutoff T⌋₊
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hClogPos : 0 < (Nat.clog 2 A : ℝ) := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two hAOne
  have hClog := sharp_cutoff_clog_le_log_majorant T hTEight
  have hEnvelopeNonneg : 0 ≤
      1 + (Real.log 6 + Real.log T) / Real.log 2 := by
    have hLogT : 0 ≤ Real.log T := Real.log_nonneg hTOne
    have hLogSix : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    positivity
  have hRatioAt := hRatio T hTratio'
  have hRatioSmall :
      100 * Real.sqrt 3 *
          (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (u - 50 * d) < 3 / 8 := by
    nlinarith [Real.sqrt_nonneg 3]
  have hPowSplit : T ^ (u - 50 * d) * T ^ (-u) = T ^ (-50 * d) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hNumerator :
      (Nat.clog 2 A : ℝ) *
          (100 * Real.sqrt 3 * T ^ (-50 * d)) <
        (3 / 4) * (T ^ (-u) / 2) := by
    have hMul := mul_lt_mul_of_pos_right hRatioSmall
      (Real.rpow_pos_of_pos hTPos (-u))
    calc
      (Nat.clog 2 A : ℝ) *
          (100 * Real.sqrt 3 * T ^ (-50 * d)) ≤
          (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            (100 * Real.sqrt 3 * T ^ (-50 * d)) := by gcongr
      _ = (100 * Real.sqrt 3 *
          (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (u - 50 * d)) * T ^ (-u) := by
        rw [← hPowSplit]
        ring
      _ < (3 / 8) * T ^ (-u) := hMul
      _ = (3 / 4) * (T ^ (-u) / 2) := by ring
  change (N + 1 : ℝ) ^ (-sigma) * (100 * Real.sqrt t) <
    ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A : ℝ)
  rw [lt_div_iff₀ hClogPos]
  calc
    (N + 1 : ℝ) ^ (-sigma) * (100 * Real.sqrt t) * (Nat.clog 2 A : ℝ) ≤
        (100 * Real.sqrt 3 * T ^ (-50 * d)) * (Nat.clog 2 A : ℝ) := by
      gcongr
    _ < (3 / 4) * (T ^ (-u) / 2) := by
      simpa only [mul_comm] using hNumerator

/-- Below the basic endpoint window, the actual finite B-process majorant is
strictly smaller than the literal detector threshold.  Every floor, clog and
fixed numerical loss is retained in the statement. -/
theorem eventually_medium_typeI_majorant_lt_detector
    {σ τ₀ d u : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hd : 0 < d) (huD : u ≤ d)
    (hdGap : d ≤ (σ - 1 / 2) / 1000)
    (hdSmall : d ≤ 1 / (1000 * (1 + τ₀))) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ (T t : ℝ) (N : ℕ), T₀ ≤ T →
      1 < N → 0 ≤ t → t ≤ 3 * T →
      typeILogarithmicScale T N < 2 * τ₀ / 3 →
      (N + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) <
        ((3 / 4) * (T ^ (-u) / 2)) /
          Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ := by
  obtain ⟨Tratio, hTratio, hRatio⟩ :=
    eventually_typeI_medium_detector_ratio_lt_one d u hd huD
  let T₀ : ℝ := max Tratio 8
  refine ⟨T₀, le_trans (by norm_num) (le_max_right _ _), ?_⟩
  intro T t N hT hN htNonneg htUpper hTauLow
  have hTratio' : Tratio ≤ T := (le_max_left _ _).trans hT
  have hTEight : 8 ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  let τ := typeILogarithmicScale T N
  have hTauMargin : τ / 2 - σ < -100 * d :=
    endpoint_medium_exponent_margin hσLower hσUpper hcert hdGap hdSmall
      (by simpa only [τ] using hTauLow)
  have hTauTwo : τ < 2 := by
    have hTau0Two := endpointScaleCertificate_tau0_lt_two hσLower hσUpper hcert
    dsimp only [τ]
    nlinarith [hcert.tau0_pos]
  have hNReal : (1 : ℝ) < N := by exact_mod_cast hN
  have hScale : (N : ℝ) ^ τ = T := by
    simpa only [τ] using rpow_typeILogarithmicScale_eq hTPos hN
  have hTNsq : T ≤ (N : ℝ) ^ (2 : ℕ) := by
    rw [← hScale, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hNReal.le hTauTwo.le
  have hWeight : (N + 1 : ℝ) ^ (-σ) ≤ (N : ℝ) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast (Nat.le_add_right N 1)
    · linarith
  have hSqrt : Real.sqrt t ≤ Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt t ≤ Real.sqrt (3 * T) := Real.sqrt_le_sqrt htUpper
      _ = Real.sqrt 3 * Real.sqrt T := by rw [Real.sqrt_mul (by norm_num)]
      _ = Real.sqrt 3 * T ^ (1 / 2 : ℝ) := by
        congr 1
        exact Real.sqrt_eq_rpow T
  have hScaleHalf : T ^ (1 / 2 : ℝ) = (N : ℝ) ^ (τ / 2) := by
    rw [← hScale, ← Real.rpow_mul (by positivity)]
    congr 1
    ring
  have hNExponent : (N : ℝ) ^ (τ / 2 - σ) ≤
      (N : ℝ) ^ (-100 * d) :=
    Real.rpow_le_rpow_of_exponent_le hNReal.le hTauMargin.le
  have hNToT : (N : ℝ) ^ (-100 * d) ≤ T ^ (-50 * d) := by
    have hExpNonpos : -50 * d ≤ 0 := by linarith
    calc
      (N : ℝ) ^ (-100 * d) =
          ((N : ℝ) ^ (2 : ℕ)) ^ (-50 * d) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        ring
      _ ≤ T ^ (-50 * d) :=
        Real.rpow_le_rpow_of_nonpos hTPos hTNsq hExpNonpos
  have hMajorant :
      (N + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) ≤
        100 * Real.sqrt 3 * T ^ (-50 * d) := by
    calc
      (N + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) ≤
          (N : ℝ) ^ (-σ) *
            (100 * (Real.sqrt 3 * T ^ (1 / 2 : ℝ))) := by gcongr
      _ = 100 * Real.sqrt 3 *
          ((N : ℝ) ^ (-σ) * (N : ℝ) ^ (τ / 2)) := by
        rw [hScaleHalf]
        ring
      _ = 100 * Real.sqrt 3 * (N : ℝ) ^ (τ / 2 - σ) := by
        rw [← Real.rpow_add (by positivity)]
        congr 2
        ring
      _ ≤ 100 * Real.sqrt 3 * (N : ℝ) ^ (-100 * d) := by gcongr
      _ ≤ 100 * Real.sqrt 3 * T ^ (-50 * d) := by gcongr
  let A := ⌊sharpZetaCutoff T⌋₊
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hClogPos : 0 < (Nat.clog 2 A : ℝ) := by
    exact_mod_cast Nat.clog_pos Nat.one_lt_two hAOne
  have hClog := sharp_cutoff_clog_le_log_majorant T hTEight
  have hEnvelopeNonneg : 0 ≤
      1 + (Real.log 6 + Real.log T) / Real.log 2 := by
    have hLogT : 0 ≤ Real.log T := Real.log_nonneg hTOne
    have hLogSix : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
    positivity
  have hRatioAt := hRatio T hTratio'
  have hRatioSmall :
      100 * Real.sqrt 3 *
          (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (u - 50 * d) < 3 / 8 := by
    nlinarith [Real.sqrt_nonneg 3]
  have hPowSplit : T ^ (u - 50 * d) * T ^ (-u) = T ^ (-50 * d) := by
    rw [← Real.rpow_add hTPos]
    congr 1
    ring
  have hNumerator :
      (Nat.clog 2 A : ℝ) *
          (100 * Real.sqrt 3 * T ^ (-50 * d)) <
        (3 / 4) * (T ^ (-u) / 2) := by
    have hMul := mul_lt_mul_of_pos_right hRatioSmall
      (Real.rpow_pos_of_pos hTPos (-u))
    calc
      (Nat.clog 2 A : ℝ) *
          (100 * Real.sqrt 3 * T ^ (-50 * d)) ≤
          (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            (100 * Real.sqrt 3 * T ^ (-50 * d)) := by gcongr
      _ = (100 * Real.sqrt 3 *
          (1 + (Real.log 6 + Real.log T) / Real.log 2) *
            T ^ (u - 50 * d)) * T ^ (-u) := by
        rw [← hPowSplit]
        ring
      _ < (3 / 8) * T ^ (-u) := hMul
      _ = (3 / 4) * (T ^ (-u) / 2) := by ring
  change (N + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) <
    ((3 / 4) * (T ^ (-u) / 2)) / (Nat.clog 2 A : ℝ)
  rw [lt_div_iff₀ hClogPos]
  calc
    (N + 1 : ℝ) ^ (-σ) * (100 * Real.sqrt t) * (Nat.clog 2 A : ℝ) ≤
        (100 * Real.sqrt 3 * T ^ (-50 * d)) * (Nat.clog 2 A : ℝ) := by
      gcongr
    _ < (3 / 4) * (T ^ (-u) / 2) := by
      simpa only [mul_comm] using hNumerator

/-- A low-scale Type-I block has enough fixed room below the square of its
length to cover the entire displaced slab `[T-T^d,2T+T^d]`. -/
theorem three_height_le_typeI_square_of_low_scale
    {σ τ₀ T : ℝ} {N : ℕ}
    (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hT : 65 ≤ T) (hN : 1 < N)
    (hTau : typeILogarithmicScale T N < 2 * τ₀ / 3) :
    3 * T ≤ (N : ℝ) ^ (2 : ℕ) := by
  have hTPos : 0 < T := by linarith
  have hNReal : (1 : ℝ) < N := by exact_mod_cast hN
  let τ := typeILogarithmicScale T N
  have hTauThreeHalf : τ < 3 / 2 := by
    have hTau0Two := endpointScaleCertificate_tau0_lt_two hσLower hσUpper hcert
    dsimp only [τ]
    nlinarith [hcert.tau0_pos]
  have hScale : (N : ℝ) ^ τ = T := by
    simpa only [τ] using rpow_typeILogarithmicScale_eq hTPos hN
  have hTUpper : T ≤ (N : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← hScale]
    exact Real.rpow_le_rpow_of_exponent_le hNReal.le hTauThreeHalf.le
  have hNNine : 9 ≤ N := by
    by_contra hnot
    have hNEight : N ≤ 8 := by omega
    have hN2 : (N : ℝ) ^ (2 : ℕ) ≤ 64 := by
      norm_num only [pow_two]
      have hNRealUpper : (N : ℝ) ≤ 8 := by exact_mod_cast hNEight
      nlinarith [show (0 : ℝ) ≤ N by positivity]
    have hPow : (N : ℝ) ^ (3 / 2 : ℝ) ≤ (N : ℝ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hNReal.le (by norm_num)
    rw [Real.rpow_two] at hPow
    nlinarith
  have hSqrtThree : 3 ≤ Real.sqrt (N : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num only [sq]
    exact_mod_cast hNNine
  have hPowThreeHalf : (N : ℝ) ^ (3 / 2 : ℝ) =
      (N : ℝ) * Real.sqrt (N : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by ring, Real.rpow_add (by positivity),
      Real.rpow_one, Real.sqrt_eq_rpow]
  have hSqrtSq := Real.sq_sqrt (show (0 : ℝ) ≤ N by positivity)
  calc
    3 * T ≤ 3 * ((N : ℝ) ^ (3 / 2 : ℝ)) := by gcongr
    _ = 3 * (N : ℝ) * Real.sqrt N := by rw [hPowThreeHalf]; ring
    _ ≤ Real.sqrt N * (N : ℝ) * Real.sqrt N := by gcongr
    _ = (N : ℝ) * (Real.sqrt N ^ 2) := by ring
    _ = (N : ℝ) * N := by rw [hSqrtSq]
    _ = (N : ℝ) ^ (2 : ℕ) := by rw [pow_two]
/-- On the basic endpoint window, the physical MHH exponent is bounded by
the final zero-density exponent after converting `T = Q^τ`. -/
theorem rpow_classicalMHHExponent_le_endpoint_target
    {σ τ₀ T : ℝ} {Q : ℕ}
    (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hT : 0 < T) (hQ : 1 < Q)
    (hτLower : 2 * τ₀ / 3 ≤ typeILogarithmicScale T Q)
    (hτUpper : typeILogarithmicScale T Q ≤ τ₀) :
    (Q : ℝ) ^ classicalMHHExponent σ (typeILogarithmicScale T Q) ≤
      T ^ (3 * (1 - σ) / τ₀) := by
  let τ := typeILogarithmicScale T Q
  have hQOne : (1 : ℝ) ≤ Q := by exact_mod_cast hQ.le
  have hEnvelope := classicalMHHExponent_le_corollary1110Envelope_of_certificate
    hσUpper hcert (τ := τ)
  have hTargetExp := hcert.subdivision_window τ hτLower hτUpper
  have hExponent : classicalMHHExponent σ τ ≤
      (3 * (1 - σ) / τ₀) * τ := by
    calc
      classicalMHHExponent σ τ ≤ corollary1110Envelope σ τ₀ τ := hEnvelope
      _ ≤ (3 - 3 * σ) * τ / τ₀ := hTargetExp
      _ = (3 * (1 - σ) / τ₀) * τ := by
        field_simp [hcert.tau0_pos.ne']
  have hPower := Real.rpow_le_rpow_of_exponent_le hQOne hExponent
  calc
    (Q : ℝ) ^ classicalMHHExponent σ τ ≤
        (Q : ℝ) ^ ((3 * (1 - σ) / τ₀) * τ) := hPower
    _ = ((Q : ℝ) ^ τ) ^ (3 * (1 - σ) / τ₀) := by
      rw [mul_comm, Real.rpow_mul (by positivity)]
    _ = T ^ (3 * (1 - σ) / τ₀) := by
      rw [rpow_typeILogarithmicScale_eq hT hQ]

lemma rpow_div_rpow_nat_eq (q σ a : ℝ) (n : ℕ) (hq : 0 < q) :
    q ^ a / (q ^ σ) ^ n = q ^ (a - n * σ) := by
  rw [div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_mul hq.le,
    ← Real.rpow_neg hq.le, ← Real.rpow_add hq]
  congr 1
  ring

/-- The three finite MHH terms, at the ideal normalized threshold `Q^σ`,
are exactly controlled by twice the maximum exponent recorded in
`classicalMHHExponent`. -/
theorem ideal_mhh_terms_le_classicalMHHExponent
    {σ T : ℝ} {Q : ℕ} (hT : 0 < T) (hQ : 1 < Q) :
    (Q : ℝ) ^ 2 / ((Q : ℝ) ^ σ) ^ 2 +
        T * min ((Q : ℝ) / ((Q : ℝ) ^ σ) ^ 2)
          ((Q : ℝ) ^ 4 / ((Q : ℝ) ^ σ) ^ 6) ≤
      2 * (Q : ℝ) ^ classicalMHHExponent σ (typeILogarithmicScale T Q) := by
  let q : ℝ := Q
  let τ := typeILogarithmicScale T Q
  have hq : 0 < q := by dsimp [q]; positivity
  have hqOne : 1 ≤ q := by dsimp [q]; exact_mod_cast hQ.le
  have hTq : q ^ τ = T := by
    simpa [q, τ] using rpow_typeILogarithmicScale_eq hT hQ
  have hFirst : q ^ (2 : ℕ) / (q ^ σ) ^ 2 = q ^ (2 - 2 * σ) := by
    rw [← Real.rpow_two]
    simpa using rpow_div_rpow_nat_eq q σ 2 2 hq
  have hSecond : T * (q / (q ^ σ) ^ 2) = q ^ (τ + 1 - 2 * σ) := by
    have hQuot : q / (q ^ σ) ^ 2 = q ^ (1 - 2 * σ) := by
      simpa only [Real.rpow_one] using rpow_div_rpow_nat_eq q σ 1 2 hq
    rw [← hTq, hQuot, ← Real.rpow_add hq]
    congr 1
    all_goals ring
  have hSixth : T * (q ^ (4 : ℕ) / (q ^ σ) ^ 6) =
      q ^ (τ + 4 - 6 * σ) := by
    have hQuot : q ^ (4 : ℕ) / (q ^ σ) ^ 6 = q ^ (4 - 6 * σ) := by
      rw [← Real.rpow_natCast]
      simpa using rpow_div_rpow_nat_eq q σ 4 6 hq
    rw [← hTq, hQuot, ← Real.rpow_add hq]
    congr 1
    all_goals ring
  have hMin : T * min (q / (q ^ σ) ^ 2) (q ^ (4 : ℕ) / (q ^ σ) ^ 6) =
      q ^ min (τ + 1 - 2 * σ) (τ + 4 - 6 * σ) := by
    rw [mul_min_of_nonneg _ _ hT.le, hSecond, hSixth]
    rcases le_total (τ + 1 - 2 * σ) (τ + 4 - 6 * σ) with h | h
    · rw [min_eq_left h, min_eq_left]
      exact Real.rpow_le_rpow_of_exponent_le hqOne h
    · rw [min_eq_right h, min_eq_right]
      exact Real.rpow_le_rpow_of_exponent_le hqOne h
  have hFirstMax : q ^ (2 - 2 * σ) ≤ q ^ classicalMHHExponent σ τ :=
    Real.rpow_le_rpow_of_exponent_le hqOne (by
      rw [classicalMHHExponent]
      exact le_max_left _ _)
  have hMinMax : q ^ min (τ + 1 - 2 * σ) (τ + 4 - 6 * σ) ≤
      q ^ classicalMHHExponent σ τ :=
    Real.rpow_le_rpow_of_exponent_le hqOne (by
      rw [classicalMHHExponent]
      exact le_max_right _ _)
  change q ^ (2 : ℕ) / (q ^ σ) ^ 2 +
      T * min (q / (q ^ σ) ^ 2) (q ^ (4 : ℕ) / (q ^ σ) ^ 6) ≤ _
  rw [hFirst, hMin]
  nlinarith

/-- A positive normalization loss `P` in the threshold costs its `n`-th
power after inversion. -/
theorem inverse_normalized_threshold_nat
    (q P V σ : ℝ) (n : ℕ) (hq : 0 < q) (hP : 0 < P)
    (hV : q ^ σ / P ≤ V) :
    V ^ (-(n : ℝ)) ≤ P ^ n * q ^ (-(n : ℝ) * σ) := by
  have hLower : 0 < q ^ σ / P := by positivity
  calc
    V ^ (-(n : ℝ)) ≤ (q ^ σ / P) ^ (-(n : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos hLower hV (neg_nonpos.mpr (Nat.cast_nonneg n))
    _ = P ^ n * q ^ (-(n : ℝ) * σ) := by
      rw [Real.div_rpow (Real.rpow_nonneg hq.le _) hP.le,
        Real.rpow_neg (Real.rpow_nonneg hq.le _) (n : ℝ),
        Real.rpow_neg hP.le (n : ℝ)]
      have hqpow : q ^ (-(n : ℝ) * σ) = ((q ^ σ) ^ n)⁻¹ := by
        rw [show -(n : ℝ) * σ = -(σ * n) by ring,
          Real.rpow_neg hq.le, Real.rpow_mul hq.le,
          Real.rpow_natCast]
      rw [hqpow]
      simp only [Real.rpow_natCast]
      field_simp [hP.ne', (Real.rpow_pos_of_pos hq σ).ne']

/-- Replacing the ideal threshold `q^σ` by `q^σ / P`, with `P ≥ 1`,
costs at most `P^6` in the complete second/sixth-power MHH expression. -/
theorem mhh_terms_le_loss_sixth
    (q T V P σ : ℝ) (hq : 0 < q) (hT : 0 ≤ T)
    (hP : 1 ≤ P) (hV : q ^ σ / P ≤ V) :
    q ^ (2 : ℕ) / V ^ 2 +
        T * min (q / V ^ 2) (q ^ (4 : ℕ) / V ^ 6) ≤
      P ^ (6 : ℕ) *
        (q ^ (2 : ℕ) / (q ^ σ) ^ 2 +
          T * min (q / (q ^ σ) ^ 2) (q ^ (4 : ℕ) / (q ^ σ) ^ 6)) := by
  have hPpos : 0 < P := zero_lt_one.trans_le hP
  have hVpos : 0 < V := (div_pos (Real.rpow_pos_of_pos hq _) hPpos).trans_le hV
  have hInv2 := inverse_normalized_threshold_nat q P V σ 2 hq hPpos hV
  have hInv6 := inverse_normalized_threshold_nat q P V σ 6 hq hPpos hV
  norm_num at hInv2 hInv6
  have hQInv2 : q ^ (-2 * σ) = ((q ^ σ) ^ (2 : ℕ))⁻¹ := by
    rw [show -2 * σ = -(σ * 2) by ring, Real.rpow_neg hq.le,
      Real.rpow_mul hq.le]
    norm_num [Real.rpow_natCast]
  have hQInv6 : q ^ (-6 * σ) = ((q ^ σ) ^ (6 : ℕ))⁻¹ := by
    rw [show -6 * σ = -(σ * 6) by ring, Real.rpow_neg hq.le,
      Real.rpow_mul hq.le]
    norm_num [Real.rpow_natCast]
  have hNeg2 : -(2 * σ) = -2 * σ := by ring
  have hNeg6 : -(6 * σ) = -6 * σ := by ring
  rw [hNeg2, hQInv2] at hInv2
  rw [hNeg6, hQInv6] at hInv6
  have hP2P6 : P ^ (2 : ℕ) ≤ P ^ (6 : ℕ) := by
    exact pow_le_pow_right₀ hP (by omega)
  have hFirst : q ^ (2 : ℕ) / V ^ 2 ≤
      P ^ (6 : ℕ) * (q ^ (2 : ℕ) / (q ^ σ) ^ 2) := by
    calc
      q ^ (2 : ℕ) / V ^ 2 = q ^ (2 : ℕ) * (V ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
        rfl
      _ ≤ q ^ (2 : ℕ) * (P ^ (2 : ℕ) * ((q ^ σ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hInv2 (by positivity)
      _ = P ^ (2 : ℕ) * (q ^ (2 : ℕ) / (q ^ σ) ^ 2) := by ring
      _ ≤ P ^ (6 : ℕ) * (q ^ (2 : ℕ) / (q ^ σ) ^ 2) := by
        exact mul_le_mul_of_nonneg_right hP2P6 (by positivity)
  have hLinear : q / V ^ 2 ≤
      P ^ (6 : ℕ) * (q / (q ^ σ) ^ 2) := by
    calc
      q / V ^ 2 = q * (V ^ 2)⁻¹ := by
        rw [div_eq_mul_inv]
        rfl
      _ ≤ q * (P ^ (2 : ℕ) * ((q ^ σ) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hInv2 hq.le
      _ = P ^ (2 : ℕ) * (q / (q ^ σ) ^ 2) := by ring
      _ ≤ P ^ (6 : ℕ) * (q / (q ^ σ) ^ 2) := by
        exact mul_le_mul_of_nonneg_right hP2P6 (by positivity)
  have hSixth : q ^ (4 : ℕ) / V ^ 6 ≤
      P ^ (6 : ℕ) * (q ^ (4 : ℕ) / (q ^ σ) ^ 6) := by
    calc
      q ^ (4 : ℕ) / V ^ 6 = q ^ (4 : ℕ) * (V ^ 6)⁻¹ := by
        rw [div_eq_mul_inv]
        rfl
      _ ≤ q ^ (4 : ℕ) * (P ^ (6 : ℕ) * ((q ^ σ) ^ 6)⁻¹) :=
        mul_le_mul_of_nonneg_left hInv6 (by positivity)
      _ = P ^ (6 : ℕ) * (q ^ (4 : ℕ) / (q ^ σ) ^ 6) := by ring
  have hMin : min (q / V ^ 2) (q ^ (4 : ℕ) / V ^ 6) ≤
      P ^ (6 : ℕ) * min (q / (q ^ σ) ^ 2) (q ^ (4 : ℕ) / (q ^ σ) ^ 6) := by
    rw [mul_min_of_nonneg _ _ (by positivity : 0 ≤ P ^ (6 : ℕ))]
    exact min_le_min hLinear hSixth
  calc
    q ^ (2 : ℕ) / V ^ 2 + T * min (q / V ^ 2) (q ^ (4 : ℕ) / V ^ 6)
        ≤ P ^ (6 : ℕ) * (q ^ (2 : ℕ) / (q ^ σ) ^ 2) +
          T * (P ^ (6 : ℕ) *
            min (q / (q ^ σ) ^ 2) (q ^ (4 : ℕ) / (q ^ σ) ^ 6)) := by gcongr
    _ = P ^ (6 : ℕ) *
        (q ^ (2 : ℕ) / (q ^ σ) ^ 2 +
          T * min (q / (q ^ σ) ^ 2) (q ^ (4 : ℕ) / (q ^ σ) ^ 6)) := by ring

/-- The exact finite MHH expression at any basic-window scale, including a
positive normalization loss, is bounded by the endpoint target times the
sixth power of that loss. -/
theorem mhh_terms_le_two_loss_endpoint_target
    {σ τ₀ T V P : ℝ} {Q : ℕ}
    (hσUpper : σ < 1) (hcert : EndpointScaleCertificate σ τ₀)
    (hT : 0 < T) (hQ : 1 < Q) (hP : 1 ≤ P)
    (hV : (Q : ℝ) ^ σ / P ≤ V)
    (hτLower : 2 * τ₀ / 3 ≤ typeILogarithmicScale T Q)
    (hτUpper : typeILogarithmicScale T Q ≤ τ₀) :
    (Q : ℝ) ^ 2 / V ^ 2 +
        T * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6) ≤
      2 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀) := by
  have hLoss := mhh_terms_le_loss_sixth (Q : ℝ) T V P σ
    (by positivity) hT.le hP hV
  have hIdeal := ideal_mhh_terms_le_classicalMHHExponent (σ := σ) hT hQ
  have hEndpoint := rpow_classicalMHHExponent_le_endpoint_target
    hσUpper hcert hT hQ hτLower hτUpper
  calc
    (Q : ℝ) ^ 2 / V ^ 2 +
          T * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6)
        ≤ P ^ (6 : ℕ) *
          ((Q : ℝ) ^ 2 / ((Q : ℝ) ^ σ) ^ 2 +
            T * min ((Q : ℝ) / ((Q : ℝ) ^ σ) ^ 2)
              ((Q : ℝ) ^ 4 / ((Q : ℝ) ^ σ) ^ 6)) := hLoss
    _ ≤ P ^ (6 : ℕ) *
          (2 * (Q : ℝ) ^ classicalMHHExponent σ
            (typeILogarithmicScale T Q)) := by gcongr
    _ ≤ P ^ (6 : ℕ) * (2 * T ^ (3 * (1 - σ) / τ₀)) := by gcongr
    _ = 2 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀) := by ring

/-- The exact analytic-multiplicity factor emitted by the dichotomy costs
only `T^(δ+2η)`.  The two copies of `η` absorb the dyadic `clog` and the
unit-height Jensen multiplicity cap separately. -/
theorem eventually_dichotomy_multiplicity_factor_bound
    (δ η : ℝ) (hδ : 0 ≤ δ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
          ((2 * ⌈T ^ δ⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) ≤
        C * T ^ (δ + 2 * η) := by
  let cLog : ℝ := 1 + (Real.log 6 + 1 / η) / Real.log 2
  let cMult : ℝ :=
    (Real.log (500 / 3 : ℝ) + 3 / η) / Real.log (35 / 32 : ℝ) + 1
  let C : ℝ := 20 * cLog * cMult
  have hlogTwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogRatio : 0 < Real.log (35 / 32 : ℝ) := Real.log_pos (by norm_num)
  have hlogSix : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
  have hlogConst : 0 ≤ Real.log (500 / 3 : ℝ) := Real.log_nonneg (by norm_num)
  have hcLog : 0 < cLog := by dsimp [cLog]; positivity
  have hcMult : 0 < cMult := by dsimp [cMult]; positivity
  refine ⟨C, by dsimp [C]; positivity, 8, le_rfl, ?_⟩
  intro T hT
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hTηOne : 1 ≤ T ^ η := Real.one_le_rpow hTone hη.le
  have hTδOne : 1 ≤ T ^ δ := Real.one_le_rpow hTone hδ
  have hlogT : Real.log T ≤ T ^ η / η :=
    Real.log_le_rpow_div hTpos.le hη
  have hClogRaw := sharp_cutoff_clog_le_log_majorant T hT
  have hClog : (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) ≤ cLog * T ^ η := by
    calc
      (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) ≤
          1 + (Real.log 6 + Real.log T) / Real.log 2 := hClogRaw
      _ ≤ cLog * T ^ η := by
        dsimp [cLog]
        rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
        have hInvLog : 0 ≤ (Real.log 2)⁻¹ := inv_nonneg.mpr hlogTwo.le
        have hInvEta : 0 ≤ η⁻¹ := inv_nonneg.mpr hη.le
        have hLogScaled : Real.log T * (Real.log 2)⁻¹ ≤
            (T ^ η / η) * (Real.log 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hlogT hInvLog
        have hConstScaled : Real.log 6 * (Real.log 2)⁻¹ ≤
            (Real.log 6 * (Real.log 2)⁻¹) * T ^ η := by
          calc
            Real.log 6 * (Real.log 2)⁻¹ =
                (Real.log 6 * (Real.log 2)⁻¹) * 1 := by ring
            _ ≤ (Real.log 6 * (Real.log 2)⁻¹) * T ^ η := by
              gcongr
        have hOneScaled : 1 ≤ T ^ η := hTηOne
        calc
          1 + (Real.log 6 + Real.log T) * (Real.log 2)⁻¹
              ≤ T ^ η +
                (Real.log 6 * (Real.log 2)⁻¹) * T ^ η +
                (T ^ η / η) * (Real.log 2)⁻¹ := by linarith
          _ = (1 + (Real.log 6 + 1 * η⁻¹) * (Real.log 2)⁻¹) * T ^ η := by
            field_simp [hη.ne']
            ring
  have hMultRaw := localMultiplicityCap_lt_log_majorant T hT
  have hMult : (classicalLocalMultiplicityCap T : ℝ) ≤ cMult * T ^ η := by
    apply hMultRaw.le.trans
    dsimp [cMult]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have hInvRatio : 0 ≤ (Real.log (35 / 32 : ℝ))⁻¹ := inv_nonneg.mpr hlogRatio.le
    have hLogScaled : 3 * Real.log T * (Real.log (35 / 32 : ℝ))⁻¹ ≤
        3 * (T ^ η / η) * (Real.log (35 / 32 : ℝ))⁻¹ := by gcongr
    have hConstScaled : Real.log (500 / 3 : ℝ) *
        (Real.log (35 / 32 : ℝ))⁻¹ ≤
        (Real.log (500 / 3 : ℝ) * (Real.log (35 / 32 : ℝ))⁻¹) * T ^ η := by
      calc
        Real.log (500 / 3 : ℝ) * (Real.log (35 / 32 : ℝ))⁻¹ =
            (Real.log (500 / 3 : ℝ) *
              (Real.log (35 / 32 : ℝ))⁻¹) * 1 := by ring
        _ ≤ (Real.log (500 / 3 : ℝ) *
              (Real.log (35 / 32 : ℝ))⁻¹) * T ^ η := by
          gcongr
    calc
      (Real.log (500 / 3 : ℝ) + 3 * Real.log T) *
            (Real.log (35 / 32 : ℝ))⁻¹ + 1
          ≤ (Real.log (500 / 3 : ℝ) * (Real.log (35 / 32 : ℝ))⁻¹) * T ^ η +
            3 * (T ^ η / η) * (Real.log (35 / 32 : ℝ))⁻¹ + T ^ η := by
        linarith
      _ = ((Real.log (500 / 3 : ℝ) + 3 / η) *
            (Real.log (35 / 32 : ℝ))⁻¹ + 1) * T ^ η := by
        field_simp [hη.ne']
  have hCeilRaw := natCast_ceil_rpow_lt_add_one T δ hTpos.le
  have hCeil : 2 * (⌈T ^ δ⌉₊ : ℝ) + 1 ≤ 5 * T ^ δ := by
    nlinarith
  push_cast
  calc
    4 * (Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ : ℝ) *
          ((2 * (⌈T ^ δ⌉₊ : ℝ) + 1) * (classicalLocalMultiplicityCap T : ℝ))
        ≤ 4 * (cLog * T ^ η) * ((5 * T ^ δ) * (cMult * T ^ η)) := by
      gcongr
    _ = C * T ^ (δ + 2 * η) := by
      dsimp [C]
      calc
        4 * (cLog * T ^ η) * (5 * T ^ δ * (cMult * T ^ η)) =
            20 * cLog * cMult * (T ^ η * T ^ δ * T ^ η) := by ring
        _ = 20 * cLog * cMult * T ^ (δ + 2 * η) := by
          rw [← Real.rpow_add hTpos, ← Real.rpow_add hTpos]
          congr 2
          ring

/-- A positive real power is eventually so large that taking its natural
floor loses at most a factor two.  This is the exact floor bridge needed for
the physical Type-II cutoff `X = floor (T^(delta2/2))`. -/
theorem eventually_half_rpow_le_natFloor
    (a : ℝ) (ha : 0 < a) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      T ^ a / 2 ≤ (⌊T ^ a⌋₊ : ℝ) ∧ (⌊T ^ a⌋₊ : ℝ) ≤ T ^ a := by
  have hTendsto : Tendsto (fun T : ℝ => T ^ a) atTop atTop :=
    tendsto_rpow_atTop ha
  have hEventually : ∀ᶠ T : ℝ in atTop, 2 ≤ T ^ a :=
    (tendsto_atTop.1 hTendsto) 2
  rw [eventually_atTop] at hEventually
  obtain ⟨T₁, hT₁⟩ := hEventually
  refine ⟨max 1 T₁, le_max_left _ _, ?_⟩
  intro T hT
  have hTone : 1 ≤ T := (le_max_left _ _).trans hT
  have hpowTwo : 2 ≤ T ^ a := hT₁ T ((le_max_right _ _).trans hT)
  have hpowNonneg : 0 ≤ T ^ a := (Real.rpow_pos_of_pos (by linarith) _).le
  have hFloorUpper : (⌊T ^ a⌋₊ : ℝ) ≤ T ^ a := Nat.floor_le hpowNonneg
  have hFloorLowerStrict : T ^ a < (⌊T ^ a⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (T ^ a)
  constructor
  · linarith
  · exact hFloorUpper

/-- The dyadic Type-II block returned by the detector lies between its base
cutoff `X` and the product `X*Y`.  The strict upper bound is the exact
`Nat.clog` bridge, rather than a real-log approximation. -/
theorem typeII_dyadic_scale_between
    {X Y r : ℕ} (hX : 0 < X) (hr : r ∈ Finset.range (Nat.clog 2 Y)) :
    X ≤ 2 ^ r * X ∧ 2 ^ r * X < Y * X := by
  have hrClog : r < Nat.clog 2 Y := Finset.mem_range.mp hr
  have hPow : 2 ^ r < Y := Nat.pow_lt_of_lt_clog hrClog
  constructor
  · exact Nat.le_mul_of_pos_left X (pow_pos (by omega) r)
  · nlinarith

/-- Logarithmic-scale inequalities are exactly equivalent to the
corresponding physical power inequalities. -/
theorem typeILogarithmicScale_mem_iff
    {T : ℝ} {Q : ℕ} (hT : 0 < T) (hQ : 1 < Q) (a b : ℝ) :
    a ≤ typeILogarithmicScale T Q ∧ typeILogarithmicScale T Q ≤ b ↔
      (Q : ℝ) ^ a ≤ T ∧ T ≤ (Q : ℝ) ^ b := by
  constructor
  · intro h
    exact ⟨(Real.le_logb_iff_rpow_le (by exact_mod_cast hQ) hT).mp h.1,
      (Real.logb_le_iff_le_rpow (by exact_mod_cast hQ) hT).mp h.2⟩
  · intro h
    exact ⟨(Real.le_logb_iff_rpow_le (by exact_mod_cast hQ) hT).mpr h.1,
      (Real.logb_le_iff_le_rpow (by exact_mod_cast hQ) hT).mpr h.2⟩

/-- One explicit epsilon budget shared by the detector displacement,
multiplicity, coefficient normalization, powering and harmonic losses. -/
noncomputable def classicalEndpointLossParameter
    (σ τ₀ ε : ℝ) : ℝ :=
  min (ε / 1000)
    (min (ε * τ₀ / 1000)
      (min ((σ - 1 / 2) / 1000)
        (min (σ / 8) (1 / (1000 * (1 + τ₀))))))

theorem classicalEndpointLossParameter_spec
    {σ τ₀ ε : ℝ} (hσ : 1 / 2 < σ) (hτ₀ : 0 < τ₀) (hε : 0 < ε) :
    let d := classicalEndpointLossParameter σ τ₀ ε
    0 < d ∧ d ≤ ε / 1000 ∧ d ≤ ε * τ₀ / 1000 ∧
      d ≤ (σ - 1 / 2) / 1000 ∧ d ≤ σ / 8 ∧
      d ≤ 1 / (1000 * (1 + τ₀)) ∧
      d / 2 ≤ d ∧ d ≤ 1 ∧ d < σ := by
  dsimp [classicalEndpointLossParameter]
  have hDen : 0 < 1000 * (1 + τ₀) := by positivity
  have hLast : 0 < 1 / (1000 * (1 + τ₀)) := by positivity
  have hdPos : 0 < min (ε / 1000)
      (min (ε * τ₀ / 1000)
        (min ((σ - 1 / 2) / 1000)
          (min (σ / 8) (1 / (1000 * (1 + τ₀)))))) := by positivity
  have hdEps : min (ε / 1000)
      (min (ε * τ₀ / 1000)
        (min ((σ - 1 / 2) / 1000)
          (min (σ / 8) (1 / (1000 * (1 + τ₀)))))) ≤ ε / 1000 :=
    min_le_left _ _
  have hdEpsTau : min (ε / 1000)
      (min (ε * τ₀ / 1000)
        (min ((σ - 1 / 2) / 1000)
          (min (σ / 8) (1 / (1000 * (1 + τ₀)))))) ≤
        ε * τ₀ / 1000 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hdHalfGap : min (ε / 1000)
      (min (ε * τ₀ / 1000)
        (min ((σ - 1 / 2) / 1000)
          (min (σ / 8) (1 / (1000 * (1 + τ₀)))))) ≤
        (σ - 1 / 2) / 1000 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))
  have hdSigma : min (ε / 1000)
      (min (ε * τ₀ / 1000)
        (min ((σ - 1 / 2) / 1000)
          (min (σ / 8) (1 / (1000 * (1 + τ₀)))))) ≤ σ / 8 :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hdTau : min (ε / 1000)
      (min (ε * τ₀ / 1000)
        (min ((σ - 1 / 2) / 1000)
          (min (σ / 8) (1 / (1000 * (1 + τ₀)))))) ≤
        1 / (1000 * (1 + τ₀)) :=
    (min_le_right _ _).trans
      ((min_le_right _ _).trans
        ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨hdPos, hdEps, hdEpsTau, hdHalfGap, hdSigma, hdTau,
    by linarith, ?_, by linarith⟩
  have hTauOne : 1 / (1000 * (1 + τ₀)) < 1 := by
    rw [div_lt_one hDen]
    nlinarith
  exact hdTau.trans hTauOne.le

/-- Every Type-II witness produced with the common loss parameter has a
physical scale between `T^(d/2)/2` and `T^(3d/2)`.  All natural floors and
the dyadic `Nat.clog` index are discharged here. -/
theorem eventually_typeII_physical_scale_bounds
    (d : ℝ) (hd : 0 < d) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ (T : ℝ) (r : ℕ), T₀ ≤ T →
      r ∈ Finset.range (Nat.clog 2 ⌊T ^ d⌋₊) →
      let X := ⌊T ^ (d / 2)⌋₊
      let N := 2 ^ r * X
      0 < N ∧ T ^ (d / 2) / 2 ≤ (N : ℝ) ∧
        (N : ℝ) ≤ T ^ (3 * d / 2) := by
  obtain ⟨Tfloor, hTfloor, hFloor⟩ :=
    eventually_half_rpow_le_natFloor (d / 2) (by linarith)
  refine ⟨Tfloor, hTfloor, ?_⟩
  intro T r hT hr
  let X := ⌊T ^ (d / 2)⌋₊
  let Y := ⌊T ^ d⌋₊
  let N := 2 ^ r * X
  have hTOne : 1 ≤ T := hTfloor.trans hT
  have hTPos : 0 < T := zero_lt_one.trans_le hTOne
  have hFloorData := hFloor T hT
  have hXRealPos : (0 : ℝ) < X := by
    dsimp only [X]
    exact lt_of_lt_of_le (by positivity : 0 < T ^ (d / 2) / 2) hFloorData.1
  have hX : 0 < X := by exact_mod_cast hXRealPos
  have hBetween := typeII_dyadic_scale_between hX (by simpa [Y] using hr)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hLowerNat : X ≤ N := by simpa only [N] using hBetween.1
  have hUpperNat : N ≤ Y * X := by
    dsimp only [N]
    exact hBetween.2.le
  have hYUpper : (Y : ℝ) ≤ T ^ d := by
    dsimp only [Y]
    exact Nat.floor_le (Real.rpow_nonneg hTPos.le _)
  have hXUpper : (X : ℝ) ≤ T ^ (d / 2) := by
    dsimp only [X]
    exact hFloorData.2
  dsimp only [N]
  refine ⟨by simpa only [N] using hN, ?_, ?_⟩
  · exact hFloorData.1.trans (by exact_mod_cast hLowerNat)
  · calc
      ((2 ^ r * X : ℕ) : ℝ) ≤ ((Y * X : ℕ) : ℝ) := by
        exact_mod_cast hUpperNat
      _ = (Y : ℝ) * (X : ℝ) := by push_cast; ring
      _ ≤ T ^ d * T ^ (d / 2) := mul_le_mul hYUpper hXUpper
        (Nat.cast_nonneg X) (Real.rpow_nonneg hTPos.le _)
      _ = T ^ (3 * d / 2) := by
        rw [← Real.rpow_add hTPos]
        congr 1
        ring

/-- Two-parameter version of the physical Type-II scale bound.  The
detector's lower cutoff exponent `dX` is allowed to be much smaller than the
Type-I cutoff exponent `dY`; this separation is essential when a power as
large as `O(dX⁻¹)` is selected later. -/
theorem eventually_typeII_physical_scale_bounds_two
    (dX dY : ℝ) (hdX : 0 < dX) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧ ∀ (T : ℝ) (r : ℕ), T₀ ≤ T →
      r ∈ Finset.range (Nat.clog 2 ⌊T ^ dY⌋₊) →
      let X := ⌊T ^ (dX / 2)⌋₊
      let N := 2 ^ r * X
      0 < N ∧ T ^ (dX / 2) / 2 ≤ (N : ℝ) ∧
        (N : ℝ) ≤ T ^ (dY + dX / 2) := by
  obtain ⟨Tfloor, hTfloor, hFloor⟩ :=
    eventually_half_rpow_le_natFloor (dX / 2) (by linarith)
  refine ⟨Tfloor, hTfloor, ?_⟩
  intro T r hT hr
  let X := ⌊T ^ (dX / 2)⌋₊
  let Y := ⌊T ^ dY⌋₊
  let N := 2 ^ r * X
  have hTOne : 1 ≤ T := hTfloor.trans hT
  have hTPos : 0 < T := zero_lt_one.trans_le hTOne
  have hFloorData := hFloor T hT
  have hXRealPos : (0 : ℝ) < X := by
    dsimp only [X]
    exact lt_of_lt_of_le (by positivity : 0 < T ^ (dX / 2) / 2) hFloorData.1
  have hX : 0 < X := by exact_mod_cast hXRealPos
  have hBetween := typeII_dyadic_scale_between hX (by simpa only [Y] using hr)
  have hN : 0 < N := by dsimp only [N]; positivity
  have hLowerNat : X ≤ N := by simpa only [N] using hBetween.1
  have hUpperNat : N ≤ Y * X := by
    dsimp only [N]
    exact hBetween.2.le
  have hYUpper : (Y : ℝ) ≤ T ^ dY := by
    dsimp only [Y]
    exact Nat.floor_le (Real.rpow_nonneg hTPos.le _)
  have hXUpper : (X : ℝ) ≤ T ^ (dX / 2) := by
    dsimp only [X]
    exact hFloorData.2
  dsimp only [N]
  refine ⟨by simpa only [N] using hN, ?_, ?_⟩
  · exact hFloorData.1.trans (by exact_mod_cast hLowerNat)
  · calc
      ((2 ^ r * X : ℕ) : ℝ) ≤ ((Y * X : ℕ) : ℝ) := by exact_mod_cast hUpperNat
      _ = (Y : ℝ) * (X : ℝ) := by push_cast; ring
      _ ≤ T ^ dY * T ^ (dX / 2) := mul_le_mul hYUpper hXUpper
        (Nat.cast_nonneg X) (Real.rpow_nonneg hTPos.le _)
      _ = T ^ (dY + dX / 2) := by rw [← Real.rpow_add hTPos]

/-- With separate detector exponents, a Type-II witness has logarithmic
scale in `[1/(2 dY), 4/dX]` once `dX ≤ 2 dY`.  The deliberately relaxed
constants absorb the two natural-floor losses without coupling `dX` and
`dY`. -/
theorem eventually_typeII_logarithmic_scale_bounds_two
    (dX dY : ℝ) (hdX : 0 < dX) (hdY : 0 < dY)
    (hXY : dX ≤ 2 * dY) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ (T : ℝ) (r : ℕ), T₀ ≤ T →
      r ∈ Finset.range (Nat.clog 2 ⌊T ^ dY⌋₊) →
      let X := ⌊T ^ (dX / 2)⌋₊
      let N := 2 ^ r * X
      1 < N ∧ 1 / (2 * dY) ≤ typeILogarithmicScale T N ∧
        typeILogarithmicScale T N ≤ 4 / dX := by
  obtain ⟨Tscale, hTscale, hScale⟩ :=
    eventually_typeII_physical_scale_bounds_two dX dY hdX
  let T₀ := max Tscale (max 2 ((2 : ℝ) ^ (4 / dX)))
  refine ⟨T₀, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro T r hT hr
  have hTscale' : Tscale ≤ T := (le_max_left _ _).trans hT
  have hTRest : max 2 ((2 : ℝ) ^ (4 / dX)) ≤ T :=
    (le_max_right _ _).trans hT
  have hTTwo : 2 ≤ T := (le_max_left _ _).trans hTRest
  have hTConst : (2 : ℝ) ^ (4 / dX) ≤ T :=
    (le_max_right _ _).trans hTRest
  have hTPos : 0 < T := by linarith
  let X := ⌊T ^ (dX / 2)⌋₊
  let N := 2 ^ r * X
  have hs := hScale T r hTscale' hr
  dsimp only at hs
  have hNPos : (0 : ℝ) < N := by exact_mod_cast hs.1
  have hNOne : 1 < N := by
    have hRaised := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _)
      hTConst (by positivity : 0 ≤ dX / 2)
    have hConstPower : ((2 : ℝ) ^ (4 / dX)) ^ (dX / 2) = 4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hExp : 4 / dX * (dX / 2) = 2 := by field_simp [hdX.ne']; ring
      rw [hExp]
      norm_num
    rw [hConstPower] at hRaised
    have hNRealTwo : (2 : ℝ) ≤ N := by nlinarith [hs.2.1]
    exact_mod_cast hNRealTwo
  have hBaseOne : (1 : ℝ) < N := by exact_mod_cast hNOne
  have hSumLe : dY + dX / 2 ≤ 2 * dY := by linarith
  have hLowerExp : (N : ℝ) ^ (1 / (2 * dY)) ≤ T := by
    calc
      (N : ℝ) ^ (1 / (2 * dY)) ≤
          (T ^ (dY + dX / 2)) ^ (1 / (2 * dY)) :=
        Real.rpow_le_rpow hNPos.le hs.2.2 (by positivity)
      _ = T ^ ((dY + dX / 2) / (2 * dY)) := by
        rw [← Real.rpow_mul hTPos.le]
        congr 1
        field_simp [hdY.ne']
      _ ≤ T := by
        calc
          T ^ ((dY + dX / 2) / (2 * dY)) ≤ T ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ T)
              ((div_le_one (by positivity : 0 < 2 * dY)).2 hSumLe)
          _ = T := Real.rpow_one T
  have hLowerTau : 1 / (2 * dY) ≤ typeILogarithmicScale T N :=
    (Real.le_logb_iff_rpow_le hBaseOne hTPos).mpr hLowerExp
  have hUpperPhysical : T ≤ (N : ℝ) ^ (4 / dX) := by
    have hRaised := Real.rpow_le_rpow (by positivity) hs.2.1
      (by positivity : 0 ≤ 4 / dX)
    have hFloorPower : (T ^ (dX / 2) / 2) ^ (4 / dX) =
        T ^ 2 / (2 : ℝ) ^ (4 / dX) := by
      have hExp : dX / 2 * (4 / dX) = 2 := by field_simp [hdX.ne']; ring
      rw [Real.div_rpow (Real.rpow_nonneg hTPos.le _)
          (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_mul hTPos.le, hExp]
      simp only [Real.rpow_two]
    rw [hFloorPower] at hRaised
    have hConstPos : 0 < (2 : ℝ) ^ (4 / dX) := by positivity
    have hTDiv : T ≤ T ^ 2 / (2 : ℝ) ^ (4 / dX) := by
      rw [le_div_iff₀ hConstPos]
      nlinarith
    exact hTDiv.trans hRaised
  have hUpperTau : typeILogarithmicScale T N ≤ 4 / dX :=
    (Real.logb_le_iff_le_rpow hBaseOne hTPos).mpr hUpperPhysical
  exact ⟨hNOne, hLowerTau, hUpperTau⟩

/-- The physical Type-II logarithmic scale is uniformly trapped in a
compact interval.  The lower endpoint comes from the exact `clog` upper
bound; the upper endpoint records the factor-two loss from the floor. -/
theorem eventually_typeII_logarithmic_scale_bounds
    (d : ℝ) (hd : 0 < d) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ (T : ℝ) (r : ℕ), T₀ ≤ T →
      r ∈ Finset.range (Nat.clog 2 ⌊T ^ d⌋₊) →
      let X := ⌊T ^ (d / 2)⌋₊
      let N := 2 ^ r * X
      1 < N ∧ 2 / (3 * d) ≤ typeILogarithmicScale T N ∧
        typeILogarithmicScale T N ≤ 4 / d := by
  obtain ⟨Tscale, hTscale, hScale⟩ :=
    eventually_typeII_physical_scale_bounds d hd
  let T₀ := max Tscale (max 2 ((2 : ℝ) ^ (4 / d)))
  refine ⟨T₀, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro T r hT hr
  have hTscale' : Tscale ≤ T := (le_max_left _ _).trans hT
  have hTTwo : 2 ≤ T :=
    (le_max_left (2 : ℝ) ((2 : ℝ) ^ (4 / d))).trans
      ((le_max_right Tscale _).trans hT)
  have hTConst : (2 : ℝ) ^ (4 / d) ≤ T :=
    (le_max_right (2 : ℝ) ((2 : ℝ) ^ (4 / d))).trans
      ((le_max_right Tscale _).trans hT)
  have hTPos : 0 < T := by linarith
  let X := ⌊T ^ (d / 2)⌋₊
  let N := 2 ^ r * X
  have hs := hScale T r hTscale' hr
  dsimp only at hs
  have hNPos : (0 : ℝ) < N := by exact_mod_cast hs.1
  have hNOne : 1 < N := by
    have hExpNonneg : 0 ≤ d / 2 := by positivity
    have hRaised := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _)
      hTConst hExpNonneg
    have hConstPower : ((2 : ℝ) ^ (4 / d)) ^ (d / 2) = 4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hExp : 4 / d * (d / 2) = 2 := by
        field_simp [hd.ne']
        ring
      rw [hExp]
      norm_num
    rw [hConstPower] at hRaised
    have hNRealTwo : (2 : ℝ) ≤ N := by nlinarith [hs.2.1]
    exact_mod_cast hNRealTwo
  have hBaseOne : (1 : ℝ) < N := by exact_mod_cast hNOne
  have hLowerExp : (N : ℝ) ^ (2 / (3 * d)) ≤ T := by
    have hExpPos : 0 < 2 / (3 * d) := by positivity
    calc
      (N : ℝ) ^ (2 / (3 * d)) ≤
          (T ^ (3 * d / 2)) ^ (2 / (3 * d)) :=
        (Real.rpow_le_rpow hNPos.le hs.2.2 hExpPos.le)
      _ = T := by
        rw [← Real.rpow_mul hTPos.le]
        have hExp : 3 * d / 2 * (2 / (3 * d)) = 1 := by
          field_simp [hd.ne']
        rw [hExp, Real.rpow_one]
  have hLowerTau : 2 / (3 * d) ≤ typeILogarithmicScale T N :=
    (Real.le_logb_iff_rpow_le hBaseOne hTPos).mpr hLowerExp
  have hUpperPhysical : T ≤ (N : ℝ) ^ (4 / d) := by
    have hExpPos : 0 < 4 / d := by positivity
    have hRaised := Real.rpow_le_rpow (by positivity) hs.2.1 hExpPos.le
    have hTwoPos : (0 : ℝ) < 2 := by norm_num
    have hFloorPower :
        (T ^ (d / 2) / 2) ^ (4 / d) = T ^ 2 / (2 : ℝ) ^ (4 / d) := by
      have hExp : d / 2 * (4 / d) = 2 := by
        field_simp [hd.ne']
        ring
      rw [Real.div_rpow (Real.rpow_nonneg hTPos.le _) hTwoPos.le,
        ← Real.rpow_mul hTPos.le, hExp]
      simp only [Real.rpow_two]
    rw [hFloorPower] at hRaised
    have hConstPos : 0 < (2 : ℝ) ^ (4 / d) := Real.rpow_pos_of_pos hTwoPos _
    have hTDiv : T ≤ T ^ 2 / (2 : ℝ) ^ (4 / d) := by
      rw [le_div_iff₀ hConstPos]
      nlinarith
    exact hTDiv.trans hRaised
  have hUpperTau : typeILogarithmicScale T N ≤ 4 / d :=
    (Real.logb_le_iff_le_rpow hBaseOne hTPos).mpr hUpperPhysical
  exact ⟨hNOne, hLowerTau, hUpperTau⟩

/-- The lower cutoff of every actual Type-I dichotomy block gives a uniform
upper bound for its physical logarithmic scale.  This is the precise
floor/cast bridge used when a power is selected uniformly over all Type-I
witnesses. -/
theorem eventually_typeI_logarithmic_scale_upper
    (d : ℝ) (hd : 0 < d) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ (T : ℝ) (r : ℕ), T₀ ≤ T →
      let Y := ⌊T ^ d⌋₊
      let N := 2 ^ r * Y
      1 < N ∧ typeILogarithmicScale T N ≤ 2 / d := by
  obtain ⟨Tfloor, hTfloor, hFloor⟩ := eventually_half_rpow_le_natFloor d hd
  let T₀ := max Tfloor (max 2 ((2 : ℝ) ^ (2 / d)))
  refine ⟨T₀, (le_max_left _ _).trans (le_max_right _ _), ?_⟩
  intro T r hT
  dsimp only
  have hTFloor : Tfloor ≤ T := (le_max_left _ _).trans hT
  have hTRest : max 2 ((2 : ℝ) ^ (2 / d)) ≤ T :=
    (le_max_right _ _).trans hT
  have hTTwo : 2 ≤ T := (le_max_left _ _).trans hTRest
  have hTConst : (2 : ℝ) ^ (2 / d) ≤ T :=
    (le_max_right _ _).trans hTRest
  have hTPos : 0 < T := by linarith
  let Y := ⌊T ^ d⌋₊
  let N := 2 ^ r * Y
  have hYLower : T ^ d / 2 ≤ (Y : ℝ) := by
    simpa only [Y] using (hFloor T hTFloor).1
  have hYTwo : (2 : ℝ) ≤ Y := by
    have hExpNonneg : 0 ≤ d := hd.le
    have hRaised := Real.rpow_le_rpow (Real.rpow_nonneg (by norm_num) _)
      hTConst hExpNonneg
    have hConstPower : ((2 : ℝ) ^ (2 / d)) ^ d = 4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      have hExp : 2 / d * d = 2 := by field_simp [hd.ne']
      rw [hExp]
      norm_num
    rw [hConstPower] at hRaised
    nlinarith
  have hYOne : 1 < Y := by exact_mod_cast hYTwo
  have hNOne : 1 < N := by
    dsimp only [N]
    exact lt_of_lt_of_le hYOne
      (Nat.le_mul_of_pos_left Y (pow_pos (by omega) r))
  have hNLower : T ^ d / 2 ≤ (N : ℝ) := by
    calc
      T ^ d / 2 ≤ (Y : ℝ) := hYLower
      _ ≤ (N : ℝ) := by
        exact_mod_cast Nat.le_mul_of_pos_left Y (pow_pos (by omega) r)
  have hUpperPhysical : T ≤ (N : ℝ) ^ (2 / d) := by
    have hExpPos : 0 < 2 / d := by positivity
    have hRaised := Real.rpow_le_rpow (by positivity) hNLower hExpPos.le
    have hFloorPower : (T ^ d / 2) ^ (2 / d) =
        T ^ 2 / (2 : ℝ) ^ (2 / d) := by
      have hExp : d * (2 / d) = 2 := by field_simp [hd.ne']
      rw [Real.div_rpow (Real.rpow_nonneg hTPos.le _) (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_mul hTPos.le, hExp]
      simp only [Real.rpow_two]
    rw [hFloorPower] at hRaised
    have hConstPos : 0 < (2 : ℝ) ^ (2 / d) := by positivity
    have hTDiv : T ≤ T ^ 2 / (2 : ℝ) ^ (2 / d) := by
      rw [le_div_iff₀ hConstPos]
      nlinarith
    exact hTDiv.trans hRaised
  have hTauUpper : typeILogarithmicScale T N ≤ 2 / d :=
    (Real.logb_le_iff_le_rpow (by exact_mod_cast hNOne) hTPos).mpr hUpperPhysical
  exact ⟨hNOne, hTauUpper⟩

/-- The power selected for a compact physical scale range is itself
uniformly bounded.  This is what permits one coefficient and harmonic
epsilon budget to work for every Type-II witness as `T` varies. -/
theorem exists_bounded_positive_power_scale_reduction
    {τ₀ τ U : ℝ} (hτ₀ : 0 < τ₀)
    (hτLower : 4 * τ₀ / 3 ≤ τ) (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧ k ≤ ⌈3 * U / (2 * τ₀)⌉₊ ∧
      2 * τ₀ / 3 ≤ τ / k ∧ τ / k ≤ τ₀ := by
  obtain ⟨k, hk, hkLower, hkUpper⟩ :=
    exists_positive_power_scale_reduction hτ₀ hτLower
  have hkRealPos : (0 : ℝ) < k := by exact_mod_cast hk
  have hBoundReal : (k : ℝ) ≤ 3 * U / (2 * τ₀) := by
    have hScaled := (le_div_iff₀ hkRealPos).mp hkLower
    apply (le_div_iff₀ (by positivity : 0 < 2 * τ₀)).2
    nlinarith
  have hkCeil : k ≤ ⌈3 * U / (2 * τ₀)⌉₊ := by
    have hReal : (k : ℝ) ≤ (⌈3 * U / (2 * τ₀)⌉₊ : ℝ) :=
      hBoundReal.trans (Nat.le_ceil _)
    exact_mod_cast hReal
  exact ⟨k, hk, hkCeil, hkLower, hkUpper⟩

/-- Passing from a block to its exact natural power divides its physical
logarithmic scale by that power.  This identity is kept separate from the
later dyadic extraction, whose extra factor is handled quantitatively. -/
theorem typeILogarithmicScale_nat_pow
    {T : ℝ} {N k : ℕ} (hN : 1 < N) (hk : 0 < k) :
    typeILogarithmicScale T (N ^ k) =
      typeILogarithmicScale T N / k := by
  unfold typeILogarithmicScale Real.logb
  rw [Nat.cast_pow, Real.log_pow]
  have hLogN : Real.log (N : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hN))
  have hkReal : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp [hLogN, hkReal]

/-- Increasing a block length decreases its logarithmic height scale. -/
theorem typeILogarithmicScale_antitone_length
    {T : ℝ} {M Q : ℕ} (hT : 1 ≤ T) (hM : 1 < M) (hMQ : M ≤ Q) :
    typeILogarithmicScale T Q ≤ typeILogarithmicScale T M := by
  have hQ : 1 < Q := hM.trans_le hMQ
  have hLogT : 0 ≤ Real.log T := Real.log_nonneg hT
  have hLogM : 0 < Real.log (M : ℝ) := Real.log_pos (by exact_mod_cast hM)
  have hLogQ : 0 < Real.log (Q : ℝ) := Real.log_pos (by exact_mod_cast hQ)
  unfold typeILogarithmicScale Real.logb
  rw [div_le_div_iff₀ hLogQ hLogM]
  have hLogMQ : Real.log (M : ℝ) ≤ Real.log (Q : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hMQ)
  exact mul_le_mul_of_nonneg_left hLogMQ hLogT

/-- The finite MHH exponent is monotone in the logarithmic height scale. -/
theorem classicalMHHExponent_mono_tau
    { σ τ τ' : ℝ} (hτ : τ ≤ τ') :
    classicalMHHExponent σ τ ≤ classicalMHHExponent σ τ' := by
  unfold classicalMHHExponent
  gcongr

/-- In the endpoint range and below height exponent two, the MHH exponent
is nonnegative and at most two. -/
theorem classicalMHHExponent_mem_zero_two
    { σ τ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hτ : τ ≤ 2) :
    0 ≤ classicalMHHExponent σ τ ∧ classicalMHHExponent σ τ ≤ 2 := by
  constructor
  · exact (by nlinarith : 0 ≤ 2 - 2 * σ).trans
      (le_max_left (2 - 2 * σ) (min (τ + 1 - 2 * σ) (τ + 4 - 6 * σ)))
  · rw [classicalMHHExponent, max_le_iff]
    constructor
    · linarith
    · exact (min_le_left _ _).trans (by linarith)

/-- The dyadic factor introduced by exact powered extraction costs only a
uniform factor depending on the a priori power bound.  The endpoint power
is evaluated at the undilated block `N^k`, so no artificial margin in the
human scale window is required. -/
theorem dyadic_power_mhh_le_endpoint_with_factor
    { σ τ₀ T : ℝ} {N k r B : ℕ}
    (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀)
    (hT : 1 ≤ T) (hN : 1 < N) (hk : 0 < k) (hkB : k ≤ B)
    (hr : r < k)
    (hτLower : 2 * τ₀ / 3 ≤ typeILogarithmicScale T N / k)
    (hτUpper : typeILogarithmicScale T N / k ≤ τ₀) :
    let Q := 2 ^ r * N ^ k
    (Q : ℝ) ^ classicalMHHExponent σ (typeILogarithmicScale T Q) ≤
      ((2 : ℝ) ^ B) ^ (2 : ℕ) * T ^ (3 * (1 - σ) / τ₀) := by
  dsimp only
  let M : ℕ := N ^ k
  let Q : ℕ := 2 ^ r * M
  have hM : 1 < M := by
    dsimp only [M]
    exact one_lt_pow₀ hN hk.ne'
  have hMPos : 0 < M := by omega
  have hQ : 1 < Q := by
    dsimp only [Q]
    exact hM.trans_le (Nat.le_mul_of_pos_left M (pow_pos (by omega) r))
  have hMQ : M ≤ Q := by
    dsimp only [Q]
    exact Nat.le_mul_of_pos_left M (pow_pos (by omega) r)
  have hScaleM : typeILogarithmicScale T M = typeILogarithmicScale T N / k := by
    dsimp only [M]
    exact typeILogarithmicScale_nat_pow hN hk
  have hScaleQM : typeILogarithmicScale T Q ≤ typeILogarithmicScale T M :=
    typeILogarithmicScale_antitone_length hT hM hMQ
  have hExpMono : classicalMHHExponent σ (typeILogarithmicScale T Q) ≤
      classicalMHHExponent σ (typeILogarithmicScale T M) :=
    classicalMHHExponent_mono_tau hScaleQM
  have hTauMTwo : typeILogarithmicScale T M ≤ 2 := by
    rw [hScaleM]
    exact hτUpper.trans
      (endpointScaleCertificate_tau0_lt_two hσLower hσUpper hcert).le
  have hExpQ := classicalMHHExponent_mem_zero_two hσLower hσUpper
    (hScaleQM.trans hTauMTwo)
  have hExpM := classicalMHHExponent_mem_zero_two hσLower hσUpper hTauMTwo
  have hEndpointM := rpow_classicalMHHExponent_le_endpoint_target
    hσUpper hcert (lt_of_lt_of_le (by norm_num) hT) hM
    (by simpa only [hScaleM] using hτLower)
    (by simpa only [hScaleM] using hτUpper)
  have hrB : r ≤ B := le_trans (Nat.le_of_lt hr) hkB
  have hQFactor : (Q : ℝ) ≤ (2 : ℝ) ^ B * M := by
    dsimp only [Q]
    have hPow : 2 ^ r ≤ 2 ^ B :=
      pow_le_pow_right₀ (by omega : (1 : ℕ) ≤ 2) hrB
    exact_mod_cast Nat.mul_le_mul_right M hPow
  have hFOne : (1 : ℝ) ≤ (2 : ℝ) ^ B := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  calc
    (Q : ℝ) ^ classicalMHHExponent σ (typeILogarithmicScale T Q) ≤
        (Q : ℝ) ^ classicalMHHExponent σ (typeILogarithmicScale T M) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hQ.le) hExpMono
    _ ≤ ((2 : ℝ) ^ B * M) ^
        classicalMHHExponent σ (typeILogarithmicScale T M) := by
      exact Real.rpow_le_rpow (by positivity) hQFactor hExpM.1
    _ = ((2 : ℝ) ^ B) ^
          classicalMHHExponent σ (typeILogarithmicScale T M) *
        (M : ℝ) ^ classicalMHHExponent σ (typeILogarithmicScale T M) := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ ((2 : ℝ) ^ B) ^ (2 : ℕ) *
        (M : ℝ) ^ classicalMHHExponent σ (typeILogarithmicScale T M) := by
      gcongr
      calc
        ((2 : ℝ) ^ B) ^
            classicalMHHExponent σ (typeILogarithmicScale T M) ≤
            ((2 : ℝ) ^ B) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hFOne hExpM.2
        _ = ((2 : ℝ) ^ B) ^ (2 : ℕ) := Real.rpow_natCast _ 2
    _ ≤ ((2 : ℝ) ^ B) ^ (2 : ℕ) *
        T ^ (3 * (1 - σ) / τ₀) := by gcongr

/-- At sufficiently large height, the bounded dyadic factor in powered
extraction can lower the selected logarithmic scale by at most the fixed
gap from `2τ₀/3` to `τ₀/2`.  This is the exact finite substitute for
silently identifying `2^r N^k` with `N^k`. -/
theorem eventually_dyadic_power_scale_lower_half
    {τ₀ U : ℝ} (hτ₀ : 0 < τ₀) (hU : 0 < U) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ (T : ℝ) (N k r : ℕ), T₀ ≤ T →
      1 < N → 0 < k → r < k →
      let τ := typeILogarithmicScale T N
      τ ≤ U → 2 * τ₀ / 3 ≤ τ / k →
      τ₀ / 2 ≤ typeILogarithmicScale T (2 ^ r * N ^ k) := by
  let T₀ : ℝ := max 2 ((8 : ℝ) ^ U)
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T N k r hT hN hk hr
  dsimp only
  let τ := typeILogarithmicScale T N
  intro hτU hτLower
  let Q : ℕ := 2 ^ r * N ^ k
  have hTTwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hNReal : (1 : ℝ) < N := by exact_mod_cast hN
  have hNPos : 0 < N := by omega
  have hQ : 1 < Q := by
    dsimp only [Q]
    have hNk : 1 < N ^ k := one_lt_pow₀ hN hk.ne'
    exact hNk.trans_le (Nat.le_mul_of_pos_left _ (pow_pos (by omega) r))
  have hNτ : (N : ℝ) ^ τ = T := by
    simpa only [τ] using rpow_typeILogarithmicScale_eq hTPos hN
  have hTConst : (8 : ℝ) ^ U ≤ T := (le_max_right (2 : ℝ) _).trans hT
  have hTUpperN : T ≤ (N : ℝ) ^ U := by
    rw [← hNτ]
    exact Real.rpow_le_rpow_of_exponent_le hNReal.le hτU
  have hLargeN : (8 : ℝ) ≤ N := by
    by_contra hnot
    have hNlt : (N : ℝ) < 8 := lt_of_not_ge hnot
    have hStrict := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ N)
      hNlt hU
    linarith
  have hPowBase : (2 ^ (3 * r) : ℕ) ≤ N ^ k := by
    have hPowR : 2 ^ (3 * r) = 8 ^ r := by
      rw [show 8 = 2 ^ 3 by norm_num, ← pow_mul]
    rw [hPowR]
    have hLargeNat : 8 ≤ N := by exact_mod_cast hLargeN
    exact (Nat.pow_le_pow_left hLargeNat r).trans
      (Nat.pow_le_pow_right (by omega) hr.le)
  have hSlack : (N : ℝ) ^ ((k : ℝ) * τ₀ / 6) ≥
      (2 : ℝ) ^ ((r : ℝ) * (τ₀ / 2)) := by
    have hExp : 0 ≤ τ₀ / 6 := by positivity
    have hRaised :
        (((2 ^ (3 * r) : ℕ) : ℝ) ^ (τ₀ / 6)) ≤
          (((N ^ k : ℕ) : ℝ) ^ (τ₀ / 6)) :=
      Real.rpow_le_rpow (by positivity)
        (by exact_mod_cast hPowBase) hExp
    calc
      (2 : ℝ) ^ ((r : ℝ) * (τ₀ / 2)) =
          (2 : ℝ) ^ (((3 * r : ℕ) : ℝ) * (τ₀ / 6)) := by
            congr 1
            push_cast
            ring
      _ = ((2 ^ (3 * r) : ℕ) : ℝ) ^ (τ₀ / 6) := by
        rw [Nat.cast_pow, ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity)]
        norm_num
      _ ≤ ((N ^ k : ℕ) : ℝ) ^ (τ₀ / 6) := hRaised
      _ = (N : ℝ) ^ ((k : ℝ) * τ₀ / 6) := by
        rw [Nat.cast_pow, ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity)]
        congr 1
        ring
  have hLowerPhysical : (Q : ℝ) ^ (τ₀ / 2) ≤ T := by
    rw [show (Q : ℝ) = (2 ^ r : ℕ) * (N ^ k : ℕ) by
      simp only [Q, Nat.cast_mul]]
    rw [Real.mul_rpow (by positivity) (by positivity)]
    have hNTarget : (N : ℝ) ^ ((k : ℝ) * (τ₀ / 2)) ≤
        T / (N : ℝ) ^ ((k : ℝ) * τ₀ / 6) := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _), ← hNτ]
      rw [← Real.rpow_add (by positivity)]
      apply Real.rpow_le_rpow_of_exponent_le hNReal.le
      have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
      have := (le_div_iff₀ hkReal).mp hτLower
      nlinarith
    have hTwo : ((2 ^ r : ℕ) : ℝ) ^ (τ₀ / 2) ≤
        (N : ℝ) ^ ((k : ℝ) * τ₀ / 6) := by
      calc
        ((2 ^ r : ℕ) : ℝ) ^ (τ₀ / 2) =
            (2 : ℝ) ^ ((r : ℝ) * (τ₀ / 2)) := by
          rw [Nat.cast_pow, ← Real.rpow_natCast,
            ← Real.rpow_mul (by positivity)]
          norm_num
        _ ≤ (N : ℝ) ^ ((k : ℝ) * τ₀ / 6) := hSlack
    calc
      ((2 ^ r : ℕ) : ℝ) ^ (τ₀ / 2) *
          ((N ^ k : ℕ) : ℝ) ^ (τ₀ / 2) ≤
          (N : ℝ) ^ ((k : ℝ) * τ₀ / 6) *
            (T / (N : ℝ) ^ ((k : ℝ) * τ₀ / 6)) := by
        gcongr
        calc
          ((N ^ k : ℕ) : ℝ) ^ (τ₀ / 2) =
              (N : ℝ) ^ ((k : ℝ) * (τ₀ / 2)) := by
            rw [Nat.cast_pow, ← Real.rpow_natCast,
              ← Real.rpow_mul (by positivity)]
          _ ≤ T / (N : ℝ) ^ ((k : ℝ) * τ₀ / 6) := hNTarget
      _ = T := by
        field_simp [(Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < N)
          ((k : ℝ) * τ₀ / 6)).ne']
  exact (Real.le_logb_iff_rpow_le (by exact_mod_cast hQ) hTPos).mpr
    (by simpa only [Q] using hLowerPhysical)

/-- A margin-preserving version of the power choice.  Choosing the ceiling
of `τ/τ₀` gives a scale in `[4τ₀/5,τ₀]` once `τ ≥ 4τ₀`; the spare margin is
used below to absorb the dyadic factor introduced by powered extraction. -/
theorem exists_bounded_power_scale_reduction_with_margin
    {τ₀ τ U : ℝ} (hτ₀ : 0 < τ₀)
    (hτLower : 4 * τ₀ ≤ τ) (hτUpper : τ ≤ U) :
    ∃ k : ℕ, 0 < k ∧ k ≤ ⌈U / τ₀⌉₊ ∧
      4 * τ₀ / 5 ≤ τ / k ∧ τ / k ≤ τ₀ := by
  let k : ℕ := ⌈τ / τ₀⌉₊
  have hτPos : 0 < τ := lt_of_lt_of_le (by positivity : 0 < 4 * τ₀) hτLower
  have hRatioFour : 4 ≤ τ / τ₀ := by
    rw [le_div_iff₀ hτ₀]
    exact hτLower
  have hkFour : 4 ≤ k := by
    dsimp only [k]
    exact_mod_cast (hRatioFour.trans (Nat.le_ceil _))
  have hk : 0 < k := by omega
  have hkLower : τ / τ₀ ≤ (k : ℝ) := Nat.le_ceil _
  have hkUpperStrict : (k : ℝ) < τ / τ₀ + 1 := by
    dsimp only [k]
    exact Nat.ceil_lt_add_one (by positivity : 0 ≤ τ / τ₀)
  have hUpper : τ / k ≤ τ₀ := by
    rw [div_le_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k)]
    have := (div_le_iff₀ hτ₀).mp hkLower
    nlinarith
  have hLower : 4 * τ₀ / 5 ≤ τ / k := by
    rw [le_div_iff₀ (by exact_mod_cast hk : (0 : ℝ) < k)]
    have hCeilCost : (k : ℝ) ≤ 5 * τ / (4 * τ₀) := by
      have hOne : 1 ≤ τ / (4 * τ₀) := by
        rw [le_div_iff₀ (by positivity : 0 < 4 * τ₀)]
        simpa using hτLower
      calc
        (k : ℝ) ≤ τ / τ₀ + 1 := hkUpperStrict.le
        _ ≤ τ / τ₀ + τ / (4 * τ₀) := by linarith
        _ = 5 * τ / (4 * τ₀) := by field_simp [hτ₀.ne']; ring
    have hCeilCost' : (k : ℝ) * (4 * τ₀) ≤ 5 * τ := by
      exact (le_div_iff₀ (by positivity : 0 < 4 * τ₀)).mp hCeilCost
    nlinarith
  have hkBound : k ≤ ⌈U / τ₀⌉₊ := by
    have hRatio : τ / τ₀ ≤ U / τ₀ := by gcongr
    exact Nat.ceil_mono hRatio
  exact ⟨k, hk, hkBound, hLower, hUpper⟩

/-- Uniform dyadic-factor absorption for every bounded positive power. -/
theorem eventually_dyadic_power_scale_in_endpoint_window
    {τ₀ U : ℝ} (hτ₀ : 0 < τ₀) (hU : 0 < U) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ (T : ℝ) (N k r : ℕ), T₀ ≤ T →
      1 < N → 0 < k → k ≤ ⌈U / τ₀⌉₊ → r < k →
      let τ := typeILogarithmicScale T N
      τ ≤ U → 4 * τ₀ / 5 ≤ τ / k → τ / k ≤ τ₀ →
      let Q := 2 ^ r * N ^ k
      1 < Q ∧ 2 * τ₀ / 3 ≤ typeILogarithmicScale T Q ∧
        typeILogarithmicScale T Q ≤ τ₀ := by
  let B : ℕ := ⌈U / τ₀⌉₊
  let T₀ : ℝ := max 2 ((128 : ℝ) ^ U)
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T N k r hT hN hk hkB hr
  dsimp only
  let τ := typeILogarithmicScale T N
  intro hτU hτLower hτUpper
  let Q := 2 ^ r * N ^ k
  have hTTwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hNReal : (1 : ℝ) < N := by exact_mod_cast hN
  have hNPos : 0 < N := by omega
  have hQ : 1 < Q := by
    dsimp only [Q]
    have : 1 < N ^ k := one_lt_pow₀ hN hk.ne'
    have hle : N ^ k ≤ 2 ^ r * N ^ k :=
      Nat.le_mul_of_pos_left (N ^ k) (pow_pos (by omega) r)
    omega
  have hNτ : (N : ℝ) ^ τ = T := by
    simpa only [τ] using rpow_typeILogarithmicScale_eq hTPos hN
  have hUpperPhysical : T ≤ (Q : ℝ) ^ τ₀ := by
    have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
    have hPowN : T ≤ (N : ℝ) ^ ((k : ℝ) * τ₀) := by
      rw [← hNτ]
      apply Real.rpow_le_rpow_of_exponent_le hNReal.le
      have := (div_le_iff₀ hkReal).mp hτUpper
      linarith
    calc
      T ≤ (N : ℝ) ^ ((k : ℝ) * τ₀) := hPowN
      _ = ((N ^ k : ℕ) : ℝ) ^ τ₀ := by
        push_cast
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      _ ≤ (Q : ℝ) ^ τ₀ := by
        apply Real.rpow_le_rpow
        · positivity
        · exact_mod_cast Nat.le_mul_of_pos_left (N ^ k) (pow_pos (by omega) r)
        · exact hτ₀.le
  have hTConst : (128 : ℝ) ^ U ≤ T :=
    (le_max_right (2 : ℝ) _).trans hT
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hTUpperN : T ≤ (N : ℝ) ^ U := by
    rw [← hNτ]
    exact Real.rpow_le_rpow_of_exponent_le hNReal.le hτU
  have hLargeN : (128 : ℝ) ≤ N := by
    by_contra hnot
    have hNlt : (N : ℝ) < 128 := lt_of_not_ge hnot
    have hStrict := Real.rpow_lt_rpow (by positivity : (0 : ℝ) ≤ N)
      hNlt hU
    linarith
  have hPowBase : (2 ^ (7 * r) : ℕ) ≤ N ^ k := by
    have hPowR : 2 ^ (7 * r) = 128 ^ r := by
      rw [show 128 = 2 ^ 7 by norm_num, ← pow_mul]
    rw [hPowR]
    have hLargeNat : 128 ≤ N := by exact_mod_cast hLargeN
    exact (Nat.pow_le_pow_left hLargeNat r).trans
      (Nat.pow_le_pow_right (by omega) hr.le)
  have hSlack : (N : ℝ) ^ ((k : ℝ) * τ₀ / 10) ≥
      (2 : ℝ) ^ ((r : ℝ) * (2 * τ₀ / 3)) := by
    have hExp : 0 ≤ τ₀ / 10 := by positivity
    have hRaised :
        (((2 ^ (7 * r) : ℕ) : ℝ) ^ (τ₀ / 10)) ≤
          (((N ^ k : ℕ) : ℝ) ^ (τ₀ / 10)) :=
      Real.rpow_le_rpow
        (by positivity : (0 : ℝ) ≤ ((2 ^ (7 * r) : ℕ) : ℝ))
        (by exact_mod_cast hPowBase :
          ((2 ^ (7 * r) : ℕ) : ℝ) ≤ ((N ^ k : ℕ) : ℝ))
      hExp
    have hExponent : (r : ℝ) * (2 * τ₀ / 3) ≤
        (7 * r : ℕ) * (τ₀ / 10) := by
      have hrNonneg : (0 : ℝ) ≤ r := by positivity
      push_cast
      nlinarith
    calc
      (2 : ℝ) ^ ((r : ℝ) * (2 * τ₀ / 3)) =
          (2 : ℝ) ^ ((r : ℝ) * (2 * τ₀ / 3)) := rfl
      _ ≤ (2 : ℝ) ^ (((7 * r : ℕ) : ℝ) * (τ₀ / 10)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hExponent
      _ = ((2 ^ (7 * r) : ℕ) : ℝ) ^ (τ₀ / 10) := by
        rw [Nat.cast_pow, ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity)]
        congr 1
      _ ≤ ((N ^ k : ℕ) : ℝ) ^ (τ₀ / 10) := hRaised
      _ = (N : ℝ) ^ ((k : ℝ) * τ₀ / 10) := by
        rw [Nat.cast_pow, ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity)]
        congr 1
        ring
  have hLowerPhysical : (Q : ℝ) ^ (2 * τ₀ / 3) ≤ T := by
    have hBase : (0 : ℝ) ≤ (2 ^ r : ℕ) := by positivity
    rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
    have hNTarget : (N : ℝ) ^ ((k : ℝ) * (2 * τ₀ / 3)) ≤
        T / (N : ℝ) ^ ((k : ℝ) * τ₀ / 10) := by
      rw [le_div_iff₀ (Real.rpow_pos_of_pos (by positivity) _), ← hNτ]
      rw [← Real.rpow_add (by positivity)]
      apply Real.rpow_le_rpow_of_exponent_le hNReal.le
      have := (le_div_iff₀ hkReal).mp hτLower
      nlinarith
    have hTwo : ((2 ^ r : ℕ) : ℝ) ^ (2 * τ₀ / 3) ≤
        (N : ℝ) ^ ((k : ℝ) * τ₀ / 10) := by
      calc
        ((2 ^ r : ℕ) : ℝ) ^ (2 * τ₀ / 3) =
            (2 : ℝ) ^ ((r : ℝ) * (2 * τ₀ / 3)) := by
          norm_num only [Nat.cast_pow, Nat.cast_ofNat]
          rw [← Real.rpow_natCast,
            ← Real.rpow_mul (by positivity)]
        _ ≤ (N : ℝ) ^ ((k : ℝ) * τ₀ / 10) := hSlack
    calc
      ((2 ^ r : ℕ) : ℝ) ^ (2 * τ₀ / 3) *
          ((N ^ k : ℕ) : ℝ) ^ (2 * τ₀ / 3) ≤
          (N : ℝ) ^ ((k : ℝ) * τ₀ / 10) *
            (T / (N : ℝ) ^ ((k : ℝ) * τ₀ / 10)) := by
        gcongr
        calc
          ((N ^ k : ℕ) : ℝ) ^ (2 * τ₀ / 3) =
              (N : ℝ) ^ ((k : ℝ) * (2 * τ₀ / 3)) := by
            rw [Nat.cast_pow, ← Real.rpow_natCast,
              ← Real.rpow_mul (by positivity)]
          _ ≤ T / (N : ℝ) ^ ((k : ℝ) * τ₀ / 10) := hNTarget
      _ = T := by
        field_simp [(Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < N)
          ((k : ℝ) * τ₀ / 10)).ne']
  have hTau := (typeILogarithmicScale_mem_iff hTPos hQ
    (2 * τ₀ / 3) τ₀).2 ⟨hLowerPhysical, hUpperPhysical⟩
  exact ⟨hQ, hTau.1, hTau.2⟩

/-- Explicit normalization loss for an actual powered Type-II block. -/
noncomputable def typeIIPoweredThresholdLoss
    (C L D η σ : ℝ) (N k : ℕ) : ℝ :=
  max 1
    (((((2 ^ k * N ^ k : ℕ) : ℝ) ^ σ) * D ^ k *
        (C * (((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) * k) / L ^ k)

/-- The actual threshold emitted by powered extraction is at least
`Q^σ/P` for the explicit positive loss `P`.  This is the algebraic bridge
from the detector normalization to the endpoint MHH estimate. -/
theorem typeII_powered_threshold_lower
    {C L D η σ : ℝ} {N k r : ℕ}
    (hC : 0 < C) (hL : 0 < L) (hD : 0 < D)
    (hN : 0 < N) (hk : 0 < k) (hσ : 0 ≤ σ)
    (hr : r < k) :
    let Q := 2 ^ r * N ^ k
    let V := (((L / D) ^ k /
        (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η)) / k)
    let P := typeIIPoweredThresholdLoss C L D η σ N k
    1 ≤ P ∧ (Q : ℝ) ^ σ / P ≤ V := by
  dsimp only
  let U : ℝ := ((2 ^ k * N ^ k : ℕ) : ℝ)
  let R : ℝ :=
    ((U ^ σ) * D ^ k * (C * U ^ η) * k) / L ^ k
  have hU : 0 < U := by
    dsimp only [U]
    positivity
  have hR : 0 < R := by
    dsimp only [R]
    positivity
  have hP : 1 ≤ max 1 R := le_max_left _ _
  have hQUpperNat : 2 ^ r * N ^ k ≤ 2 ^ k * N ^ k := by
    exact Nat.mul_le_mul_right (N ^ k)
      (Nat.pow_le_pow_right (by omega : 1 ≤ 2) hr.le)
  have hQUpper : (((2 ^ r * N ^ k : ℕ) : ℝ) ^ σ) ≤ U ^ σ := by
    apply Real.rpow_le_rpow
    · positivity
    · dsimp only [U]
      exact_mod_cast hQUpperNat
    · exact hσ
  have hRatio : (((2 ^ r * N ^ k : ℕ) : ℝ) ^ σ) / max 1 R ≤
      (((2 ^ r * N ^ k : ℕ) : ℝ) ^ σ) / R := by
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
      hR (le_max_right _ _)
  refine ⟨hP, hRatio.trans ((div_le_div_iff_of_pos_right hR).2 hQUpper |>.trans ?_)⟩
  dsimp only [R, U]
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hUpperPow : 0 < ((2 ^ k * N ^ k : ℕ) : ℝ) ^ σ := by positivity
  have hEtaPow : 0 < ((2 ^ k * N ^ k : ℕ) : ℝ) ^ η := by positivity
  rw [show (L / D) ^ k = L ^ k / D ^ k by rw [div_pow]]
  field_simp [hL.ne', hD.ne', hC.ne', hkReal.ne', hUpperPow.ne', hEtaPow.ne']
  norm_num

/-- Exact cancellation of the source `N^σ` normalization against the
`N^{-σ}` detector-coefficient normalization. -/
theorem typeII_powered_scale_normalization_identity
    (C₀ d σ : ℝ) (N k : ℕ) (hN : 0 < N) :
    (((2 ^ k * N ^ k : ℕ) : ℝ) ^ σ) *
        (C₀ * (2 * N : ℝ) ^ d * (N : ℝ) ^ (-σ)) ^ k =
      ((2 ^ k : ℕ) : ℝ) ^ σ * C₀ ^ k *
        (2 * N : ℝ) ^ (d * k) := by
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hTwoN : (0 : ℝ) < 2 * N := by positivity
  push_cast
  rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
      (pow_nonneg hNReal.le k),
    mul_pow, mul_pow]
  have hTwoNat : (2 : ℝ) ^ k = (2 : ℝ) ^ (k : ℝ) :=
    (Real.rpow_natCast (2 : ℝ) k).symm
  have hNNat : (N : ℝ) ^ k = (N : ℝ) ^ (k : ℝ) :=
    (Real.rpow_natCast (N : ℝ) k).symm
  rw [hTwoNat, hNNat]
  change ((2 : ℝ) ^ (k : ℝ)) ^ σ *
      ((N : ℝ) ^ (k : ℝ)) ^ σ *
        (C₀ ^ k * (((2 : ℝ) * N) ^ d) ^ k *
          (((N : ℝ) ^ (-σ)) ^ k)) =
    ((2 : ℝ) ^ (k : ℝ)) ^ σ * C₀ ^ k *
      ((2 : ℝ) * N) ^ (d * (k : ℝ))
  rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2),
    ← Real.rpow_mul hNReal.le]
  have hTwoNpow : (((2 : ℝ) * N) ^ d) ^ k =
      ((2 : ℝ) * N) ^ (d * (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTwoN.le]
  have hNnegpow : ((N : ℝ) ^ (-σ)) ^ k =
      (N : ℝ) ^ ((-σ) * (k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNReal.le]
  rw [hTwoNpow, hNnegpow]
  have hCancel : (N : ℝ) ^ ((k : ℝ) * σ) *
      (N : ℝ) ^ ((-σ) * (k : ℝ)) = 1 := by
    rw [← Real.rpow_add hNReal]
    convert Real.rpow_zero (N : ℝ) using 1
    ring_nf
  calc
    (2 : ℝ) ^ ((k : ℝ) * σ) * (N : ℝ) ^ ((k : ℝ) * σ) *
          (C₀ ^ k * ((2 : ℝ) * N) ^ (d * k) *
            (N : ℝ) ^ ((-σ) * (k : ℝ))) =
        ((2 : ℝ) ^ ((k : ℝ) * σ) * C₀ ^ k *
          ((2 : ℝ) * N) ^ (d * k)) *
            ((N : ℝ) ^ ((k : ℝ) * σ) *
              (N : ℝ) ^ ((-σ) * (k : ℝ))) := by ring
    _ = (2 : ℝ) ^ ((k : ℝ) * σ) * C₀ ^ k *
        ((2 : ℝ) * N) ^ (d * k) := by
      rw [hCancel, mul_one]

theorem classicalTypeIIPowerLoss_mono_length
    {A d T : ℝ} {k Q R : ℕ} (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hT : 1 ≤ T)
    (hR : R ≤ Q) :
    classicalTypeIIPowerLoss A d T k R ≤
      classicalTypeIIPowerLoss A d T k Q := by
  dsimp only [classicalTypeIIPowerLoss]
  have hScale : (((2 : ℝ) ^ k) * R) ^ (2 * d) ≤
      (((2 : ℝ) ^ k) * Q) ^ (2 * d) := by
    apply Real.rpow_le_rpow
    · positivity
    · gcongr
    · positivity
  have hLog : 0 ≤ Real.log T := Real.log_nonneg hT
  gcongr

/-- The explicit threshold loss is bounded by a single powered-scale and
logarithmic envelope, uniformly for every `1 ≤ k ≤ B`. -/
theorem typeII_powered_threshold_loss_le_envelope
    {C₀ C e dY σ T : ℝ} {Y N k : ℕ}
    (hC₀ : 1 ≤ C₀) (hC : 1 ≤ C) (hdYOne : dY ≤ 1)
    (hσOne : σ ≤ 1) (hT : Real.exp 1 ≤ T)
    (hY : 1 < Y) (hYUpper : (Y : ℝ) ≤ T ^ dY)
    (hN : 0 < N) (hk : 0 < k) {B : ℕ} (hkB : k ≤ B) :
    let L := (9 / 16 : ℝ) / Nat.clog 2 Y
    let D := C₀ * (2 * N : ℝ) ^ e * (N : ℝ) ^ (-σ)
    let aLog := max 1
      (((16 / 9 : ℝ) * (1 + (Real.log 2)⁻¹)) / 4)
    let A := (2 : ℝ) ^ B * C₀ ^ B * C * aLog ^ B
    typeIIPoweredThresholdLoss C L D e σ N k ≤
      1 + classicalTypeIIPowerLoss A e T k (N ^ k) := by
  dsimp only
  let L : ℝ := (9 / 16 : ℝ) / Nat.clog 2 Y
  let D : ℝ := C₀ * (2 * N : ℝ) ^ e * (N : ℝ) ^ (-σ)
  let aLog : ℝ := max 1
    (((16 / 9 : ℝ) * (1 + (Real.log 2)⁻¹)) / 4)
  let A : ℝ := (2 : ℝ) ^ B * C₀ ^ B * C * aLog ^ B
  have hTOne : 1 ≤ T := by
    calc
      1 = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ T := hT
  have hTPos : 0 < T := zero_lt_one.trans_le hTOne
  have hLogOne : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) hT
  have hLogPos : 0 < Real.log T := zero_lt_one.trans_le hLogOne
  have hClogPos : 0 < Nat.clog 2 Y := Nat.clog_pos Nat.one_lt_two hY
  have hL : 0 < L := by
    dsimp only [L]
    positivity
  have hD : 0 < D := by
    dsimp only [D]
    positivity
  have hLogY : Real.log Y ≤ dY * Real.log T := by
    have hYPos : (0 : ℝ) < Y := by exact_mod_cast (Nat.zero_lt_of_lt hY)
    have hMonotone := Real.log_le_log hYPos hYUpper
    rw [Real.log_rpow hTPos] at hMonotone
    exact hMonotone
  have hClog : (Nat.clog 2 Y : ℝ) ≤
      (1 + (Real.log 2)⁻¹) * Real.log T := by
    have hRaw := natCast_clog_two_le_one_add_log Y hY.le
    have hInv : 0 ≤ (Real.log 2)⁻¹ :=
      inv_nonneg.mpr (Real.log_pos (by norm_num)).le
    rw [div_eq_mul_inv] at hRaw
    calc
      (Nat.clog 2 Y : ℝ) ≤ 1 + Real.log Y * (Real.log 2)⁻¹ := hRaw
      _ ≤ 1 + (dY * Real.log T) * (Real.log 2)⁻¹ := by gcongr
      _ ≤ Real.log T + Real.log T * (Real.log 2)⁻¹ := by
        have hdLog : dY * Real.log T ≤ Real.log T := by
          nlinarith [mul_le_mul_of_nonneg_right hdYOne hLogPos.le]
        nlinarith [mul_le_mul_of_nonneg_right hdLog hInv]
      _ = (1 + (Real.log 2)⁻¹) * Real.log T := by ring
  have haLog : 1 ≤ aLog := by exact le_max_left _ _
  have hInvL : L⁻¹ ≤ aLog * (4 * Real.log T) := by
    have hClogReal : (0 : ℝ) < Nat.clog 2 Y := by exact_mod_cast hClogPos
    have hFactor : ((16 / 9 : ℝ) * (1 + (Real.log 2)⁻¹)) / 4 ≤ aLog :=
      le_max_right _ _
    dsimp only [L]
    rw [inv_div]
    calc
      (Nat.clog 2 Y : ℝ) / (9 / 16 : ℝ) =
          (9 / 16 : ℝ)⁻¹ * (Nat.clog 2 Y : ℝ) := by ring
      _ ≤
          (16 / 9 : ℝ) * ((1 + (Real.log 2)⁻¹) * Real.log T) := by
        norm_num
        gcongr
      _ = (((16 / 9 : ℝ) * (1 + (Real.log 2)⁻¹)) / 4) *
          (4 * Real.log T) := by ring
      _ ≤ aLog * (4 * Real.log T) := by gcongr
  have hTwoPowSigma : (((2 ^ k : ℕ) : ℝ) ^ σ) ≤ (2 : ℝ) ^ B := by
    have hBase : (1 : ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by norm_num : 2 ≠ 0)))
    calc
      (((2 ^ k : ℕ) : ℝ) ^ σ) ≤ (((2 ^ k : ℕ) : ℝ) ^ (1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hBase hσOne
      _ = (2 : ℝ) ^ k := by norm_num
      _ ≤ (2 : ℝ) ^ B := pow_le_pow_right₀ (by norm_num) hkB
  have hC₀Pow : C₀ ^ k ≤ C₀ ^ B := pow_le_pow_right₀ hC₀ hkB
  have hInvLPow : L⁻¹ ^ k ≤ aLog ^ B * (4 * Real.log T) ^ k := by
    calc
      L⁻¹ ^ k ≤ (aLog * (4 * Real.log T)) ^ k :=
        pow_le_pow_left₀ (by positivity) hInvL k
      _ = aLog ^ k * (4 * Real.log T) ^ k := by rw [mul_pow]
      _ ≤ aLog ^ B * (4 * Real.log T) ^ k := by
        gcongr
  have hScaleIdentity :
      (2 * N : ℝ) ^ (e * k) *
          (((2 ^ k * N ^ k : ℕ) : ℝ) ^ e) =
        (((2 : ℝ) ^ k) * ((N ^ k : ℕ) : ℝ)) ^ (2 * e) := by
    have hTwoN : (0 : ℝ) < 2 * N := by positivity
    have hU : (0 : ℝ) < ((2 ^ k * N ^ k : ℕ) : ℝ) := by positivity
    have hEq : (2 * N : ℝ) ^ (e * (k : ℝ)) =
        (((2 ^ k * N ^ k : ℕ) : ℝ) ^ e) := by
      rw [mul_comm e, Real.rpow_mul hTwoN.le]
      congr 1
      norm_num [mul_pow]
    rw [hEq, ← Real.rpow_add hU]
    have hCast : ((2 ^ k * N ^ k : ℕ) : ℝ) =
        (2 : ℝ) ^ k * ((N ^ k : ℕ) : ℝ) := by norm_num
    rw [hCast]
    congr 1
    ring
  have hRBound :
      ((((2 ^ k * N ^ k : ℕ) : ℝ) ^ σ) * D ^ k *
          (C * (((2 ^ k * N ^ k : ℕ) : ℝ) ^ e)) * k) / L ^ k ≤
        classicalTypeIIPowerLoss A e T k (N ^ k) := by
    rw [typeII_powered_scale_normalization_identity C₀ e σ N k hN]
    rw [div_eq_mul_inv, ← inv_pow]
    dsimp only [classicalTypeIIPowerLoss, A]
    rw [show (L⁻¹) ^ k = L⁻¹ ^ k by rfl]
    calc
      ((2 ^ k : ℕ) : ℝ) ^ σ * C₀ ^ k * (2 * N : ℝ) ^ (e * k) *
            (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ e) * (k : ℝ) * L⁻¹ ^ k ≤
          (2 : ℝ) ^ B * C₀ ^ B *
            (2 * N : ℝ) ^ (e * k) *
              (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ e) *
                (k : ℝ) * (aLog ^ B * (4 * Real.log T) ^ k) := by
        gcongr
      _ = (2 : ℝ) ^ B * C₀ ^ B * C * aLog ^ B *
          (((2 : ℝ) ^ k) * ((N ^ k : ℕ) : ℝ)) ^ (2 * e) *
            (k : ℝ) * (4 * Real.log T) ^ k := by
        rw [← hScaleIdentity]
        push_cast
        ring
  apply max_le
  · have hLossNonneg : 0 ≤ classicalTypeIIPowerLoss A e T k (N ^ k) := by
      dsimp only [classicalTypeIIPowerLoss, A]
      positivity
    linarith
  · exact hRBound.trans (le_add_of_nonneg_left (by norm_num))

/-- Uniform threshold envelope for a powered actual Type-I block at the
project's sharp zeta cutoff.  The factor `T^(u*k)` is retained explicitly:
it is the `k`-fold cost of the detector threshold `T⁻u`, and is paid from the
final epsilon budget rather than hidden in a constant. -/
theorem typeI_powered_threshold_loss_le_envelope
    {C e u σ T : ℝ} {N k : ℕ}
    (hC : 1 ≤ C) (he : 0 ≤ e)
    (hσOne : σ ≤ 1) (hT : 8 ≤ T)
    (hN : 0 < N) (hk : 0 < k) {B : ℕ} (hkB : k ≤ B) :
    let A := ⌊sharpZetaCutoff T⌋₊
    let V := ((3 / 4 : ℝ) * (T ^ (-u) / 2)) / Nat.clog 2 A
    let aLog := max 1 (((8 / 3 : ℝ) * (1 + 2 / Real.log 2)) / 4)
    let E := (2 : ℝ) ^ B * C * aLog ^ B
    typeIIPoweredThresholdLoss C ((N : ℝ) ^ σ * V) 1 e σ N k ≤
      1 + T ^ (u * k) * classicalTypeIIPowerLoss E e T k (N ^ k) := by
  dsimp only
  let A := ⌊sharpZetaCutoff T⌋₊
  let V : ℝ := ((3 / 4 : ℝ) * (T ^ (-u) / 2)) / Nat.clog 2 A
  let aLog : ℝ := max 1 (((8 / 3 : ℝ) * (1 + 2 / Real.log 2)) / 4)
  let E : ℝ := (2 : ℝ) ^ B * C * aLog ^ B
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hExpT : Real.exp 1 ≤ T := by
    calc
      Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
      _ ≤ 8 := by norm_num
      _ ≤ T := hT
  have hLogOne : 1 ≤ Real.log T := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) hExpT
  have hLogPos : 0 < Real.log T := zero_lt_one.trans_le hLogOne
  have hLogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLogSixT : Real.log 6 ≤ Real.log T :=
    Real.log_le_log (by norm_num) (by linarith)
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hClogPos : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hAOne
  have hClog := sharp_cutoff_clog_le_log_majorant T hT
  have hClog' : (Nat.clog 2 A : ℝ) ≤
      (1 + 2 / Real.log 2) * Real.log T := by
    calc
      (Nat.clog 2 A : ℝ) ≤
          1 + (Real.log 6 + Real.log T) / Real.log 2 := by
            simpa only [A] using hClog
      _ ≤ (1 + 2 / Real.log 2) * Real.log T := by
        have hNumerator : Real.log 6 + Real.log T ≤ 2 * Real.log T := by
          linarith
        have hFrac : (Real.log 6 + Real.log T) / Real.log 2 ≤
            (2 * Real.log T) / Real.log 2 :=
          div_le_div_of_nonneg_right hNumerator hLogTwo.le
        calc
          1 + (Real.log 6 + Real.log T) / Real.log 2 ≤
              1 + (2 * Real.log T) / Real.log 2 := by linarith
          _ ≤ Real.log T + (2 * Real.log T) / Real.log 2 := by linarith
          _ = (1 + 2 / Real.log 2) * Real.log T := by ring
  have hV : 0 < V := by
    dsimp only [V]
    positivity
  have haLog : 1 ≤ aLog := le_max_left _ _
  have hInvV : V⁻¹ ≤ aLog * (4 * Real.log T) * T ^ u := by
    have hFactor : ((8 / 3 : ℝ) * (1 + 2 / Real.log 2)) / 4 ≤ aLog :=
      le_max_right _ _
    have hInvEq : V⁻¹ = (8 / 3 : ℝ) * (Nat.clog 2 A : ℝ) * T ^ u := by
      dsimp only [V]
      rw [Real.rpow_neg hTPos.le]
      field_simp [hV.ne', (Real.rpow_pos_of_pos hTPos u).ne']
      ring
    rw [hInvEq]
    calc
      (8 / 3 : ℝ) * (Nat.clog 2 A : ℝ) * T ^ u ≤
          (8 / 3 : ℝ) * ((1 + 2 / Real.log 2) * Real.log T) * T ^ u := by
            gcongr
      _ = (((8 / 3 : ℝ) * (1 + 2 / Real.log 2)) / 4) *
          (4 * Real.log T) * T ^ u := by ring
      _ ≤ aLog * (4 * Real.log T) * T ^ u := by gcongr
  have hInvVPow : V⁻¹ ^ k ≤
      aLog ^ B * (4 * Real.log T) ^ k * T ^ (u * k) := by
    have hTPow : (T ^ u) ^ k = T ^ (u * (k : ℝ)) := by
      calc
        (T ^ u) ^ k = (T ^ u) ^ (k : ℝ) :=
          (Real.rpow_natCast (T ^ u) k).symm
        _ = T ^ (u * (k : ℝ)) := (Real.rpow_mul hTPos.le u k).symm
    calc
      V⁻¹ ^ k ≤ (aLog * (4 * Real.log T) * T ^ u) ^ k :=
        pow_le_pow_left₀ (by positivity) hInvV k
      _ = aLog ^ k * (4 * Real.log T) ^ k * (T ^ u) ^ k := by
        simp only [mul_pow]
      _ ≤ aLog ^ B * (4 * Real.log T) ^ k * (T ^ u) ^ k := by
        gcongr
      _ = aLog ^ B * (4 * Real.log T) ^ k * T ^ (u * k) := by
        rw [hTPow]
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hCancel :
      (((2 ^ k * N ^ k : ℕ) : ℝ) ^ σ) /
          (((N : ℝ) ^ σ) ^ k) = (((2 : ℝ) ^ k) ^ σ) := by
    push_cast
    rw [Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ k)
      (pow_nonneg hNReal.le k)]
    have hNPow : (((N : ℝ) ^ k) ^ σ) = ((N : ℝ) ^ σ) ^ k := by
      calc
        (((N : ℝ) ^ k) ^ σ) = (((N : ℝ) ^ (k : ℝ)) ^ σ) := by
          rw [Real.rpow_natCast]
        _ = (N : ℝ) ^ ((k : ℝ) * σ) := (Real.rpow_mul hNReal.le k σ).symm
        _ = (N : ℝ) ^ (σ * (k : ℝ)) := by congr 1; ring
        _ = (((N : ℝ) ^ σ) ^ (k : ℝ)) := Real.rpow_mul hNReal.le σ k
        _ = ((N : ℝ) ^ σ) ^ k := Real.rpow_natCast _ _
    rw [hNPow]
    field_simp [(Real.rpow_pos_of_pos hNReal σ).ne']
  have hTwoPowSigma : (((2 : ℝ) ^ k) ^ σ) ≤ (2 : ℝ) ^ B := by
    have hBase : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
    calc
      (((2 : ℝ) ^ k) ^ σ) ≤ (((2 : ℝ) ^ k) ^ (1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hBase hσOne
      _ = (2 : ℝ) ^ k := by norm_num
      _ ≤ (2 : ℝ) ^ B := pow_le_pow_right₀ (by norm_num) hkB
  have hScale :
      (((2 ^ k * N ^ k : ℕ) : ℝ) ^ e) ≤
        ((((2 : ℝ) ^ k) * ((N ^ k : ℕ) : ℝ)) ^ (2 * e)) := by
    have hCast : ((2 ^ k * N ^ k : ℕ) : ℝ) =
        ((2 : ℝ) ^ k) * ((N ^ k : ℕ) : ℝ) := by norm_num
    rw [hCast]
    have hBaseNat : 1 ≤ 2 ^ k * N ^ k := by
      exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (pow_ne_zero _ (by omega)) (pow_ne_zero _ (Nat.ne_of_gt hN)))
    have hBaseReal : (1 : ℝ) ≤ ((2 : ℝ) ^ k) * ((N ^ k : ℕ) : ℝ) := by
      exact_mod_cast hBaseNat
    apply Real.rpow_le_rpow_of_exponent_le
      hBaseReal
    linarith
  have hRaw :
      (((((2 ^ k * N ^ k : ℕ) : ℝ) ^ σ) * (1 : ℝ) ^ k *
          (C * (((2 ^ k * N ^ k : ℕ) : ℝ) ^ e)) * k) /
            (((N : ℝ) ^ σ * V) ^ k)) ≤
        T ^ (u * k) * classicalTypeIIPowerLoss E e T k (N ^ k) := by
    rw [mul_pow, div_eq_mul_inv, mul_inv, ← inv_pow]
    have hIdentity :
        (((2 ^ k * N ^ k : ℕ) : ℝ) ^ σ) *
            (((N : ℝ) ^ σ) ^ k)⁻¹ = (((2 : ℝ) ^ k) ^ σ) := by
      rw [← div_eq_mul_inv]
      exact hCancel
    have hIdentity' :
        (((2 ^ k * N ^ k : ℕ) : ℝ) ^ σ) *
            ((N : ℝ) ^ σ)⁻¹ ^ k = (((2 : ℝ) ^ k) ^ σ) := by
      rw [inv_pow]
      exact hIdentity
    dsimp only [classicalTypeIIPowerLoss, E]
    calc
      (((2 ^ k * N ^ k : ℕ) : ℝ) ^ σ * 1 ^ k *
            (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ e) * (k : ℝ) *
              (((N : ℝ) ^ σ)⁻¹ ^ k * (V ^ k)⁻¹)) =
          ((((2 ^ k * N ^ k : ℕ) : ℝ) ^ σ * ((N : ℝ) ^ σ)⁻¹ ^ k) *
            1 ^ k * (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ e) *
              (k : ℝ) * V⁻¹ ^ k) := by rw [inv_pow]; ring
      _ = (((2 : ℝ) ^ k) ^ σ * 1 ^ k *
            (C * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ e) * (k : ℝ) * V⁻¹ ^ k) := by
          rw [hIdentity']
      _ ≤
          (2 : ℝ) ^ B * (C *
            ((((2 : ℝ) ^ k) * ((N ^ k : ℕ) : ℝ)) ^ (2 * e))) *
              (k : ℝ) *
                (aLog ^ B * (4 * Real.log T) ^ k * T ^ (u * k)) := by
          gcongr
          simpa using hTwoPowSigma
      _ = T ^ (u * k) *
          (((2 : ℝ) ^ B * C * aLog ^ B) *
            ((((2 : ℝ) ^ k) * ((N ^ k : ℕ) : ℝ)) ^ (2 * e)) *
              (k : ℝ) * (4 * Real.log T) ^ k) := by ring
  have hFinal :
      typeIIPoweredThresholdLoss C ((N : ℝ) ^ σ * V) 1 e σ N k ≤
        1 + T ^ (u * k) * classicalTypeIIPowerLoss E e T k (N ^ k) := by
    unfold typeIIPoweredThresholdLoss
    apply max_le
    · have : 0 ≤ T ^ (u * k) * classicalTypeIIPowerLoss E e T k (N ^ k) := by
        dsimp only [classicalTypeIIPowerLoss, E]
        positivity
      linarith
    · exact hRaw.trans (le_add_of_nonneg_left (by norm_num))
  simpa only [A, V, aLog, E] using hFinal

/-- Exact finite conversion from a multiplicity-preserving dichotomy witness
and its powered MHH subfamily to the endpoint power.  Unlike an abstract
cardinality lemma, this statement retains the original natural-valued zero
count and the precise extraction loss `W.card ≤ k * W'.card`. -/
theorem endpoint_powered_witness_count_le
    {σ τ₀ T V P K : ℝ} {Q k multiplicity count : ℕ}
    {W W' : Finset ℝ}
    (hσUpper : σ < 1) (hcert : EndpointScaleCertificate σ τ₀)
    (hT : 0 < T) (hQ : 1 < Q) (hk : 0 < k)
    (hP : 1 ≤ P) (hV : (Q : ℝ) ^ σ / P ≤ V)
    (hτLower : 2 * τ₀ / 3 ≤ typeILogarithmicScale T Q)
    (hτUpper : typeILogarithmicScale T Q ≤ τ₀)
    (hCount : count ≤ multiplicity * W.card)
    (hExtract : (W.card : ℝ) ≤ k * (W'.card : ℝ))
    (hK : 0 ≤ K)
    (hMHH : (W'.card : ℝ) ≤
      K * (1 + (((harmonic Q : ℚ) : ℝ))) *
        ((Q : ℝ) ^ 2 / V ^ 2 +
          (3 * T) * min ((Q : ℝ) / V ^ 2)
            ((Q : ℝ) ^ 4 / V ^ 6))) :
    (count : ℝ) ≤
      (multiplicity : ℝ) * k *
        (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀)) := by
  have hEndpoint := mhh_terms_le_two_loss_endpoint_target
    hσUpper hcert hT hQ hP hV hτLower hτUpper
  have hThree :
      (Q : ℝ) ^ 2 / V ^ 2 +
          (3 * T) * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6) ≤
        3 * ((Q : ℝ) ^ 2 / V ^ 2 +
          T * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6)) := by
    have hFirst : 0 ≤ (Q : ℝ) ^ 2 / V ^ 2 := by positivity
    nlinarith
  have hEndpointThree := hThree.trans (mul_le_mul_of_nonneg_left hEndpoint (by norm_num))
  have hCountReal : (count : ℝ) ≤ (multiplicity : ℝ) * (W.card : ℝ) := by
    exact_mod_cast hCount
  have hHarmonic : (0 : ℝ) ≤ ((harmonic Q : ℚ) : ℝ) := by
    exact_mod_cast (harmonic_pos (by omega : Q ≠ 0)).le
  calc
    (count : ℝ) ≤ (multiplicity : ℝ) * (W.card : ℝ) := hCountReal
    _ ≤ (multiplicity : ℝ) * (k * (W'.card : ℝ)) := by gcongr
    _ ≤ (multiplicity : ℝ) *
        (k * (K * (1 + (((harmonic Q : ℚ) : ℝ))) *
          ((Q : ℝ) ^ 2 / V ^ 2 +
            (3 * T) * min ((Q : ℝ) / V ^ 2)
              ((Q : ℝ) ^ 4 / V ^ 6)))) := by
      gcongr
    _ ≤ (multiplicity : ℝ) *
        (k * (K * (1 + (((harmonic Q : ℚ) : ℝ))) *
          (6 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀)))) := by
      gcongr
      nlinarith [hEndpointThree]
    _ = (multiplicity : ℝ) * k *
        (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀)) := by ring

/-- Variant of `endpoint_powered_witness_count_le` for a scale whose final
power comparison has already been established directly.  This is used by
the unpowered low Type-I branch, where the physical scale may lie just above
`τ₀` but is still below height exponent `2`. -/
theorem endpoint_witness_count_le_of_mhh_power
    {σ τ₀ T V P K : ℝ} {Q k multiplicity count : ℕ}
    {W W' : Finset ℝ}
    (hT : 0 < T) (hQ : 1 < Q) (hk : 0 < k)
    (hP : 1 ≤ P) (hV : (Q : ℝ) ^ σ / P ≤ V)
    (hPower : (Q : ℝ) ^
        classicalMHHExponent σ (typeILogarithmicScale T Q) ≤
      T ^ (3 * (1 - σ) / τ₀))
    (hCount : count ≤ multiplicity * W.card)
    (hExtract : (W.card : ℝ) ≤ k * (W'.card : ℝ))
    (hK : 0 ≤ K)
    (hMHH : (W'.card : ℝ) ≤
      K * (1 + (((harmonic Q : ℚ) : ℝ))) *
        ((Q : ℝ) ^ 2 / V ^ 2 +
          (3 * T) * min ((Q : ℝ) / V ^ 2)
            ((Q : ℝ) ^ 4 / V ^ 6))) :
    (count : ℝ) ≤
      (multiplicity : ℝ) * k *
        (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀)) := by
  have hLoss := mhh_terms_le_loss_sixth (Q : ℝ) T V P σ
    (by positivity) hT.le hP hV
  have hIdeal := ideal_mhh_terms_le_classicalMHHExponent (σ := σ) hT hQ
  have hEndpoint :
      (Q : ℝ) ^ 2 / V ^ 2 +
          T * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6) ≤
        2 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀) := by
    calc
      (Q : ℝ) ^ 2 / V ^ 2 +
            T * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6)
          ≤ P ^ (6 : ℕ) *
            ((Q : ℝ) ^ 2 / ((Q : ℝ) ^ σ) ^ 2 +
              T * min ((Q : ℝ) / ((Q : ℝ) ^ σ) ^ 2)
                ((Q : ℝ) ^ 4 / ((Q : ℝ) ^ σ) ^ 6)) := hLoss
      _ ≤ P ^ (6 : ℕ) *
            (2 * (Q : ℝ) ^ classicalMHHExponent σ
              (typeILogarithmicScale T Q)) := by gcongr
      _ ≤ P ^ (6 : ℕ) *
            (2 * T ^ (3 * (1 - σ) / τ₀)) := by gcongr
      _ = 2 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀) := by ring
  have hThree :
      (Q : ℝ) ^ 2 / V ^ 2 +
          (3 * T) * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6) ≤
        3 * ((Q : ℝ) ^ 2 / V ^ 2 +
          T * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6)) := by
    have hFirst : 0 ≤ (Q : ℝ) ^ 2 / V ^ 2 := by positivity
    nlinarith
  have hEndpointThree := hThree.trans
    (mul_le_mul_of_nonneg_left hEndpoint (by norm_num))
  have hCountReal : (count : ℝ) ≤ (multiplicity : ℝ) * (W.card : ℝ) := by
    exact_mod_cast hCount
  have hHarmonic : (0 : ℝ) ≤ ((harmonic Q : ℚ) : ℝ) := by
    exact_mod_cast (harmonic_pos (by omega : Q ≠ 0)).le
  calc
    (count : ℝ) ≤ (multiplicity : ℝ) * (W.card : ℝ) := hCountReal
    _ ≤ (multiplicity : ℝ) * (k * (W'.card : ℝ)) := by gcongr
    _ ≤ (multiplicity : ℝ) *
        (k * (K * (1 + (((harmonic Q : ℚ) : ℝ))) *
          ((Q : ℝ) ^ 2 / V ^ 2 +
            (3 * T) * min ((Q : ℝ) / V ^ 2)
              ((Q : ℝ) ^ 4 / V ^ 6)))) := by gcongr
    _ ≤ (multiplicity : ℝ) *
        (k * (K * (1 + (((harmonic Q : ℚ) : ℝ))) *
          (6 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀)))) := by
      gcongr
      nlinarith [hEndpointThree]
    _ = (multiplicity : ℝ) * k *
        (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * P ^ (6 : ℕ) * T ^ (3 * (1 - σ) / τ₀)) := by ring

/-- Bounded-factor version of `endpoint_witness_count_le_of_mhh_power`.
It records exactly the constant loss caused by the dyadic factor in a
powered extraction rather than moving the extracted scale away from the
source endpoint window. -/
theorem endpoint_witness_count_le_of_mhh_power_factor
    {σ τ₀ T V P K R : ℝ} {Q k multiplicity count : ℕ}
    {W W' : Finset ℝ}
    (hT : 0 < T) (hQ : 1 < Q) (hk : 0 < k)
    (hP : 1 ≤ P) (hV : (Q : ℝ) ^ σ / P ≤ V)
    (hPower : (Q : ℝ) ^
        classicalMHHExponent σ (typeILogarithmicScale T Q) ≤
      R * T ^ (3 * (1 - σ) / τ₀))
    (hCount : count ≤ multiplicity * W.card)
    (hExtract : (W.card : ℝ) ≤ k * (W'.card : ℝ))
    (hK : 0 ≤ K)
    (hMHH : (W'.card : ℝ) ≤
      K * (1 + (((harmonic Q : ℚ) : ℝ))) *
        ((Q : ℝ) ^ 2 / V ^ 2 +
          (3 * T) * min ((Q : ℝ) / V ^ 2)
            ((Q : ℝ) ^ 4 / V ^ 6))) :
    (count : ℝ) ≤
      (multiplicity : ℝ) * k *
        (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * P ^ (6 : ℕ) * R * T ^ (3 * (1 - σ) / τ₀)) := by
  have hLoss := mhh_terms_le_loss_sixth (Q : ℝ) T V P σ
    (by positivity) hT.le hP hV
  have hIdeal := ideal_mhh_terms_le_classicalMHHExponent (σ := σ) hT hQ
  have hEndpoint :
      (Q : ℝ) ^ 2 / V ^ 2 +
          T * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6) ≤
        2 * P ^ (6 : ℕ) * R * T ^ (3 * (1 - σ) / τ₀) := by
    calc
      (Q : ℝ) ^ 2 / V ^ 2 +
            T * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6)
          ≤ P ^ (6 : ℕ) *
            ((Q : ℝ) ^ 2 / ((Q : ℝ) ^ σ) ^ 2 +
              T * min ((Q : ℝ) / ((Q : ℝ) ^ σ) ^ 2)
                ((Q : ℝ) ^ 4 / ((Q : ℝ) ^ σ) ^ 6)) := hLoss
      _ ≤ P ^ (6 : ℕ) *
            (2 * (Q : ℝ) ^ classicalMHHExponent σ
              (typeILogarithmicScale T Q)) := by gcongr
      _ ≤ P ^ (6 : ℕ) *
            (2 * (R * T ^ (3 * (1 - σ) / τ₀))) := by gcongr
      _ = 2 * P ^ (6 : ℕ) * R * T ^ (3 * (1 - σ) / τ₀) := by ring
  have hThree :
      (Q : ℝ) ^ 2 / V ^ 2 +
          (3 * T) * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6) ≤
        3 * ((Q : ℝ) ^ 2 / V ^ 2 +
          T * min ((Q : ℝ) / V ^ 2) ((Q : ℝ) ^ 4 / V ^ 6)) := by
    have hFirst : 0 ≤ (Q : ℝ) ^ 2 / V ^ 2 := by positivity
    nlinarith
  have hEndpointThree := hThree.trans
    (mul_le_mul_of_nonneg_left hEndpoint (by norm_num))
  have hCountReal : (count : ℝ) ≤ (multiplicity : ℝ) * (W.card : ℝ) := by
    exact_mod_cast hCount
  have hHarmonic : (0 : ℝ) ≤ ((harmonic Q : ℚ) : ℝ) := by
    exact_mod_cast (harmonic_pos (by omega : Q ≠ 0)).le
  calc
    (count : ℝ) ≤ (multiplicity : ℝ) * (W.card : ℝ) := hCountReal
    _ ≤ (multiplicity : ℝ) * (k * (W'.card : ℝ)) := by gcongr
    _ ≤ (multiplicity : ℝ) *
        (k * (K * (1 + (((harmonic Q : ℚ) : ℝ))) *
          ((Q : ℝ) ^ 2 / V ^ 2 +
            (3 * T) * min ((Q : ℝ) / V ^ 2)
              ((Q : ℝ) ^ 4 / V ^ 6)))) := by gcongr
    _ ≤ (multiplicity : ℝ) *
        (k * (K * (1 + (((harmonic Q : ℚ) : ℝ))) *
          (6 * P ^ (6 : ℕ) * R * T ^ (3 * (1 - σ) / τ₀)))) := by
      gcongr
      nlinarith [hEndpointThree]
    _ = (multiplicity : ℝ) * k *
        (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * P ^ (6 : ℕ) * R * T ^ (3 * (1 - σ) / τ₀)) := by ring

/-- A lower logarithmic-scale bound gives a uniform physical upper bound on
the powered polynomial length. -/
theorem endpoint_scale_length_le
    {τ₀ T : ℝ} {Q : ℕ} (hτ₀ : 0 < τ₀) (hT : 0 < T) (hQ : 1 < Q)
    (hτ : 2 * τ₀ / 3 ≤ typeILogarithmicScale T Q) :
    (Q : ℝ) ≤ T ^ (3 / (2 * τ₀)) := by
  have hBase : (1 : ℝ) < Q := by exact_mod_cast hQ
  have ha : 0 < 2 * τ₀ / 3 := by positivity
  have hQa : (Q : ℝ) ^ (2 * τ₀ / 3) ≤ T :=
    (Real.le_logb_iff_rpow_le hBase hT).mp hτ
  have hInvNonneg : 0 ≤ (2 * τ₀ / 3)⁻¹ := inv_nonneg.mpr ha.le
  calc
    (Q : ℝ) = ((Q : ℝ) ^ (2 * τ₀ / 3)) ^ (2 * τ₀ / 3)⁻¹ := by
      symm
      exact Real.rpow_rpow_inv (by positivity) ha.ne'
    _ ≤ T ^ (2 * τ₀ / 3)⁻¹ :=
      Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hQa hInvNonneg
    _ = T ^ (3 / (2 * τ₀)) := by
      congr 1
      field_simp [hτ₀.ne']

/-- Any fixed natural power of `log T` is eventually dominated by an
arbitrarily small positive power of `T`. -/
theorem eventually_log_nat_power_le_rpow
    (B : ℕ) (η : ℝ) (hη : 0 < η) :
    ∀ᶠ T : ℝ in atTop, (Real.log T) ^ B ≤ T ^ η := by
  have hLittle := isLittleO_log_rpow_rpow_atTop (B : ℝ) hη
  filter_upwards [hLittle.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with T hBound hT
  have hLogNonneg : 0 ≤ Real.log T := Real.log_nonneg hT
  have hTNonneg : 0 ≤ T := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLogNonneg _),
    Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hTNonneg _)] at hBound
  rw [← Real.rpow_natCast]
  exact hBound

theorem eventually_rpow_le_half_self
    (d : ℝ) (hd : d < 1) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T → T ^ d ≤ T / 2 := by
  have hDecay : Tendsto (fun T : ℝ => T ^ (-(1 - d))) atTop (𝓝 0) :=
    tendsto_rpow_neg_atTop (by linarith)
  have hEventually : ∀ᶠ T : ℝ in atTop, T ^ (-(1 - d)) ≤ 1 / 2 := by
    filter_upwards [(tendsto_order.1 hDecay).2 (1 / 2)
      (by norm_num : (0 : ℝ) < 1 / 2)] with T hT
    exact hT.le
  rw [eventually_atTop] at hEventually
  obtain ⟨Tscale, hTscale⟩ := hEventually
  let T₀ := max 2 Tscale
  refine ⟨T₀, le_max_left _ _, ?_⟩
  intro T hT
  have hTTwo : 2 ≤ T := (le_max_left _ _).trans hT
  have hTscale' : Tscale ≤ T := (le_max_right _ _).trans hT
  have hTPos : 0 < T := by linarith
  have hDecay' := hTscale T hTscale'
  have hIdentity : T ^ d = T * T ^ (-(1 - d)) := by
    calc
      T ^ d = T ^ (1 + (-(1 - d))) := by congr 1; ring
      _ = T ^ (1 : ℝ) * T ^ (-(1 - d)) := Real.rpow_add hTPos _ _
      _ = T * T ^ (-(1 - d)) := by rw [Real.rpow_one]
  rw [hIdentity]
  nlinarith

/-- Uniform epsilon estimate for the complete powered threshold loss.  The
power `k` and the polynomial length `Q` may vary with `T`, but `k` is bounded
and `Q` lies in the endpoint logarithmic window. -/
theorem eventually_classicalTypeIIPowerLoss_sixth_le
    (A d τ₀ ε : ℝ) (B : ℕ) (hA : 0 ≤ A) (hd : 0 ≤ d)
    (hτ₀ : 0 < τ₀) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, Real.exp 1 ≤ T₀ ∧
      ∀ (T : ℝ) (Q k : ℕ), T₀ ≤ T → 1 < Q → 0 < k → k ≤ B →
        2 * τ₀ / 3 ≤ typeILogarithmicScale T Q →
        (1 + classicalTypeIIPowerLoss A d T k Q) ^ (6 : ℕ) ≤
          C * T ^ (18 * d / τ₀ + ε) := by
  let η : ℝ := ε / 6
  have hη : 0 < η := by dsimp only [η]; positivity
  have hLogEventually := eventually_log_nat_power_le_rpow B η hη
  rw [eventually_atTop] at hLogEventually
  obtain ⟨Tlog, hTlog⟩ := hLogEventually
  let T₀ : ℝ := max (Real.exp 1) Tlog
  let cScale : ℝ := ((2 : ℝ) ^ B) ^ (2 * d)
  let cLog : ℝ := (4 : ℝ) ^ B
  let cBase : ℝ := 1 + A * cScale * B * cLog
  let C : ℝ := cBase ^ (6 : ℕ)
  have hcScale : 0 < cScale := by dsimp only [cScale]; positivity
  have hcLog : 0 < cLog := by dsimp only [cLog]; positivity
  have hcBase : 0 < cBase := by dsimp only [cBase]; positivity
  refine ⟨C, by dsimp only [C]; positivity, T₀, le_max_left _ _, ?_⟩
  intro T Q k hT hQ hk hkB hτ
  have hTExp : Real.exp 1 ≤ T := (le_max_left _ _).trans hT
  have hTLog : Tlog ≤ T := (le_max_right _ _).trans hT
  have hTOne : 1 ≤ T := by
    calc
      1 = Real.exp 0 := by rw [Real.exp_zero]
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
      _ ≤ T := hTExp
  have hTPos : 0 < T := zero_lt_one.trans_le hTOne
  have hLogOne : 1 ≤ Real.log T := by
    simpa using Real.log_le_log (Real.exp_pos 1) hTExp
  have hLogBound : (Real.log T) ^ B ≤ T ^ η := hTlog T hTLog
  have hkReal : (0 : ℝ) < k := by exact_mod_cast hk
  have hkBReal : (k : ℝ) ≤ B := by exact_mod_cast hkB
  have hTwoPow : ((2 : ℝ) ^ k) ≤ (2 : ℝ) ^ B :=
    pow_le_pow_right₀ (by norm_num) hkB
  have hQScale : (Q : ℝ) ≤ T ^ (3 / (2 * τ₀)) :=
    endpoint_scale_length_le hτ₀ hTPos hQ hτ
  have hProduct : ((2 : ℝ) ^ k) * Q ≤
      (2 : ℝ) ^ B * T ^ (3 / (2 * τ₀)) := by gcongr
  have hScale : (((2 : ℝ) ^ k) * Q) ^ (2 * d) ≤
      cScale * T ^ (3 * d / τ₀) := by
    calc
      (((2 : ℝ) ^ k) * Q) ^ (2 * d) ≤
          ((2 : ℝ) ^ B * T ^ (3 / (2 * τ₀))) ^ (2 * d) :=
        Real.rpow_le_rpow (by positivity) hProduct (by positivity)
      _ = cScale * T ^ (3 * d / τ₀) := by
        rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hTPos.le _)]
        dsimp only [cScale]
        rw [← Real.rpow_mul hTPos.le]
        congr 1
        field_simp [hτ₀.ne']
  have hFourLogOne : (1 : ℝ) ≤ 4 * Real.log T := by nlinarith
  have hLogK : (4 * Real.log T) ^ k ≤ cLog * T ^ η := by
    calc
      (4 * Real.log T) ^ k ≤ (4 * Real.log T) ^ B :=
        pow_le_pow_right₀ hFourLogOne hkB
      _ = (4 : ℝ) ^ B * (Real.log T) ^ B := by rw [mul_pow]
      _ ≤ cLog * T ^ η := by
        dsimp only [cLog]
        gcongr
  have hCore : classicalTypeIIPowerLoss A d T k Q ≤
      (A * cScale * B * cLog) * T ^ (3 * d / τ₀ + η) := by
    dsimp only [classicalTypeIIPowerLoss]
    calc
      A * (((2 : ℝ) ^ k) * Q) ^ (2 * d) * (k : ℝ) *
            (4 * Real.log T) ^ k ≤
          A * (cScale * T ^ (3 * d / τ₀)) * B *
            (cLog * T ^ η) := by gcongr
      _ = (A * cScale * B * cLog) * T ^ (3 * d / τ₀ + η) := by
        rw [Real.rpow_add hTPos]
        ring
  have hPowOne : 1 ≤ T ^ (3 * d / τ₀ + η) := by
    apply Real.one_le_rpow hTOne
    positivity
  have hP : 1 + classicalTypeIIPowerLoss A d T k Q ≤
      cBase * T ^ (3 * d / τ₀ + η) := by
    dsimp only [cBase]
    nlinarith [mul_le_mul_of_nonneg_left hPowOne
      (mul_nonneg (mul_nonneg (mul_nonneg hA hcScale.le)
        (Nat.cast_nonneg B)) hcLog.le)]
  calc
    (1 + classicalTypeIIPowerLoss A d T k Q) ^ (6 : ℕ) ≤
        (cBase * T ^ (3 * d / τ₀ + η)) ^ (6 : ℕ) := by
      exact pow_le_pow_left₀ (by
        dsimp only [classicalTypeIIPowerLoss]
        positivity) hP 6
    _ = C * T ^ (18 * d / τ₀ + ε) := by
      dsimp only [C]
      rw [mul_pow]
      have hTPow : (T ^ (3 * d / τ₀ + η)) ^ (6 : ℕ) =
          T ^ (18 * d / τ₀ + ε) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hTPos.le]
        congr 1
        dsimp only [η]
        ring
      rw [hTPow]

/-- The complete finite loss occurring after witness extraction is uniformly
absorbed by the requested epsilon.  This includes displacement, analytic
multiplicity, both dyadic logarithms, the selected natural power, harmonic
loss, coefficient normalization, and the powered threshold. -/
theorem eventually_endpoint_loss_bundle_le
    (A K dDisp e τ₀ ε : ℝ) (B : ℕ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hdDisp : 0 < dDisp) (he : 0 < e) (hτ₀ : 0 < τ₀) (hε : 0 < ε)
    (hB : 0 < B) (hdDispEps : dDisp ≤ ε / 1000)
    (heEpsTau : e ≤ ε * τ₀ / 1000) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧
      ∀ (T : ℝ) (Q k : ℕ), T₀ ≤ T → 1 < Q → 0 < k → k ≤ B →
        2 * τ₀ / 3 ≤ typeILogarithmicScale T Q →
        ((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
            ((2 * ⌈T ^ dDisp⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
          k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss A e T k Q) ^ (6 : ℕ)) ≤
          C * T ^ ε := by
  obtain ⟨Cp, hCp, Tp, hTp, hPower⟩ :=
    eventually_classicalTypeIIPowerLoss_sixth_le
      A e τ₀ (ε / 4) B hA he.le hτ₀ (by positivity) hB
  obtain ⟨Cm, hCm, Tm, hTm, hMult⟩ :=
    eventually_dichotomy_multiplicity_factor_bound dDisp dDisp hdDisp.le hdDisp
  let Ch : ℝ := 2 + e⁻¹
  let C : ℝ := Cm * B * K * Ch * (6 * Cp)
  let T₀ : ℝ := max 8 (max Tp Tm)
  have hCh : 0 < Ch := by dsimp only [Ch]; positivity
  refine ⟨max 1 C, by positivity, T₀, le_max_left _ _, ?_⟩
  intro T Q k hT hQ hk hkB hτ
  have hTEight : 8 ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tp Tm ≤ T := (le_max_right _ _).trans hT
  have hTp' : Tp ≤ T := (le_max_left _ _).trans hRest
  have hTm' : Tm ≤ T := (le_max_right _ _).trans hRest
  have hTOne : 1 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hQOne : (1 : ℝ) ≤ Q := by exact_mod_cast hQ.le
  have hP := hPower T Q k hTp' hQ hk hkB hτ
  have hM := hMult T hTm'
  have hQScale : (Q : ℝ) ≤ T ^ (3 / (2 * τ₀)) :=
    endpoint_scale_length_le hτ₀ hTPos hQ hτ
  have hHarmRaw := harmonic_le_epsilon_rpow he Q
  have hQPowOne : (1 : ℝ) ≤ (Q : ℝ) ^ e := Real.one_le_rpow hQOne he.le
  have hMax : max 1 ((Q : ℝ) ^ e) = (Q : ℝ) ^ e := max_eq_right hQPowOne
  rw [hMax] at hHarmRaw
  have hHarm : 1 + (((harmonic Q : ℚ) : ℝ)) ≤ Ch * (Q : ℝ) ^ e := by
    dsimp only [Ch]
    nlinarith [mul_le_mul_of_nonneg_left hQPowOne
      (add_nonneg zero_le_one (inv_nonneg.mpr he.le))]
  have hQd : (Q : ℝ) ^ e ≤ T ^ (3 * e / (2 * τ₀)) := by
    calc
      (Q : ℝ) ^ e ≤ (T ^ (3 / (2 * τ₀))) ^ e :=
        Real.rpow_le_rpow (by positivity) hQScale he.le
      _ = T ^ (3 * e / (2 * τ₀)) := by
        rw [← Real.rpow_mul hTPos.le]
        congr 1
        field_simp [hτ₀.ne']
  have hExponent : 3 * dDisp + 3 * e / (2 * τ₀) +
        (18 * e / τ₀ + ε / 4) ≤ ε := by
    have heTauRatio : e / τ₀ ≤ ε / 1000 := by
      rw [div_le_iff₀ hτ₀]
      convert heEpsTau using 1
      ring
    have hRatio : 3 * e / (2 * τ₀) + 18 * e / τ₀ =
        (39 / 2 : ℝ) * (e / τ₀) := by
      field_simp [hτ₀.ne']
      ring
    rw [show 3 * dDisp + 3 * e / (2 * τ₀) + (18 * e / τ₀ + ε / 4) =
        3 * dDisp + (3 * e / (2 * τ₀) + 18 * e / τ₀) + ε / 4 by ring,
      hRatio]
    nlinarith
  have hRpowExponent :
      T ^ (3 * dDisp + 3 * e / (2 * τ₀) + (18 * e / τ₀ + ε / 4)) ≤
        T ^ ε := Real.rpow_le_rpow_of_exponent_le hTOne hExponent
  have hCnonneg : 0 ≤ C := by dsimp only [C]; positivity
  have hHarmNonneg : 0 ≤ 1 + (((harmonic Q : ℚ) : ℝ)) := by
    have : (0 : ℝ) ≤ ((harmonic Q : ℚ) : ℝ) := by
      exact_mod_cast (harmonic_pos (by omega : Q ≠ 0)).le
    linarith
  have hHarmT : 1 + (((harmonic Q : ℚ) : ℝ)) ≤
      Ch * T ^ (3 * e / (2 * τ₀)) :=
    hHarm.trans (mul_le_mul_of_nonneg_left hQd hCh.le)
  calc
    ((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
          ((2 * ⌈T ^ dDisp⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
        k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * (1 + classicalTypeIIPowerLoss A e T k Q) ^ (6 : ℕ)) ≤
      (Cm * T ^ (3 * dDisp)) * B * (K * (Ch * T ^ (3 * e / (2 * τ₀)))) *
        (6 * (Cp * T ^ (18 * e / τ₀ + ε / 4))) := by
      gcongr
      convert hM using 1
      ring
    _ = C * T ^
        (3 * dDisp + 3 * e / (2 * τ₀) + (18 * e / τ₀ + ε / 4)) := by
      dsimp only [C]
      have hPowAll : T ^ (3 * dDisp) * T ^ (3 * e / (2 * τ₀)) *
          T ^ (18 * e / τ₀ + ε / 4) =
          T ^ (3 * dDisp + 3 * e / (2 * τ₀) +
            (18 * e / τ₀ + ε / 4)) := by
        calc
          T ^ (3 * dDisp) * T ^ (3 * e / (2 * τ₀)) *
                T ^ (18 * e / τ₀ + ε / 4) =
              T ^ (3 * dDisp + 3 * e / (2 * τ₀)) *
                T ^ (18 * e / τ₀ + ε / 4) := by
            rw [show T ^ (3 * dDisp) * T ^ (3 * e / (2 * τ₀)) =
                T ^ (3 * dDisp + 3 * e / (2 * τ₀)) from
              (Real.rpow_add hTPos _ _).symm]
          _ = T ^ (3 * dDisp + 3 * e / (2 * τ₀) +
                (18 * e / τ₀ + ε / 4)) :=
            (Real.rpow_add hTPos _ _).symm
      calc
        (Cm * T ^ (3 * dDisp)) * (B : ℝ) *
              (K * (Ch * T ^ (3 * e / (2 * τ₀)))) *
                (6 * (Cp * T ^ (18 * e / τ₀ + ε / 4))) =
            (Cm * (B : ℝ) * K * Ch * (6 * Cp)) *
              (T ^ (3 * dDisp) * T ^ (3 * e / (2 * τ₀)) *
                T ^ (18 * e / τ₀ + ε / 4)) := by ring
        _ = (Cm * (B : ℝ) * K * Ch * (6 * Cp)) *
              T ^ (3 * dDisp + 3 * e / (2 * τ₀) +
                (18 * e / τ₀ + ε / 4)) := by rw [hPowAll]
    _ ≤ C * T ^ ε := mul_le_mul_of_nonneg_left hRpowExponent hCnonneg
    _ ≤ max 1 C * T ^ ε :=
      mul_le_mul_of_nonneg_right (le_max_right 1 C) (Real.rpow_nonneg hTPos.le _)

/-- The fourth-power detector loss remains negligible after every natural
power required to return a Type-I scale to the endpoint window.  This is the
finite floor/ceiling form of the source argument's `o(1)` bookkeeping. -/
theorem typeI_power_detector_exponent_budget
    {d τ₀ ε : ℝ} (hd : 0 < d) (hdOne : d ≤ 1)
    (hτ₀ : 0 < τ₀)
    (hdEps : d ≤ ε / 100000)
    (hdEpsTau : d ≤ ε * τ₀ / 100000) :
    let B := ⌈3 * (2 / d ^ 2) / (2 * τ₀)⌉₊
    6 * d ^ 4 * (B : ℝ) + ε / 4 ≤ ε := by
  dsimp only
  let B := ⌈3 * (2 / d ^ 2) / (2 * τ₀)⌉₊
  have hdSq : 0 < d ^ 2 := sq_pos_of_pos hd
  have hRatioNonneg : 0 ≤ 3 * (2 / d ^ 2) / (2 * τ₀) := by positivity
  have hCeil : (B : ℝ) < 3 * (2 / d ^ 2) / (2 * τ₀) + 1 := by
    dsimp only [B]
    exact Nat.ceil_lt_add_one hRatioNonneg
  have hdRatio : d / τ₀ ≤ ε / 100000 := by
    rw [div_le_iff₀ hτ₀]
    convert hdEpsTau using 1
    ring
  have hdSqRatio : d ^ 2 / τ₀ ≤ ε / 100000 := by
    calc
      d ^ 2 / τ₀ = d * (d / τ₀) := by field_simp [hτ₀.ne']
      _ ≤ 1 * (ε / 100000) := by
        exact mul_le_mul hdOne hdRatio (div_nonneg hd.le hτ₀.le) (by norm_num)
      _ = ε / 100000 := one_mul _
  have hdFourth : d ^ 4 ≤ d := by
    calc
      d ^ 4 = d ^ (4 : ℝ) := (Real.rpow_natCast d 4).symm
      _ ≤ d := Real.rpow_le_self_of_le_one hd.le hdOne (by norm_num)
  have hPowered : d ^ 4 * (B : ℝ) < 3 * (d ^ 2 / τ₀) + d ^ 4 := by
    have hMul := mul_lt_mul_of_pos_left hCeil (by positivity : 0 < d ^ 4)
    calc
      d ^ 4 * (B : ℝ) <
          d ^ 4 * (3 * (2 / d ^ 2) / (2 * τ₀) + 1) := hMul
      _ = 3 * (d ^ 2 / τ₀) + d ^ 4 := by
        field_simp [hd.ne', hτ₀.ne']
  have hSmall : d ^ 4 * (B : ℝ) ≤ 4 * ε / 100000 := by
    have hdFourthEps : d ^ 4 ≤ ε / 100000 := hdFourth.trans hdEps
    linarith
  nlinarith

/-! ## Exact Type-I basic-window witness consumer -/

/-- The literal Type-I alternative, once its actual scale lies in the basic
endpoint window, implies the multiplicity-weighted endpoint estimate.  The
proof consumes the normalized unrestricted MHH theorem and derives every
cutoff, threshold, harmonic, and displacement loss. -/
theorem actual_typeI_basic_window_dichotomy_witness_consumer
    {σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ ε
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ r ∈ Finset.range (Nat.clog 2 A), ∀ W : Finset ℝ,
          IsSeparated 1 W →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-d ^ 4) / 2)) / Nat.clog 2 A ≤
              ‖dirichletPoly (2 ^ r * Y)
                (classicalZetaLongLineCoeff A σ) t‖) →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          zeroCountRect σ 1 T (2 * T) ≤
            4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card →
          2 * τ₀ / 3 ≤ typeILogarithmicScale T (2 ^ r * Y) →
          typeILogarithmicScale T (2 ^ r * Y) ≤ τ₀ →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  intro ε hε
  have hσ : 0 < σ := by linarith
  let d := classicalEndpointLossParameter σ τ₀ ε
  have hdSpec := classicalEndpointLossParameter_spec hσLower hcert.tau0_pos hε
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, hdEps, hdEpsTau, _hdHalfGap, _hdSigma,
    hdSmall, _hdHalf, _hdOne, _hdSigmaStrict⟩
  let s : ℝ := d ^ 2
  let u : ℝ := d ^ 4
  have hs : 0 < s := by dsimp only [s]; positivity
  have hu : 0 < u := by dsimp only [u]; positivity
  have hsLeD : s ≤ d := by
    dsimp only [s]
    nlinarith [hd, _hdOne]
  have huLeD : u ≤ d := by
    dsimp only [u]
    nlinarith [hd, _hdOne]
  obtain ⟨K, hK, hMHH⟩ := actual_typeI_normalized_dichotomy_witness_mhh_native
  obtain ⟨Closs, hCloss, Tloss, hTloss, hLoss⟩ :=
    eventually_endpoint_loss_bundle_le typeIDirectPowerLossConstant K d u τ₀ ε 1
      typeIDirectPowerLossConstant_pos.le hK.le hd hu hcert.tau0_pos hε
      (by omega) hdEps (huLeD.trans hdEpsTau)
  obtain ⟨Tscale, hTscale, hScale⟩ := eventually_typeI_logarithmic_scale_upper s hs
  have hdOneStrict : d < 1 := by
    have hDen : 0 < 1000 * (1 + τ₀) := by nlinarith [hcert.tau0_pos]
    have hSmallStrict : 1 / (1000 * (1 + τ₀)) < 1 := by
      rw [div_lt_one hDen]
      nlinarith [hcert.tau0_pos]
    exact hdSmall.trans_lt hSmallStrict
  obtain ⟨Thalf, hThalf, hHalf⟩ := eventually_rpow_le_half_self d hdOneStrict
  let T₀ := max Tloss (max Tscale Thalf)
  refine ⟨Closs, hCloss, T₀, hTloss.trans (le_max_left _ _), ?_⟩
  intro T hT
  dsimp only
  intro r hr W hSep hLarge hRange hCount hTauLower hTauUpper
  have hTLoss : Tloss ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tscale Thalf ≤ T := (le_max_right _ _).trans hT
  have hTScale : Tscale ≤ T := (le_max_left _ _).trans hRest
  have hTHalf : Thalf ≤ T := (le_max_right _ _).trans hRest
  have hTEight : 8 ≤ T := hTloss.trans hTLoss
  have hTPos : 0 < T := by linarith
  have hDisp : T ^ d ≤ T / 2 := hHalf T hTHalf
  let Y := ⌊T ^ (d ^ 2)⌋₊
  let A := ⌊sharpZetaCutoff T⌋₊
  let N := 2 ^ r * Y
  have hNOne : 1 < N := by
    have hscaleAt := hScale T r hTScale
    simpa only [s, Y, N] using hscaleAt.1
  have hN : 0 < N := lt_trans Nat.zero_lt_one hNOne
  by_cases hW : W.Nonempty
  · obtain ⟨t, ht⟩ := hW
    let L : ℝ := ((3 / 4) * (T ^ (-d ^ 4) / 2)) / Nat.clog 2 A
    have hAOne : 1 < A := by
      dsimp only [A]
      apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
      apply Nat.le_floor
      exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
        (four_mul_lt_sharpZetaCutoff T).le
    have hNC : N < A := by
      have hLPos : 0 < L := by
        dsimp only [L]
        have hClog : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hAOne
        positivity
      exact typeI_start_lt_cutoff_of_positive_large_value A N σ t L hLPos
        (by simpa only [L, N, Y, A] using hLarge t ht)
    have hTN := physical_height_le_sq_of_basic_endpoint_scale
      hσLower hσUpper hcert hTPos hNOne hTauUpper
    let P : ℝ := 1 + classicalTypeIIPowerLoss
      typeIDirectPowerLossConstant u T 1 N
    have hP : 1 ≤ P := by
      dsimp only [P, classicalTypeIIPowerLoss]
      apply le_add_of_nonneg_right
      have hLog : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
      exact mul_nonneg
        (mul_nonneg
          (mul_nonneg typeIDirectPowerLossConstant_pos.le
            (Real.rpow_nonneg (by positivity) _)) (by norm_num))
        (by simpa using mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hLog)
    have hPDirect := typeIDirectThresholdLoss_le_classicalTypeIIPowerLoss
      (A := A) (N := N) (d := u) hTEight hu.le hNOne
        (by dsimp only [A]; exact le_rfl) hTN
    have hPDirectPos : 0 < typeIDirectThresholdLoss T A u := by
      unfold typeIDirectThresholdLoss
      positivity
    have hThresholdDirect := typeI_direct_normalized_threshold_lower
      (d := u) (N := N) (σ := σ) hTPos hAOne
    have hThreshold : (N : ℝ) ^ σ / P ≤ (N : ℝ) ^ σ * L := by
      calc
        (N : ℝ) ^ σ / P ≤
            (N : ℝ) ^ σ / typeIDirectThresholdLoss T A u := by
              exact div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
                hPDirectPos (by simpa only [P] using hPDirect)
        _ ≤ (N : ℝ) ^ σ * L := by
              simpa only [L, u] using hThresholdDirect
    have hLPos : 0 < L := by
      dsimp only [L]
      have hClog : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hAOne
      positivity
    have hMHHAt := hMHH A N σ d T L W hσ.le hN (by linarith)
      hLPos hDisp hSep (by simpa only [L, N, Y, A] using hRange)
      (by simpa only [L, N, Y, A] using hLarge)
    have hEndpoint := endpoint_powered_witness_count_le hσUpper hcert hTPos
      hNOne (by omega : 0 < (1 : ℕ)) hP hThreshold hTauLower hTauUpper
      (by simpa only [N, Y, A] using hCount)
      (by simp : (W.card : ℝ) ≤ (1 : ℕ) * (W.card : ℝ)) hK.le hMHHAt
    have hLossAt := hLoss T N 1 hTLoss hNOne (by omega) (by omega) hTauLower
    have hTargetNonneg : 0 ≤ T ^ (3 * (1 - σ) / τ₀) :=
      Real.rpow_nonneg hTPos.le _
    have hEndpoint' :
        (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
          ((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
            1 * (K * (1 + (((harmonic N : ℚ) : ℝ)))) *
              (6 * (1 + classicalTypeIIPowerLoss
                typeIDirectPowerLossConstant u T 1 N) ^ (6 : ℕ) *
                T ^ (3 * (1 - σ) / τ₀)) := by
      simpa only [A, d, P, s, Nat.cast_one] using hEndpoint
    have hLossAt' :
        ((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
            1 * (K * (1 + (((harmonic N : ℚ) : ℝ)))) *
              (6 * (1 + classicalTypeIIPowerLoss
                typeIDirectPowerLossConstant u T 1 N) ^ (6 : ℕ)) ≤
          Closs * T ^ ε := by
      simpa only [d, u, Nat.cast_one] using hLossAt
    calc
      (zeroCountRect σ 1 T (2 * T) : ℝ) ≤ _ := hEndpoint'
      _ = (((4 * Nat.clog 2 ⌊sharpZetaCutoff T⌋₊ *
            ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
            1 * (K * (1 + (((harmonic N : ℚ) : ℝ)))) *
              (6 * (1 + classicalTypeIIPowerLoss
                typeIDirectPowerLossConstant u T 1 N) ^ (6 : ℕ))) *
            T ^ (3 * (1 - σ) / τ₀) := by ring
      _ ≤ Closs * T ^ ε * T ^ (3 * (1 - σ) / τ₀) :=
        mul_le_mul_of_nonneg_right hLossAt' hTargetNonneg
  · have hWCard : W.card = 0 := Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hW)
    have hZero : zeroCountRect σ 1 T (2 * T) = 0 := by
      rw [hWCard, mul_zero] at hCount
      omega
    rw [hZero]
    norm_num
    exact mul_nonneg
      (mul_nonneg hCloss.le (Real.rpow_nonneg hTPos.le _))
      (Real.rpow_nonneg hTPos.le _)

set_option maxHeartbeats 800000

/-- The literal Type-I alternative in the raised-scale range.  This theorem
selects the natural power from the physical logarithmic scale, applies exact
finite powering to the actual sharp zeta block, extracts the resulting dyadic
polynomial, applies MHH, and returns to the original analytic-multiplicity
count with every finite loss absorbed in the requested epsilon. -/
theorem actual_typeI_powered_window_dichotomy_witness_consumer
    {σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ r ∈ Finset.range (Nat.clog 2 A), ∀ W : Finset ℝ,
          IsSeparated 1 W →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-d ^ 4) / 2)) / Nat.clog 2 A ≤
              ‖dirichletPoly (2 ^ r * Y)
                (classicalZetaLongLineCoeff A σ) t‖) →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          zeroCountRect σ 1 T (2 * T) ≤
            4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card →
          4 * τ₀ / 3 ≤ typeILogarithmicScale T (2 ^ r * Y) →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  intro ε hε
  have hσ : 0 < σ := by linarith
  let εs : ℝ := ε / 100
  let d := classicalEndpointLossParameter σ τ₀ εs
  have hεs : 0 < εs := by dsimp only [εs]; positivity
  have hdSpec := classicalEndpointLossParameter_spec hσLower hcert.tau0_pos hεs
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, hdEpsSmall, hdEpsTauSmall, _hdHalfGap, _hdSigma,
    hdSmall, _hdHalf, hdOne, _hdSigmaStrict⟩
  let s : ℝ := d ^ 2
  let u : ℝ := d ^ 4
  let e : ℝ := d ^ 3
  let U : ℝ := 2 / s
  let B : ℕ := ⌈3 * U / (2 * τ₀)⌉₊
  let R : ℝ := ((2 : ℝ) ^ B) ^ (2 : ℕ)
  have hs : 0 < s := by dsimp only [s]; positivity
  have hu : 0 < u := by dsimp only [u]; positivity
  have he : 0 < e := by dsimp only [e]; positivity
  have hU : 0 < U := by dsimp only [U]; positivity
  have hB : 0 < B := by
    dsimp only [B]
    exact Nat.ceil_pos.mpr
      (div_pos (mul_pos (by norm_num) hU) (mul_pos (by norm_num) hcert.tau0_pos))
  have heLeD : e ≤ d := by
    dsimp only [e]
    calc
      d ^ 3 = d ^ (3 : ℝ) := (Real.rpow_natCast d 3).symm
      _ ≤ d := Real.rpow_le_self_of_le_one hd.le hdOne (by norm_num)
  have hdEps : d ≤ ε / 100000 := by
    dsimp only [εs] at hdEpsSmall
    nlinarith
  have hdEpsTau : d ≤ ε * τ₀ / 100000 := by
    dsimp only [εs] at hdEpsTauSmall
    nlinarith
  have hdEpsQuarter : d ≤ (ε / 4) / 1000 := by nlinarith
  have heEpsTauQuarter : e ≤ (ε / 4) * τ₀ / 1000 := by
    exact heLeD.trans (by nlinarith [hdEpsTau])
  let τh : ℝ := 3 * τ₀ / 4
  have hτh : 0 < τh := by dsimp only [τh]; nlinarith [hcert.tau0_pos]
  have heEpsTauHalfQuarter : e ≤ (ε / 4) * τh / 1000 := by
    have heTiny : e ≤ ε * τ₀ / 100000 := heLeD.trans hdEpsTau
    dsimp only [τh]
    nlinarith [mul_pos hε hcert.tau0_pos]
  have hDetectorBudget : 6 * u * (B : ℝ) + ε / 4 ≤ ε := by
    simpa only [u, s, U, B] using
      typeI_power_detector_exponent_budget hd hdOne hcert.tau0_pos hdEps hdEpsTau
  obtain ⟨D, hD, K, hK, hPowered⟩ :=
    powered_actual_typeI_block_large_values_bound_bounded_uniform B e he
  let aLog : ℝ := max 1 (((8 / 3 : ℝ) * (1 + 2 / Real.log 2)) / 4)
  let E : ℝ := (2 : ℝ) ^ B * D * aLog ^ B
  have hE : 0 ≤ E := by dsimp only [E, aLog]; positivity
  obtain ⟨Closs, hCloss, Tloss, hTloss, hLoss⟩ :=
    eventually_endpoint_loss_bundle_le E K d e τh (ε / 4) B hE hK.le
      hd he hτh (by positivity) hB hdEpsQuarter heEpsTauHalfQuarter
  let Ctotal : ℝ := Closs * R
  have hCtotal : 0 < Ctotal := by dsimp only [Ctotal, R]; positivity
  obtain ⟨Tscale, hTscale, hScale⟩ := eventually_typeI_logarithmic_scale_upper s hs
  obtain ⟨Tdyadic, hTdyadic, hDyadicLower⟩ :=
    eventually_dyadic_power_scale_lower_half hcert.tau0_pos hU
  have hdOneStrict : d < 1 := by
    have hDen : 0 < 1000 * (1 + τ₀) := by nlinarith [hcert.tau0_pos]
    have hSmallStrict : 1 / (1000 * (1 + τ₀)) < 1 := by
      rw [div_lt_one hDen]
      nlinarith [hcert.tau0_pos]
    exact hdSmall.trans_lt hSmallStrict
  obtain ⟨Thalf, hThalf, hHalf⟩ := eventually_rpow_le_half_self d hdOneStrict
  let T₀ : ℝ := max Tloss (max Tscale (max Tdyadic Thalf))
  refine ⟨Ctotal, hCtotal, T₀, hTloss.trans (le_max_left _ _), ?_⟩
  intro T hT
  dsimp only
  intro r hr W hSep hLarge hRange hCount hTauMargin
  have hTLoss : Tloss ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tscale (max Tdyadic Thalf) ≤ T := (le_max_right _ _).trans hT
  have hTScale : Tscale ≤ T := (le_max_left _ _).trans hRest
  have hRest' : max Tdyadic Thalf ≤ T := (le_max_right _ _).trans hRest
  have hTDyadic : Tdyadic ≤ T := (le_max_left _ _).trans hRest'
  have hTHalf : Thalf ≤ T := (le_max_right _ _).trans hRest'
  have hTEight : 8 ≤ T := hTloss.trans hTLoss
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hDisp : T ^ d ≤ T / 2 := hHalf T hTHalf
  let Y := ⌊T ^ s⌋₊
  let A := ⌊sharpZetaCutoff T⌋₊
  let N := 2 ^ r * Y
  have hScaleData := hScale T r hTScale
  dsimp only at hScaleData
  rcases hScaleData with ⟨hNOne, hTauUpper⟩
  have hN : 0 < N := lt_trans Nat.zero_lt_one hNOne
  let τ := typeILogarithmicScale T N
  obtain ⟨k, hk, hkB, hTauPowLower, hTauPowUpper⟩ :=
    exists_bounded_positive_power_scale_reduction hcert.tau0_pos
      (by simpa only [τ, N, Y] using hTauMargin)
      (by simpa only [τ] using hTauUpper)
  have hBase : InBaseInterval (3 * T) W := by
    intro t ht
    rw [Set.mem_Icc]
    have htRange := hRange t ht
    constructor
    · calc
        (0 : ℝ) ≤ T / 2 := by linarith
        _ ≤ T - T ^ d := by linarith
        _ ≤ t := htRange.1
    · calc
        t ≤ 2 * T + T ^ d := htRange.2
        _ ≤ 3 * T := by linarith
  let L : ℝ := ((3 / 4 : ℝ) * (T ^ (-u) / 2)) / Nat.clog 2 A
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
    apply Nat.le_floor
    exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff T).le
  have hL : 0 < L := by
    dsimp only [L]
    have : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hAOne
    positivity
  obtain ⟨r₁, hr₁, W', hW', hCard, hSep', hBase', hLarge', hMHH⟩ :=
    hPowered k A N σ (3 * T) L W hk hkB hN hσ.le (by linarith)
      hL hSep hBase (by simpa only [L, N, Y, A, u, s] using hLarge)
  let Q : ℕ := 2 ^ r₁ * N ^ k
  let V : ℝ := ((((N : ℝ) ^ σ * L) ^ k /
      (D * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ e)) / k)
  have hr₁lt : r₁ < k := Finset.mem_range.mp hr₁
  have hQOne : 1 < Q := by
    dsimp only [Q]
    have hNk : 1 < N ^ k := one_lt_pow₀ hNOne hk.ne'
    exact hNk.trans_le (Nat.le_mul_of_pos_left _ (pow_pos (by omega) r₁))
  have hPower : (Q : ℝ) ^
        classicalMHHExponent σ (typeILogarithmicScale T Q) ≤
      R * T ^ (3 * (1 - σ) / τ₀) := by
    simpa only [Q, R, τ] using
      dyadic_power_mhh_le_endpoint_with_factor hσLower hσUpper hcert hTOne
        hNOne hk hkB hr₁lt hTauPowLower hTauPowUpper
  have hQScaleHalf : τ₀ / 2 ≤ typeILogarithmicScale T Q := by
    simpa only [Q, τ] using
      hDyadicLower T N k r₁ hTDyadic hNOne hk hr₁lt
        (by simpa only [τ] using hTauUpper) hTauPowLower
  let P := typeIIPoweredThresholdLoss D ((N : ℝ) ^ σ * L) 1 e σ N k
  have hThreshold := typeII_powered_threshold_lower (N := N) (k := k) (r := r₁)
    (C := D) (L := (N : ℝ) ^ σ * L) (D := 1) (η := e) (σ := σ)
    (zero_lt_one.trans_le hD)
      (mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast hN) σ) hL)
      (by norm_num) hN hk hσ.le hr₁lt
  dsimp only at hThreshold
  have hEnvelope := typeI_powered_threshold_loss_le_envelope
    (C := D) (e := e) (u := u) (σ := σ) (T := T) (N := N) (k := k)
      hD he.le hσUpper.le hTEight hN hk hkB
  dsimp only [A, L, aLog, E] at hEnvelope
  have hNpowQ : N ^ k ≤ Q := by
    dsimp only [Q]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by omega) r₁)
  have hEnvelopeQ : P ≤
      1 + T ^ (u * k) * classicalTypeIIPowerLoss E e T k Q := by
    calc
      P ≤ 1 + T ^ (u * k) * classicalTypeIIPowerLoss E e T k (N ^ k) := by
        simpa only [P, L, A, aLog, E] using hEnvelope
      _ ≤ 1 + T ^ (u * k) * classicalTypeIIPowerLoss E e T k Q := by
        gcongr
        exact classicalTypeIIPowerLoss_mono_length hE he.le hTOne hNpowQ
  let Pbig := T ^ (u * k) * (1 + classicalTypeIIPowerLoss E e T k Q)
  have hTukOne : 1 ≤ T ^ (u * k) :=
    Real.one_le_rpow hTOne (mul_nonneg hu.le (Nat.cast_nonneg k))
  have hLossNonneg : 0 ≤ classicalTypeIIPowerLoss E e T k Q := by
    dsimp only [classicalTypeIIPowerLoss]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hE (Real.rpow_nonneg (by positivity) _))
        (Nat.cast_nonneg k))
      (pow_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hTOne)) k)
  have hPbig : 1 ≤ Pbig := by
    dsimp only [Pbig]
    exact le_trans hTukOne
      (le_mul_of_one_le_right (Real.rpow_nonneg hTPos.le _)
        (le_add_of_nonneg_right hLossNonneg))
  have hPEnvelope : P ≤ Pbig := by
    calc
      P ≤ 1 + T ^ (u * k) * classicalTypeIIPowerLoss E e T k Q := hEnvelopeQ
      _ ≤ T ^ (u * k) * (1 + classicalTypeIIPowerLoss E e T k Q) := by
        calc
          1 + T ^ (u * k) * classicalTypeIIPowerLoss E e T k Q ≤
              T ^ (u * k) + T ^ (u * k) *
                classicalTypeIIPowerLoss E e T k Q := by gcongr
          _ = T ^ (u * k) *
              (1 + classicalTypeIIPowerLoss E e T k Q) := by ring
      _ = Pbig := rfl
  have hVBig : (Q : ℝ) ^ σ / Pbig ≤ V := by
    have hPPos : 0 < P := zero_lt_one.trans_le hThreshold.1
    exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
      hPPos hPEnvelope).trans (by
        simpa only [Q, V, P, div_one] using hThreshold.2)
  have hCountEndpoint := endpoint_witness_count_le_of_mhh_power_factor hTPos
    hQOne hk hPbig hVBig hPower hCount hCard hK.le
    (by simpa only [Q, V] using hMHH)
  have hLossAt := hLoss T Q k hTLoss hQOne hk hkB (by
    dsimp only [τh]
    convert hQScaleHalf using 1
    ring)
  have hDetectorBudgetK : 6 * u * (k : ℝ) + ε / 4 ≤ ε := by
    have hkReal : (k : ℝ) ≤ B := by exact_mod_cast hkB
    have hMono : 6 * u * (k : ℝ) ≤ 6 * u * (B : ℝ) := by gcongr
    linarith
  have hPowBudget : T ^ (ε / 4) * T ^ (6 * u * k) ≤ T ^ ε := by
    rw [← Real.rpow_add hTPos]
    exact Real.rpow_le_rpow_of_exponent_le hTOne (by nlinarith [hDetectorBudgetK])
  have hTargetNonneg : 0 ≤ T ^ (3 * (1 - σ) / τ₀) :=
    Real.rpow_nonneg hTPos.le _
  have hPbigPow : Pbig ^ (6 : ℕ) =
      T ^ (6 * u * k) * (1 + classicalTypeIIPowerLoss E e T k Q) ^ (6 : ℕ) := by
    dsimp only [Pbig]
    rw [mul_pow]
    have hTPow : (T ^ (u * (k : ℝ))) ^ (6 : ℕ) = T ^ (6 * u * k) := by
      calc
        (T ^ (u * (k : ℝ))) ^ (6 : ℕ) =
            (T ^ (u * (k : ℝ))) ^ (6 : ℝ) :=
          (Real.rpow_natCast _ 6).symm
        _ = T ^ ((u * (k : ℝ)) * 6) :=
          (Real.rpow_mul hTPos.le _ _).symm
        _ = T ^ (6 * u * k) := by congr 1; ring
    rw [hTPow]
  have hLossPowered :
      (((4 * Nat.clog 2 A *
          ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
          k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss E e T k Q) ^ (6 : ℕ))) *
          T ^ (6 * u * k) ≤
        (Closs * T ^ (ε / 4)) * T ^ (6 * u * k) := by
    exact mul_le_mul_of_nonneg_right (by simpa only [A] using hLossAt)
      (Real.rpow_nonneg hTPos.le _)
  have hCoreBudget :
      (Closs * T ^ (ε / 4)) * T ^ (6 * u * k) ≤ Closs * T ^ ε := by
    calc
      (Closs * T ^ (ε / 4)) * T ^ (6 * u * k) =
          Closs * (T ^ (ε / 4) * T ^ (6 * u * k)) := by ring
      _ ≤ Closs * T ^ ε := mul_le_mul_of_nonneg_left hPowBudget hCloss.le
  calc
    (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        ((4 * Nat.clog 2 A *
          ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
          k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
          (6 * Pbig ^ (6 : ℕ) * R * T ^ (3 * (1 - σ) / τ₀)) := by
          simpa only [Q] using hCountEndpoint
    _ = (((4 * Nat.clog 2 A *
          ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
          k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss E e T k Q) ^ (6 : ℕ))) *
          T ^ (6 * u * k) * R * T ^ (3 * (1 - σ) / τ₀) := by
            rw [hPbigPow]
            ring
    _ ≤ (Closs * T ^ (ε / 4)) * T ^ (6 * u * k) * R *
          T ^ (3 * (1 - σ) / τ₀) := by
            gcongr
    _ ≤ (Closs * R) * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
          calc
            (Closs * T ^ (ε / 4)) * T ^ (6 * u * k) * R *
                T ^ (3 * (1 - σ) / τ₀) =
              ((Closs * T ^ (ε / 4)) * T ^ (6 * u * k)) * R *
                T ^ (3 * (1 - σ) / τ₀) := by ring
            _ ≤ (Closs * T ^ ε) * R *
                T ^ (3 * (1 - σ) / τ₀) := by gcongr
            _ = (Closs * R) * T ^ ε *
                T ^ (3 * (1 - σ) / τ₀) := by ring

/-- The low-scale Type-I alternative is empty.  This theorem consumes the
literal dichotomy witness, obtains the terminal `N < t` relation, applies the
finite weighted B-process on every retained ordinate, and contradicts the
literal detector threshold including its `Nat.clog` denominator. -/
theorem actual_typeI_low_window_dichotomy_witness_consumer
    {σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ (ε / 100)
        let Y := ⌊T ^ (d ^ 2)⌋₊
        let A := ⌊sharpZetaCutoff T⌋₊
        ∀ r ∈ Finset.range (Nat.clog 2 A), ∀ W : Finset ℝ,
          IsSeparated 1 W →
          (∀ t ∈ W,
            ((3 / 4) * (T ^ (-d ^ 4) / 2)) / Nat.clog 2 A ≤
              ‖dirichletPoly (2 ^ r * Y)
                (classicalZetaLongLineCoeff A σ) t‖) →
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) →
          zeroCountRect σ 1 T (2 * T) ≤
            4 * Nat.clog 2 A *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) * W.card →
          typeILogarithmicScale T (2 ^ r * Y) < 2 * τ₀ / 3 →
          (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
            C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  intro ε hε
  have hσ : 0 < σ := by linarith
  let εs : ℝ := ε / 100
  let d := classicalEndpointLossParameter σ τ₀ εs
  let s : ℝ := d ^ 2
  let u : ℝ := d ^ 4
  have hεs : 0 < εs := by dsimp only [εs]; positivity
  have hdSpec := classicalEndpointLossParameter_spec hσLower hcert.tau0_pos hεs
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, _hdEps, _hdEpsTau, hdGap, _hdSigma,
    hdSmall, _hdHalf, hdOne, hdSigmaStrict⟩
  have hs : 0 < s := by dsimp only [s]; positivity
  have hu : 0 < u := by dsimp only [u]; positivity
  have huD : u ≤ d := by
    dsimp only [u]
    calc
      d ^ 4 = d ^ (4 : ℝ) := (Real.rpow_natCast d 4).symm
      _ ≤ d := Real.rpow_le_self_of_le_one hd.le hdOne (by norm_num)
  have huSigma : u < σ := huD.trans_lt hdSigmaStrict
  obtain ⟨Tscale, hTscale, hScale⟩ := eventually_typeI_logarithmic_scale_upper s hs
  obtain ⟨Tterminal, hTterminal, hTerminal⟩ :=
    eventually_typeI_start_lt_ordinate σ u hσ.le huSigma
  obtain ⟨Tmedium, hTmedium, hMedium⟩ :=
    eventually_medium_typeI_majorant_lt_detector hσLower hσUpper hcert
      hd huD hdGap hdSmall
  have hdOneStrict : d < 1 := by
    have hDen : 0 < 1000 * (1 + τ₀) := by nlinarith [hcert.tau0_pos]
    have hSmallStrict : 1 / (1000 * (1 + τ₀)) < 1 := by
      rw [div_lt_one hDen]
      nlinarith [hcert.tau0_pos]
    exact hdSmall.trans_lt hSmallStrict
  obtain ⟨Thalf, hThalf, hHalf⟩ := eventually_rpow_le_half_self d hdOneStrict
  let T₀ : ℝ := max 65 (max Tscale (max Tterminal (max Tmedium Thalf)))
  refine ⟨1, by norm_num, T₀, (by
    exact le_trans (by norm_num) (le_max_left _ _)), ?_⟩
  intro T hT
  dsimp only
  intro r hr W hSep hLarge hRange hCount hTauLow
  have hT65 : 65 ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tscale (max Tterminal (max Tmedium Thalf)) ≤ T :=
    (le_max_right _ _).trans hT
  have hTScale : Tscale ≤ T := (le_max_left _ _).trans hRest
  have hRest₁ : max Tterminal (max Tmedium Thalf) ≤ T :=
    (le_max_right _ _).trans hRest
  have hTTerminal : Tterminal ≤ T := (le_max_left _ _).trans hRest₁
  have hRest₂ : max Tmedium Thalf ≤ T := (le_max_right _ _).trans hRest₁
  have hTMedium : Tmedium ≤ T := (le_max_left _ _).trans hRest₂
  have hTHalf : Thalf ≤ T := (le_max_right _ _).trans hRest₂
  have hTEight : 8 ≤ T := by linarith
  have hTPos : 0 < T := by linarith
  have hDisp : T ^ d ≤ T / 2 := hHalf T hTHalf
  let Y := ⌊T ^ s⌋₊
  let A := ⌊sharpZetaCutoff T⌋₊
  let N := 2 ^ r * Y
  have hScaleData := hScale T r hTScale
  dsimp only at hScaleData
  rcases hScaleData with ⟨hNOne, _hTauUpper⟩
  have hN : 0 < N := lt_trans Nat.zero_lt_one hNOne
  by_cases hW : W.Nonempty
  · obtain ⟨t, htW⟩ := hW
    let L : ℝ := ((3 / 4 : ℝ) * (T ^ (-u) / 2)) / Nat.clog 2 A
    have hL : 0 < L := by
      dsimp only [L]
      have hAOne : 1 < A := by
        dsimp only [A]
        apply lt_of_lt_of_le (by omega : 1 < (2 : ℕ))
        apply Nat.le_floor
        exact (show (2 : ℝ) ≤ 4 * T by nlinarith).trans
          (four_mul_lt_sharpZetaCutoff T).le
      have hClog : 0 < Nat.clog 2 A := Nat.clog_pos Nat.one_lt_two hAOne
      positivity
    have hNC : N < A := typeI_start_lt_cutoff_of_positive_large_value
      A N σ t L hL (by simpa only [L, N, Y, A, u, s] using hLarge t htW)
    have htRange := hRange t htW
    have htHalf : T / 2 ≤ t := by linarith
    have htOne : 1 ≤ t := by linarith
    have hNt : (N : ℝ) < t := by
      by_contra hnot
      have htN : t ≤ (N : ℝ) := le_of_not_gt hnot
      have hMajor := hTerminal T t A N hTTerminal rfl hN hNC htHalf htN
      exact hnot (typeI_scale_lt_height_of_large A N σ t L hσ.le hN hNC
        htOne (by simpa only [L, N, Y, A, u, s] using hLarge t htW) hMajor)
    have htSquare : t ≤ (N : ℝ) ^ (2 : ℕ) := by
      exact htRange.2.trans (by
        have hThree := three_height_le_typeI_square_of_low_scale
          hσLower hσUpper hcert hT65 hNOne
          (by simpa only [N, Y, s] using hTauLow)
        nlinarith [hDisp])
    have hMajorant := hMedium T t N hTMedium hNOne (by linarith)
      (by nlinarith [htRange.2, hDisp]) (by simpa only [N, Y, s] using hTauLow)
    have hFalse := mediumTypeILargeValue_false A N σ t L hσ.le hN hNC
      hNt.le htSquare (by simpa only [L] using hMajorant)
      (by simpa only [L, N, Y, A, u, s] using hLarge t htW)
    exact False.elim hFalse
  · have hWCard : W.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hW)
    have hZeroLe : zeroCountRect σ 1 T (2 * T) ≤ 0 := by
      simpa only [hWCard, mul_zero] using hCount
    have hZero : zeroCountRect σ 1 T (2 * T) = 0 := Nat.eq_zero_of_le_zero hZeroLe
    rw [hZero]
    norm_num only [Nat.cast_zero, one_mul]
    exact mul_nonneg (Real.rpow_nonneg hTPos.le _) (Real.rpow_nonneg hTPos.le _)

/-! ## Exact Type-II dichotomy-witness consumer -/

set_option maxHeartbeats 800000

/-- The actual Type-II alternative of `classical_typeI_typeII_dichotomy_native`
implies the endpoint slab bound, including the original analytic multiplicity
factor.  The three small parameters have distinct jobs: `d` controls ordinate
displacement and multiplicity, `d²` controls the detector cutoffs, and `d³`
controls coefficient normalization after a power of size `O(d⁻²)`. -/
theorem actual_typeII_dichotomy_witness_consumer
    { σ τ₀ : ℝ} (hσLower : 1 / 2 < σ) (hσUpper : σ < 1)
    (hcert : EndpointScaleCertificate σ τ₀) :
    ∀ ε : ℝ, 0 < ε →
      ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
        let d := classicalEndpointLossParameter σ τ₀ ε
        let X := ⌊T ^ (d ^ 4 / 2)⌋₊
        let Y := ⌊T ^ (d ^ 2)⌋₊
        (∃ r ∈ Finset.range (Nat.clog 2 Y), ∃ W : Finset ℝ,
          IsSeparated 1 W ∧
          (∀ t ∈ W, (9 / 16 : ℝ) / Nat.clog 2 Y ≤
            ‖dirichletPoly (2 ^ r * X)
              (sharpMollifiedLineCoeff Y X σ) t‖) ∧
          (∀ t ∈ W, T - T ^ d ≤ t ∧ t ≤ 2 * T + T ^ d) ∧
          zeroCountRect σ 1 T (2 * T) ≤
            4 * Nat.clog 2 Y *
              ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) *
                W.card) →
        (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
          C * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
  intro ε hε
  have hσ : 0 < σ := by linarith
  let d := classicalEndpointLossParameter σ τ₀ ε
  have hdSpec := classicalEndpointLossParameter_spec hσLower hcert.tau0_pos hε
  dsimp only at hdSpec
  rcases hdSpec with ⟨hd, hdEps, hdEpsTau, _hdHalfGap, hdSigma, hdSmall,
    hdHalf, hdOne, hdSigmaStrict⟩
  let s : ℝ := d ^ 2
  let u : ℝ := d ^ 4
  let e : ℝ := d ^ 3
  let U : ℝ := 4 / u
  let B : ℕ := ⌈U / τ₀⌉₊
  have hs : 0 < s := by dsimp only [s]; positivity
  have hu : 0 < u := by dsimp only [u]; positivity
  have he : 0 < e := by dsimp only [e]; positivity
  have hsOne : s ≤ 1 := by dsimp only [s]; nlinarith
  have huLeTwoS : u ≤ 2 * s := by dsimp only [u, s]; nlinarith
  have heLeD : e ≤ d := by dsimp only [e]; nlinarith
  have hU : 0 < U := by dsimp only [U]; positivity
  have hB : 0 < B := by
    dsimp only [B]
    exact Nat.ceil_pos.mpr (div_pos hU hcert.tau0_pos)
  obtain ⟨C₀, hC₀, Cpow, hCpow, K, hK, hPowered⟩ :=
    actual_typeII_powered_mhh_bounded_uniform_native B e e he he
  let aLog : ℝ := max 1
    (((16 / 9 : ℝ) * (1 + (Real.log 2)⁻¹)) / 4)
  let Aenv : ℝ := (2 : ℝ) ^ B * C₀ ^ B * Cpow * aLog ^ B
  have hAenv : 0 ≤ Aenv := by dsimp only [Aenv, aLog]; positivity
  obtain ⟨Closs, hCloss, Tloss, hTloss, hLoss⟩ :=
    eventually_endpoint_loss_bundle_le Aenv K d e τ₀ ε B hAenv hK.le
      hd he hcert.tau0_pos hε hB hdEps (heLeD.trans hdEpsTau)
  obtain ⟨Tscale, hTscale, hScale⟩ :=
    eventually_typeII_logarithmic_scale_bounds_two u s hu hs huLeTwoS
  obtain ⟨Twindow, hTwindow, hWindow⟩ :=
    eventually_dyadic_power_scale_in_endpoint_window hcert.tau0_pos hU
  obtain ⟨Tcut, hTcut, hCut⟩ :=
    eventually_classical_dichotomy_cutoffs s u hs hu (by
      dsimp only [u, s]
      nlinarith) hsOne
  have hdOneStrict : d < 1 := by
    have hDen : 0 < 1000 * (1 + τ₀) := by nlinarith [hcert.tau0_pos]
    have hSmallStrict : 1 / (1000 * (1 + τ₀)) < 1 := by
      rw [div_lt_one hDen]
      nlinarith [hcert.tau0_pos]
    exact hdSmall.trans_lt hSmallStrict
  obtain ⟨Thalf, hThalf, hHalf⟩ := eventually_rpow_le_half_self d hdOneStrict
  let T₀ : ℝ := max Tloss (max Tscale (max Twindow (max Tcut Thalf)))
  refine ⟨Closs, hCloss, T₀, hTloss.trans (le_max_left _ _), ?_⟩
  intro T hT
  dsimp only
  intro hBranch
  have hTLoss : Tloss ≤ T := (le_max_left _ _).trans hT
  have hRest : max Tscale (max Twindow (max Tcut Thalf)) ≤ T :=
    (le_max_right _ _).trans hT
  have hTScale : Tscale ≤ T := (le_max_left _ _).trans hRest
  have hRest₁ : max Twindow (max Tcut Thalf) ≤ T :=
    (le_max_right _ _).trans hRest
  have hTWindow : Twindow ≤ T := (le_max_left _ _).trans hRest₁
  have hRest₂ : max Tcut Thalf ≤ T := (le_max_right _ _).trans hRest₁
  have hTCut : Tcut ≤ T := (le_max_left _ _).trans hRest₂
  have hTHalf : Thalf ≤ T := (le_max_right _ _).trans hRest₂
  have hTEight : 8 ≤ T := hTloss.trans hTLoss
  have hTPos : 0 < T := by linarith
  have hTOne : 1 ≤ T := by linarith
  have hDisp : T ^ d ≤ T / 2 := hHalf T hTHalf
  let X := ⌊T ^ (u / 2)⌋₊
  let Y := ⌊T ^ s⌋₊
  let A := ⌊sharpZetaCutoff T⌋₊
  have hCutData := hCut T hTCut
  dsimp only at hCutData
  rcases hCutData with ⟨hX, hY, hXY, hYA, hXT, hYT⟩
  rcases hBranch with ⟨r, hr, W, hSep, hLarge, hRange, hCount⟩
  let N := 2 ^ r * X
  have hScaleData := hScale T r hTScale (by simpa only [Y] using hr)
  dsimp only at hScaleData
  rcases hScaleData with ⟨hNOne, hTauLower, hTauUpper⟩
  have hN : 0 < N := lt_trans Nat.zero_lt_one hNOne
  let τ := typeILogarithmicScale T N
  have hTauSmallProduct : τ₀ * d ≤ 1 / 1000 := by
    have hRatio : τ₀ / (1 + τ₀) ≤ 1 := by
      rw [div_le_one (by linarith [hcert.tau0_pos] : 0 < 1 + τ₀)]
      linarith
    have hMul := mul_le_mul_of_nonneg_left hdSmall hcert.tau0_pos.le
    calc
      τ₀ * d ≤ τ₀ * (1 / (1000 * (1 + τ₀))) := hMul
      _ = (1 / 1000 : ℝ) * (τ₀ / (1 + τ₀)) := by
        field_simp [show (1 + τ₀) ≠ 0 by nlinarith [hcert.tau0_pos]]
      _ ≤ 1 / 1000 := by nlinarith
  have hTauSquareProduct : τ₀ * s ≤ 1 / 1000 := by
    dsimp only [s]
    calc
      τ₀ * d ^ 2 = (τ₀ * d) * d := by ring
      _ ≤ (1 / 1000 : ℝ) * d :=
        mul_le_mul_of_nonneg_right hTauSmallProduct hd.le
      _ ≤ 1 / 1000 := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hdOne (by norm_num : (0 : ℝ) ≤ 1 / 1000)
  have hTauMargin : 4 * τ₀ ≤ τ := by
    have hCore : 4 * τ₀ ≤ 1 / (2 * s) := by
      apply (le_div_iff₀ (by positivity : 0 < 2 * s)).2
      calc
        4 * τ₀ * (2 * s) = 8 * (τ₀ * s) := by ring
        _ ≤ 8 * (1 / 1000 : ℝ) := by gcongr
        _ ≤ 1 := by norm_num
    exact hCore.trans hTauLower
  obtain ⟨k, hk, hkB, hTauPowLower, hTauPowUpper⟩ :=
    exists_bounded_power_scale_reduction_with_margin hcert.tau0_pos
      hTauMargin hTauUpper
  have hBase : InBaseInterval (3 * T) W := by
    intro t ht
    rw [Set.mem_Icc]
    have htRange := hRange t ht
    constructor
    · calc
        (0 : ℝ) ≤ T / 2 := by linarith
        _ ≤ T - T ^ d := by linarith
        _ ≤ t := htRange.1
    · calc
        t ≤ 2 * T + T ^ d := htRange.2
        _ ≤ 3 * T := by linarith
  let L : ℝ := (9 / 16 : ℝ) / Nat.clog 2 Y
  have hL : 0 < L := by
    dsimp only [L]
    have : 0 < Nat.clog 2 Y := Nat.clog_pos Nat.one_lt_two hY
    positivity
  obtain ⟨r₁, hr₁, W', hW', hCard, hSep', hBase', hLarge', hMHH⟩ :=
    hPowered k Y X N σ (3 * T) L W hk hkB hN hσ.le (by linarith)
      hL hSep hBase (by simpa only [L, N] using hLarge)
  let D : ℝ := C₀ * (2 * N : ℝ) ^ e * (N : ℝ) ^ (-σ)
  let Q : ℕ := 2 ^ r₁ * N ^ k
  let V : ℝ := (((L / D) ^ k /
      (Cpow * ((2 ^ k * N ^ k : ℕ) : ℝ) ^ e)) / k)
  have hr₁lt : r₁ < k := Finset.mem_range.mp hr₁
  have hQWindow := hWindow T N k r₁ hTWindow hNOne hk hkB hr₁lt
    hTauUpper hTauPowLower hTauPowUpper
  dsimp only at hQWindow
  rcases hQWindow with ⟨hQOne, hQScaleLower, hQScaleUpper⟩
  have hNReal : (0 : ℝ) < N := by exact_mod_cast hN
  have hD : 0 < D := by
    dsimp only [D]
    exact mul_pos
      (mul_pos (zero_lt_one.trans_le hC₀)
        (Real.rpow_pos_of_pos (by positivity : (0 : ℝ) < 2 * N) e))
      (Real.rpow_pos_of_pos hNReal (-σ))
  let P := typeIIPoweredThresholdLoss Cpow L D e σ N k
  have hThreshold := typeII_powered_threshold_lower (N := N) (k := k) (r := r₁)
    (C := Cpow) (L := L) (D := D) (η := e) (σ := σ)
    (zero_lt_one.trans_le hCpow) hL hD hN hk hσ.le hr₁lt
  dsimp only at hThreshold
  have hYUpperPow : (Y : ℝ) ≤ T ^ s := by
    dsimp only [Y]
    exact Nat.floor_le (Real.rpow_nonneg hTPos.le _)
  have hEnvelope := typeII_powered_threshold_loss_le_envelope (e := e) hC₀ hCpow
    hsOne hσUpper.le (by
      calc Real.exp 1 ≤ 3 := Real.exp_one_lt_three.le
           _ ≤ 8 := by norm_num
           _ ≤ T := hTEight)
    hY hYUpperPow hN hk hkB
  dsimp only [L, D, aLog, Aenv] at hEnvelope
  have hNpowQ : N ^ k ≤ Q := by
    dsimp only [Q]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by omega) r₁)
  have hEnvelopeQ : P ≤ 1 + classicalTypeIIPowerLoss Aenv e T k Q := by
    calc
      P ≤ 1 + classicalTypeIIPowerLoss Aenv e T k (N ^ k) := by
        simpa only [P, L, D, aLog, Aenv] using hEnvelope
      _ ≤ 1 + classicalTypeIIPowerLoss Aenv e T k Q := by
        gcongr
        exact classicalTypeIIPowerLoss_mono_length hAenv he.le hTOne hNpowQ
  have hPBig : 1 ≤ 1 + classicalTypeIIPowerLoss Aenv e T k Q := by
    apply le_add_of_nonneg_right
    dsimp only [classicalTypeIIPowerLoss]
    have hFourLog : 0 ≤ 4 * Real.log T := by
      positivity [Real.log_nonneg hTOne]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hAenv (Real.rpow_nonneg (by positivity) _))
        (Nat.cast_nonneg k))
      (pow_nonneg hFourLog k)
  have hVBig : (Q : ℝ) ^ σ /
        (1 + classicalTypeIIPowerLoss Aenv e T k Q) ≤ V := by
    have hPPos : 0 < P := zero_lt_one.trans_le hThreshold.1
    have hBigPos : 0 < 1 + classicalTypeIIPowerLoss Aenv e T k Q :=
      zero_lt_one.trans_le hPBig
    exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (by positivity) _)
      hPPos hEnvelopeQ).trans (by simpa only [Q, V] using hThreshold.2)
  have hCountEndpoint := endpoint_powered_witness_count_le hσUpper hcert hTPos
    hQOne hk hPBig hVBig hQScaleLower hQScaleUpper hCount hCard hK.le
    (by simpa only [Q, V] using hMHH)
  have hClogMono : Nat.clog 2 Y ≤ Nat.clog 2 A := Nat.clog_mono_right 2 hYA
  have hMultiplicityMono :
      4 * Nat.clog 2 Y *
          ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) ≤
        4 * Nat.clog 2 A *
          ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) := by
    gcongr
  have hMultiplicityMonoReal :
      ((4 * Nat.clog 2 Y *
          ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) ≤
        ((4 * Nat.clog 2 A *
          ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) := by
    exact_mod_cast hMultiplicityMono
  have hHarmonicNonneg : 0 ≤ 1 + (((harmonic Q : ℚ) : ℝ)) := by
    have hq : (0 : ℝ) ≤ ((harmonic Q : ℚ) : ℝ) := by
      exact_mod_cast (harmonic_pos (by omega : Q ≠ 0)).le
    linarith
  have hLossAt := hLoss T Q k hTLoss hQOne hk hkB hQScaleLower
  have hEndpointNonneg : 0 ≤ T ^ (3 * (1 - σ) / τ₀) :=
    Real.rpow_nonneg hTPos.le _
  calc
    (zeroCountRect σ 1 T (2 * T) : ℝ) ≤
        (4 * Nat.clog 2 Y *
          ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) *
          k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss Aenv e T k Q) ^ (6 : ℕ) *
              T ^ (3 * (1 - σ) / τ₀)) := by
          simpa only [Q] using hCountEndpoint
    _ ≤ ((4 * Nat.clog 2 A *
          ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
          k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
            (6 * (1 + classicalTypeIIPowerLoss Aenv e T k Q) ^ (6 : ℕ)) *
              T ^ (3 * (1 - σ) / τ₀) := by
          calc
            ((4 * Nat.clog 2 Y *
                ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
                k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
                  (6 * (1 + classicalTypeIIPowerLoss Aenv e T k Q) ^ (6 : ℕ) *
                    T ^ (3 * (1 - σ) / τ₀)) ≤
              ((4 * Nat.clog 2 A *
                ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
                k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
                  (6 * (1 + classicalTypeIIPowerLoss Aenv e T k Q) ^ (6 : ℕ) *
                    T ^ (3 * (1 - σ) / τ₀)) := by
              gcongr
            _ = ((4 * Nat.clog 2 A *
                ((2 * ⌈T ^ d⌉₊ + 1) * classicalLocalMultiplicityCap T) : ℕ) : ℝ) *
                k * (K * (1 + (((harmonic Q : ℚ) : ℝ)))) *
                  (6 * (1 + classicalTypeIIPowerLoss Aenv e T k Q) ^ (6 : ℕ)) *
                    T ^ (3 * (1 - σ) / τ₀) := by ring
    _ ≤ Closs * T ^ ε * T ^ (3 * (1 - σ) / τ₀) := by
          exact mul_le_mul_of_nonneg_right hLossAt hEndpointNonneg

end RiemannZeta.GuthMaynard
