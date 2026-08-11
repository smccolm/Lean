import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Fourier.PoissonSummation
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

end RiemannZeta.GuthMaynard
