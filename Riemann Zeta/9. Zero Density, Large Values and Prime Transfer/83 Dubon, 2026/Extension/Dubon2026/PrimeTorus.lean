import Dubon2026.PrimeFrequencies
import Dubon2026.SymmetricAverage
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! # The normalized prime torus and the actual vertical flow -/

namespace Dubon2026

open Filter MeasureTheory
open scoped BigOperators Topology

noncomputable section

/-- The normalized circle measure used by Mathlib's multivariable Fourier theorem. -/
local instance primeTorusCircleMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance primeTorusCircleProbability : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- A finite product of unit additive circles, one for each prime at most `N`. -/
abbrev PrimeTorus (N : ℕ) := UnitAddTorus (PrimeCoordinate N)

/-- Product Haar probability; each coordinate circle has total mass one. -/
def torusHaar (N : ℕ) : Measure (PrimeTorus N) :=
  Measure.pi (fun _ : PrimeCoordinate N => AddCircle.haarAddCircle)

instance torusHaar_isProbabilityMeasure (N : ℕ) : IsProbabilityMeasure (torusHaar N) := by
  unfold torusHaar
  infer_instance

/-- The additive parametrization matching `exp(-i t log p)` after multiplication by `2πi`. -/
def primeTorusFlow (N : ℕ) (t : ℝ) : PrimeTorus N :=
  fun p => ((-t * Real.log p.val / (2 * Real.pi) : ℝ) : UnitAddCircle)

theorem continuous_primeTorusFlow (N : ℕ) : Continuous (primeTorusFlow N) := by
  apply continuous_pi
  intro p
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp (by fun_prop)

theorem fourier_primeTorusFlow (N : ℕ) (t : ℝ) (p : PrimeCoordinate N) (k : ℤ) :
    fourier k (primeTorusFlow N t p) =
      Complex.exp (-Complex.I * (t : ℂ) * ((k : ℂ) * (Real.log p.val : ℂ))) := by
  rw [primeTorusFlow, fourier_coe_apply]
  congr 1
  push_cast
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp

theorem fourier_one_primeTorusFlow (N : ℕ) (t : ℝ) (p : PrimeCoordinate N) :
    fourier 1 (primeTorusFlow N t p) = verticalFlow N t p := by
  simpa only [Int.cast_one, one_mul, verticalFlow] using fourier_primeTorusFlow N t p 1

theorem mFourier_primeTorusFlow (N : ℕ) (k : PrimeCoordinate N → ℤ) (t : ℝ) :
    UnitAddTorus.mFourier k (primeTorusFlow N t) =
      Complex.exp ((-Complex.I *
        ((∑ p : PrimeCoordinate N, (k p : ℝ) * Real.log p.val : ℝ) : ℂ)) * (t : ℂ)) := by
  simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, fourier_primeTorusFlow,
    ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p _
  ring

theorem integral_mFourier_torusHaar (N : ℕ) (k : PrimeCoordinate N → ℤ) :
    (∫ z, UnitAddTorus.mFourier k z ∂torusHaar N) = if k = 0 then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := PrimeCoordinate N))) 0 k
  simpa only [UnitAddTorus.mFourierLp, ContinuousMap.inner_toLp,
    UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, map_one, one_mul, mul_one, eq_comm] using h

/-- Symmetric vertical averaging of an actual continuous function on the prime torus. -/
def torusAverage (N : ℕ) (f : C(PrimeTorus N, ℂ)) (T : ℝ) : ℂ :=
  symmetricAverage (fun t => f (primeTorusFlow N t)) T

theorem norm_torusAverage_le (N : ℕ) (f : C(PrimeTorus N, ℂ)) (T : ℝ) :
    ‖torusAverage N f T‖ ≤ ‖f‖ :=
  norm_symmetricAverage_le (norm_nonneg f)
    (fun t => f.norm_coe_le_norm (primeTorusFlow N t)) T

theorem tendsto_torusAverage_mFourier (N : ℕ) (k : PrimeCoordinate N → ℤ) :
    Tendsto (torusAverage N (UnitAddTorus.mFourier k)) atTop
      (𝓝 (∫ z, UnitAddTorus.mFourier k z ∂torusHaar N)) := by
  classical
  rw [integral_mFourier_torusHaar]
  by_cases hk : k = 0
  · simp only [hk, if_true, UnitAddTorus.mFourier_zero]
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with T hT
    exact (symmetricAverage_const (1 : ℂ) hT).symm
  · rw [if_neg hk]
    have hω : (∑ p : PrimeCoordinate N, (k p : ℝ) * Real.log p.val) ≠ 0 := by
      intro h
      exact hk (funext (prime_log_integer_independent k h))
    change Tendsto (fun T => symmetricAverage
      (fun t => UnitAddTorus.mFourier k (primeTorusFlow N t)) T) atTop (𝓝 0)
    simp_rw [mFourier_primeTorusFlow]
    exact tendsto_symmetricAverage_exp_zero hω

end

end Dubon2026
