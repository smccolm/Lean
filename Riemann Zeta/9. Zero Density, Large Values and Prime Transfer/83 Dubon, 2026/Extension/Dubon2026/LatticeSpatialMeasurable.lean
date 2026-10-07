import Dubon2026.LatticeMellinTailSplit
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-! # Spatial measurability of the actual lattice Mellin continuation -/

namespace Dubon2026

open UpperHalfPlane MeasureTheory Set

noncomputable section

/-- The literal determinant-one quadratic form depends continuously on its upper-half-plane point. -/
theorem continuous_latticeQuadratic (v : ℤ × ℤ) : Continuous (fun z : ℍ => latticeQuadratic z v) := by
  unfold latticeQuadratic
  apply Continuous.div
  · fun_prop
  · exact continuous_im
  · exact fun z => z.im_ne_zero

/-- Every actual Gaussian lattice term is jointly continuous in the point and theta parameter. -/
theorem continuous_latticeThetaTerm_joint (v : ℤ × ℤ) :
    Continuous (fun p : ℍ × ℝ => latticeThetaTerm p.1 p.2 v) := by
  exact Real.continuous_exp.comp
    ((continuous_const.mul continuous_snd).mul ((continuous_latticeQuadratic v).comp continuous_fst))

/-- The actual nonzero lattice theta sum is jointly measurable. -/
theorem measurable_latticeThetaRemainder_joint :
    Measurable (fun p : ℍ × ℝ => latticeThetaRemainder p.1 p.2) :=
  Measurable.tsum (fun v => (continuous_latticeThetaTerm_joint v.val).measurable)

/-- The entire upper-tail Mellin function is measurable in its actual spatial variable. -/
theorem measurable_latticeThetaMellinTail (s : ℂ) :
    Measurable (fun z : ℍ => latticeThetaMellinTail z s) := by
  have hf : Measurable (fun p : ℍ × ℝ =>
      Complex.exp ((Real.log p.2 : ℂ) * (s - 1)) * (latticeThetaRemainder p.1 p.2 : ℂ)) :=
    (Complex.continuous_exp.measurable.comp
      ((Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp measurable_snd)).mul_const _)).mul
        (Complex.continuous_ofReal.measurable.comp measurable_latticeThetaRemainder_joint)
  have hi := hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (1 : ℝ)))
  have he : (fun z : ℍ => latticeThetaMellinTail z s) =
      (fun z : ℍ => ∫ t : ℝ in Ioi 1,
        Complex.exp ((Real.log t : ℂ) * (s - 1)) * (latticeThetaRemainder z t : ℂ)) := by
    funext z
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change latticeThetaMellinKernel z s t =
      Complex.exp ((Real.log t : ℂ) * (s - 1)) * (latticeThetaRemainder z t : ℂ)
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    rw [latticeThetaMellinKernel, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht0.ne'),
      ← Complex.ofReal_log ht0.le]
  rw [he]
  exact hi.measurable

/-- The actual entire regularized lattice continuation is measurable in the upper-half-plane point. -/
theorem measurable_latticeCompletedMellinRegular (s : ℂ) :
    Measurable (fun z : ℍ => latticeCompletedMellinRegular z s) := by
  have h := ((measurable_latticeThetaMellinTail s).add
    (measurable_latticeThetaMellinTail (1 - s))).div_const (2 : ℂ)
  simpa only [latticeCompletedMellinRegular_eq_tails] using h

/-- The genuine meromorphic lattice continuation is spatially measurable at every fixed parameter. -/
theorem measurable_latticeCompletedMellin (s : ℂ) :
    Measurable (fun z : ℍ => latticeCompletedMellin z s) := by
  have h := ((measurable_latticeCompletedMellinRegular s).sub_const (1 / (2 * s))).add_const
    (1 / (2 * (s - 1)))
  simpa only [latticeCompletedMellin_eq_regular] using h

end
end Dubon2026
