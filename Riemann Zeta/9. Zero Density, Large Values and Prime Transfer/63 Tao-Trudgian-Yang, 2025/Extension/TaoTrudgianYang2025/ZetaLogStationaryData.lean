import TaoTrudgianYang2025.BetaStationaryMain
import TaoTrudgianYang2025.ZetaLogarithmicPair

/-!
# Exact logarithmic stationary data

The inverse slope, curvature, amplitude and phase below belong to the
literal logarithmic phase already accepted by the sharp B-process.
All identities are restricted to its genuine stationary slope image.
-/

noncomputable section
open Set Expdb
open scoped FourierTransform
namespace TaoTrudgianYang2025

theorem modelPhaseInverseSlope_log {v : ℝ}
    (hv : v ∈ modelPhaseSlopeRange Real.log) :
    modelPhaseInverseSlope Real.log v = v⁻¹ := by
  have hd := deriv_modelPhaseInverseSlope_apply hv
  rw [Real.deriv_log] at hd
  simpa only [inv_inv] using congrArg (fun x : ℝ => x⁻¹) hd

theorem modelPhaseSlopeRange_log_pos {v : ℝ}
    (hv : v ∈ modelPhaseSlopeRange Real.log) : 0 < v := by
  have hu := modelPhaseInverseSlope_mem hv
  have hd := deriv_modelPhaseInverseSlope_apply hv
  rw [Real.deriv_log] at hd
  rw [← hd]
  exact inv_pos.mpr (by linarith [hu.1])

theorem modelPhaseCurvatureAt_log {v : ℝ}
    (hv : v ∈ modelPhaseSlopeRange Real.log) :
    modelPhaseCurvatureAt Real.log v = v^2 := by
  rw [modelPhaseCurvatureAt,Real.deriv_log',deriv_inv,neg_neg,
    modelPhaseInverseSlope_log hv,inv_pow,inv_inv]

theorem modelPhaseStationaryAmplitude_log {v : ℝ}
    (hv : v ∈ modelPhaseSlopeRange Real.log) :
    modelPhaseStationaryAmplitude Real.log v = v⁻¹ := by
  rw [modelPhaseStationaryAmplitude,modelPhaseCurvatureAt_log hv,
    Real.sqrt_sq (modelPhaseSlopeRange_log_pos hv).le]

theorem logarithmicStationaryFrequency_pos {T N r : ℝ}
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange Real.log) : 0 < r := by
  have hh := modelPhaseSlopeRange_log_pos hv
  exact (mul_pos_iff_of_pos_right hN).mp ((div_pos_iff_of_pos_right hT).mp hh)

theorem modelPhaseStationaryPoint_log {T N r : ℝ}
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange Real.log) :
    modelPhaseStationaryPoint Real.log T N r = T/r := by
  have hr := logarithmicStationaryFrequency_pos hT hN hv
  rw [modelPhaseStationaryPoint,modelPhaseInverseSlope_log hv]
  field_simp

theorem modelPhasePhysicalAmplitude_log {T N r : ℝ}
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange Real.log) :
    modelPhasePhysicalAmplitude Real.log T N r = Real.sqrt T/r := by
  have hr := logarithmicStationaryFrequency_pos hT hN hv
  rw [modelPhasePhysicalAmplitude_eq (log_approximateModel 1 (le_refl 0)) hT hN hv,
    modelPhaseStationaryAmplitude_log hv]
  have hs := Real.sq_sqrt hT.le
  have hsp := Real.sqrt_pos.mpr hT
  field_simp
  nlinarith

theorem modelPhaseFrequencyPhase_log_stationary {T N r : ℝ}
    (hT : 0 < T) (hN : 0 < N)
    (hv : r*N/T ∈ modelPhaseSlopeRange Real.log) :
    modelPhaseFrequencyPhase Real.log T N r (modelPhaseStationaryPoint Real.log T N r) =
      T*Real.log (T/N)-T*Real.log r-T := by
  have hr := logarithmicStationaryFrequency_pos hT hN hv
  rw [modelPhaseStationaryPoint_log hT hN hv,modelPhaseFrequencyPhase]
  have heq : T/r/N = (T/N)/r := by ring
  rw [heq,Real.log_div (div_pos hT hN).ne' hr.ne']
  field_simp

end TaoTrudgianYang2025
