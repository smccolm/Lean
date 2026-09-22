import TaoTrudgianYang2025.BourgainRetainedCardinality
import TaoTrudgianYang2025.JutilaPowerWindows

/-!
# Honest enlargement of retained zeta windows

Monotonicity concerns the actual integral and actual difference counts.
The native integer smoothing radius, including the unit enlargement,
is bounded by a physical small power only at a proved uniform threshold.
-/

open Filter Finset MeasureTheory
open RiemannZeta.GuthMaynard

noncomputable section

namespace TaoTrudgianYang2025

theorem bourgainLocalZetaSquare_mono {H K : ℝ}
    (hH : 0 ≤ H) (hHK : H ≤ K) (ℓ : ℤ) :
    bourgainLocalZetaSquare H ℓ ≤ bourgainLocalZetaSquare K ℓ := by
  unfold bourgainLocalZetaSquare
  exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) hHK
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (((continuous_zetaMomentCriticalNorm.comp (continuous_const.add continuous_id)).pow 2).intervalIntegrable _ _)

theorem bourgainZetaDifferenceMoment_mono (W : Finset ℝ) {H K : ℝ}
    (hH : 0 ≤ H) (hHK : H ≤ K) :
    bourgainZetaDifferenceMoment W H ≤ bourgainZetaDifferenceMoment W K := by
  unfold bourgainZetaDifferenceMoment
  exact Finset.sum_le_sum (fun ℓ _ => mul_le_mul_of_nonneg_left
    (bourgainLocalZetaSquare_mono hH hHK ℓ) (Nat.cast_nonneg _))

/-- The integer ceiling and the unit-window shift both fit the exponent gap. -/
theorem eventually_bourgain_smoothing_radius_le {θ ε : ℝ}
    (hθ : 0 ≤ θ) (hθε : θ < ε) :
    ∀ᶠ T : ℝ in atTop,
      (heathBrownSmoothingHeight T θ : ℝ)+1 ≤ T^ε := by
  filter_upwards [eventually_const_mul_rpow_le_rpow (D := 3) hθε,
    eventually_ge_atTop (1 : ℝ)] with T hbound hT
  have hH := heathBrownSmoothingHeight_le_two_rpow hT hθ
  have hone := Real.one_le_rpow hT hθ
  linarith

/-- The square root of the actual smoothing factor costs at most one
additional copy of its small power, uniformly for T at least one. -/
theorem bourgain_retained_sqrt_coefficient_le {B T ν : ℝ}
    (hB : 0 ≤ B) (hT : 1 ≤ T) (hν : 0 ≤ ν) :
    (B*T^ν)*Real.sqrt (2*(B*T^ν)) ≤ B*Real.sqrt (2*B)*T^(2*ν) := by
  have hTp : 0 < T := by linarith
  have ht := Real.one_le_rpow hT hν
  have hs : Real.sqrt (T^ν) ≤ T^ν := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (T^ν-1)]
  calc
    _ = (B*T^ν)*(Real.sqrt (2*B)*Real.sqrt (T^ν)) := by
      rw [show 2*(B*T^ν) = (2*B)*T^ν by ring, Real.sqrt_mul (by positivity)]
    _ ≤ (B*T^ν)*(Real.sqrt (2*B)*T^ν) := by gcongr
    _ = _ := by
      rw [show (B*T^ν)*(Real.sqrt (2*B)*T^ν) =
        B*Real.sqrt (2*B)*(T^ν*T^ν) by ring, ← Real.rpow_add hTp]
      congr 2
      ring

end TaoTrudgianYang2025
