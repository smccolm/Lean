import GafniTao.PintzOffDiagonalAbsorption

/-!
# Native finite near-one density inequality

Both analytic hypotheses of the earlier physical assembly are discharged in
this module.  The only remaining restrictions are explicit source parameter
ranges and lower bounds on the physical height.
-/

open Asymptotics Filter

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem eventually_two_pintzDensityLambda_le_height
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ T : ℝ in atTop, ∀ eta : ℝ,
      0 < eta → eta ≤ 1 →
      c / vinogradovKorobovDenominator T < eta →
      2 * pintzDensityLambda eta T ≤ T := by
  have hLittleReal :
      (fun T : ℝ =>
        (2 * pintzDensityLambdaLogCoefficient c) *
          Real.log T ^ (2 : ℝ)) =o[atTop]
        (fun T : ℝ => T ^ (1 : ℝ)) :=
    (isLittleO_log_rpow_rpow_atTop 2 (by norm_num)).const_mul_left
      (2 * pintzDensityLambdaLogCoefficient c)
  have hLittle :
      (fun T : ℝ =>
        (2 * pintzDensityLambdaLogCoefficient c) *
          Real.log T ^ (2 : ℕ)) =o[atTop]
        (fun T : ℝ => T) := by
    apply hLittleReal.congr' _ _
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T _hT
      congr 1
      exact Real.rpow_natCast (Real.log T) 2
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with T _hT
      rw [Real.rpow_one]
  filter_upwards [hLittle.eventuallyLE,
    eventually_ge_atTop (Real.exp (Real.exp 1))] with T hlog hT eta
      heta hetaUpper hetaAbove
  have hlambda := pintzDensityLambda_le_log_sq
    hc heta hetaUpper hT hetaAbove
  have hcoeff : 0 ≤ 2 * pintzDensityLambdaLogCoefficient c := by
    exact mul_nonneg (by norm_num) (pintzDensityLambdaLogCoefficient_pos hc).le
  have hlogNonneg : 0 ≤ Real.log T ^ (2 : ℕ) := sq_nonneg _
  have hNormLeft :
      ‖(2 * pintzDensityLambdaLogCoefficient c) *
        Real.log T ^ (2 : ℕ)‖ =
      (2 * pintzDensityLambdaLogCoefficient c) *
        Real.log T ^ (2 : ℕ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hcoeff hlogNonneg)]
  have hNormRight : ‖T‖ = T := by
    rw [Real.norm_eq_abs, abs_of_nonneg ((Real.exp_pos _).trans_le hT).le]
  rw [hNormLeft, hNormRight] at hlog
  nlinarith

theorem pintz_physical_finite_density_native
    {c eta T : ℝ} (hc : 0 < c) (heta : 0 < eta)
    (hetaUpper : eta ≤ 1 / 8)
    (hBasic : max (Real.exp 2) 8 ≤ T)
    (hErrorHeight : pintzContourErrorHeight c ≤ T)
    (hCoreHeight : pintzCoreAbsorptionHeight c ≤ T)
    (hLambdaHeight : 2 * pintzDensityLambda eta T ≤ T)
    (hetaAbove : c / vinogradovKorobovDenominator T < eta) :
    (zeroCount (1 - eta) T : ℝ) *
        pintzDetectedLowerBound eta (pintzDensityLambda eta T) T ^ 2 ≤
      (2 * ((2 * Nat.ceil (2 * pintzDensityLambda eta T + 3) + 1) *
          Nat.ceil (globalLocalZeroLogConstant * Real.log T)) : ℝ) *
          pintzDetectedLowerBound eta (pintzDensityLambda eta T) T ^ 2 +
      (pintzSelectionLoss (2 * pintzDensityLambda eta T)
          (pintzAdaptiveSeparation c eta T) T : ℝ) *
        (2 * (harmonic (pintzMobiusCutoff
            (pintzDensityLambda eta T)) : ℝ) *
          ((pintzMobiusCutoff (pintzDensityLambda eta T) : ℝ) ^
              (4 * eta) *
            (harmonic (pintzMobiusCutoff
              (pintzDensityLambda eta T)) : ℝ))) := by
  have hBase : Real.exp (Real.exp 1) ≤ T :=
    (pintzContourErrorHeight c |> fun H => by
      unfold pintzContourErrorHeight at hErrorHeight
      exact (Real.exp_le_exp.mpr (le_max_left _ _)).trans hErrorHeight)
  have hlambda : pintzMobiusLambdaThreshold ≤
      pintzDensityLambda eta T := by
    have hExp : Real.exp 1 ≤ T :=
      (Real.exp_le_exp.mpr
        (Real.one_lt_exp_iff.mpr zero_lt_one).le).trans hBase
    exact pintzDensityLambda_ge_threshold heta.le hExp
  apply pintz_corrected_physical_finite_density heta hetaUpper hBasic
    hlambda hLambdaHeight
    (pintzAdaptiveSeparation_ge_three (eta := eta) hc hBase)
  · exact pintz_physical_contour_error_le_quarter
      hc heta hetaUpper hErrorHeight hetaAbove
  · exact pintz_off_diagonal_absorption hc heta (by linarith)
      hBase hCoreHeight hetaAbove

#print axioms eventually_two_pintzDensityLambda_le_height
#print axioms pintz_physical_finite_density_native

end

end GafniTao
