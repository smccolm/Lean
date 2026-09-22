import GafniTao.SharpPerronPartialFraction

/-!
# Positive-height logarithmic derivative on the Perron horizontal edge

The local partial-fraction theorem, the good-height spacing, and Jensen's
zero-mass estimate are assembled here into a uniform logarithmic-square bound.
-/

open Complex Set Metric Finset
open RiemannZeta.GuthMaynard
open scoped BigOperators

noncomputable section

namespace GafniTao

noncomputable def sharpLandauPartialFractionConstant : ℝ :=
  16 * (24 / 25 : ℝ) ^ 2 / ((24 / 25 : ℝ) - 19 / 20) ^ 3 +
    1 / (((49 / 50 : ℝ) ^ 2 / (97 / 100 : ℝ) - 97 / 100) *
      Real.log ((49 / 50 : ℝ) / (97 / 100 : ℝ)))

noncomputable def sharpLandauMassConstant : ℝ :=
  202 / Real.log ((49 / 50 : ℝ) / (24 / 25 : ℝ))

theorem sharpLandauPartialFractionConstant_pos :
    0 < sharpLandauPartialFractionConstant := by
  unfold sharpLandauPartialFractionConstant
  have hlog : 0 < Real.log ((49 / 50 : ℝ) / (97 / 100 : ℝ)) := by
    exact Real.log_pos (by norm_num)
  positivity

theorem sharpLandauMassConstant_pos : 0 < sharpLandauMassConstant := by
  unfold sharpLandauMassConstant
  have hlog : 0 < Real.log ((49 / 50 : ℝ) / (24 / 25 : ℝ)) := by
    exact Real.log_pos (by norm_num)
  positivity

theorem log_two_hundred_mul_rpow_le
    {T : ℝ} (hT : 8 ≤ T) :
    Real.log (200 * T ^ (3 : ℝ)) ≤ 202 * Real.log T := by
  have hTPos : 0 < T := by linarith
  have hLogOne : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTPos]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hConst := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 200 by norm_num)
  calc
    Real.log (200 * T ^ (3 : ℝ)) =
        Real.log 200 + Real.log (T ^ (3 : ℝ)) := by
      rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hTPos 3).ne']
    _ = Real.log 200 + 3 * Real.log T := by
      rw [Real.log_rpow hTPos]
    _ ≤ 202 * Real.log T := by nlinarith

theorem sharpLandauZeroMass_le_log
    {T : ℝ} (hT : 8 ≤ T) :
    (sharpLandauZeroMass T hT : ℝ) ≤
      sharpLandauMassConstant * Real.log T := by
  have hden : 0 < Real.log ((49 / 50 : ℝ) / (24 / 25 : ℝ)) := by
    exact Real.log_pos (by norm_num)
  have hmass := sharpLandauZeroMass_le hT
  have hlog := log_two_hundred_mul_rpow_le hT
  calc
    (sharpLandauZeroMass T hT : ℝ) ≤
        1 / Real.log ((49 / 50 : ℝ) / (24 / 25 : ℝ)) *
          Real.log (200 * T ^ (3 : ℝ)) := hmass
    _ ≤ 1 / Real.log ((49 / 50 : ℝ) / (24 / 25 : ℝ)) *
          (202 * Real.log T) :=
      mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = sharpLandauMassConstant * Real.log T := by
      unfold sharpLandauMassConstant
      ring

theorem norm_sharpLandauNormalized_logDeriv_le_raw
    {T σ R : ℝ} (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1)) (hσ : σ ∈ Set.Icc (1 / 2) 2)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    ‖deriv (sharpLandauNormalized T) (sharpLandauCoord T σ R) /
        sharpLandauNormalized T (sharpLandauCoord T σ R)‖ ≤
      sharpLandauPartialFractionConstant *
          Real.log (200 * T ^ (3 : ℝ)) +
        (7 / 2 : ℝ) *
          (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1) *
            sharpLandauZeroMass T hT := by
  let L := deriv (sharpLandauNormalized T) (sharpLandauCoord T σ R) /
    sharpLandauNormalized T (sharpLandauCoord T σ R)
  let Z := ∑ ρ ∈ sharpLandauZeroFinset T hT,
    (analyticOrderNatAt (sharpLandauNormalized T) ρ : ℂ) /
      (sharpLandauCoord T σ R - ρ)
  have hpartial := sharpLandau_partialFraction_bound hT hR hσ hfar
  have hzero := norm_sharpLandau_zeroSum_le (T := T) (σ := σ)
    (R := R) hT hfar
  change ‖L‖ ≤ _
  have htri : ‖L‖ ≤ ‖L - Z‖ + ‖Z‖ := by
    calc
      ‖L‖ = ‖(L - Z) + Z‖ := by ring_nf
      _ ≤ ‖L - Z‖ + ‖Z‖ := norm_add_le _ _
  exact htri.trans (add_le_add hpartial hzero)

/-- Uniform logarithmic-square estimate for the normalized zeta logarithmic
derivative on the selected positive horizontal edge. -/
theorem norm_sharpLandauNormalized_logDeriv_le_log_sq
    {T σ R : ℝ} (hT : 8 ≤ T)
    (hR : R ∈ Set.Icc T (T + 1)) (hσ : σ ∈ Set.Icc (1 / 2) 2)
    (hfar : ∀ ρ ∈ sharpLandauZeroFinset T hT,
      1 / (2 * (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1)) ≤
        |R - (sharpLandauMap T ρ).im|) :
    ‖deriv (sharpLandauNormalized T) (sharpLandauCoord T σ R) /
        sharpLandauNormalized T (sharpLandauCoord T σ R)‖ ≤
      (202 * sharpLandauPartialFractionConstant +
          (7 / 2 : ℝ) * (sharpLandauMassConstant + 1) *
            sharpLandauMassConstant) * Real.log T ^ 2 := by
  have hTPos : 0 < T := by linarith
  have hLogOne : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTPos]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hraw := norm_sharpLandauNormalized_logDeriv_le_raw hT hR hσ hfar
  have hmass := sharpLandauZeroMass_le_log hT
  have hcardNat := sharpLandauZeroOrdinates_card_le_mass hT
  have hcard : ((sharpLandauZeroOrdinates T hT).card : ℝ) ≤
      sharpLandauZeroMass T hT := by exact_mod_cast hcardNat
  have hlog := log_two_hundred_mul_rpow_le hT
  have hmassNonneg : (0 : ℝ) ≤ sharpLandauZeroMass T hT := by positivity
  have hDNonneg : 0 ≤ sharpLandauMassConstant :=
    sharpLandauMassConstant_pos.le
  have hANonneg : 0 ≤ sharpLandauPartialFractionConstant :=
    sharpLandauPartialFractionConstant_pos.le
  calc
    ‖deriv (sharpLandauNormalized T) (sharpLandauCoord T σ R) /
        sharpLandauNormalized T (sharpLandauCoord T σ R)‖ ≤
        sharpLandauPartialFractionConstant *
            Real.log (200 * T ^ (3 : ℝ)) +
          (7 / 2 : ℝ) *
            (((sharpLandauZeroOrdinates T hT).card : ℝ) + 1) *
              sharpLandauZeroMass T hT := hraw
    _ ≤ sharpLandauPartialFractionConstant * (202 * Real.log T) +
          (7 / 2 : ℝ) *
            (sharpLandauZeroMass T hT + 1) *
              sharpLandauZeroMass T hT := by
      gcongr
    _ ≤ sharpLandauPartialFractionConstant * (202 * Real.log T) +
          (7 / 2 : ℝ) *
            (sharpLandauMassConstant * Real.log T + 1) *
              (sharpLandauMassConstant * Real.log T) := by
      gcongr
    _ ≤ (202 * sharpLandauPartialFractionConstant +
          (7 / 2 : ℝ) * (sharpLandauMassConstant + 1) *
            sharpLandauMassConstant) * Real.log T ^ 2 := by
      have hLNonneg : 0 ≤ Real.log T := by linarith
      have hLsq : Real.log T ≤ Real.log T ^ 2 := by nlinarith
      have hfirst :
          sharpLandauPartialFractionConstant * (202 * Real.log T) ≤
            (202 * sharpLandauPartialFractionConstant) * Real.log T ^ 2 := by
        calc
          sharpLandauPartialFractionConstant * (202 * Real.log T) =
              (202 * sharpLandauPartialFractionConstant) * Real.log T := by ring
          _ ≤ (202 * sharpLandauPartialFractionConstant) * Real.log T ^ 2 :=
            mul_le_mul_of_nonneg_left hLsq (by positivity)
      have hplus : sharpLandauMassConstant * Real.log T + 1 ≤
          (sharpLandauMassConstant + 1) * Real.log T := by
        nlinarith
      have hsecond :
          (7 / 2 : ℝ) *
              (sharpLandauMassConstant * Real.log T + 1) *
                (sharpLandauMassConstant * Real.log T) ≤
            ((7 / 2 : ℝ) * (sharpLandauMassConstant + 1) *
              sharpLandauMassConstant) * Real.log T ^ 2 := by
        calc
          (7 / 2 : ℝ) *
                (sharpLandauMassConstant * Real.log T + 1) *
                  (sharpLandauMassConstant * Real.log T) ≤
              (7 / 2 : ℝ) *
                ((sharpLandauMassConstant + 1) * Real.log T) *
                  (sharpLandauMassConstant * Real.log T) := by
            gcongr
          _ = ((7 / 2 : ℝ) * (sharpLandauMassConstant + 1) *
                sharpLandauMassConstant) * Real.log T ^ 2 := by ring
      nlinarith

end GafniTao
