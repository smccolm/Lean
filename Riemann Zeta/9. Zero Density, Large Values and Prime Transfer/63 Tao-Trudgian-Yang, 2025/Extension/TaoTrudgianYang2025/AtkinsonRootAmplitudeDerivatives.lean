import TaoTrudgianYang2025.AtkinsonPhaseSecondDerivatives

/-!
# Constructed second-order bounds for the actual normalized source

Every factor is retained: the Mellin power profile, actual band cutoff,
unit Gamma factor, true quadratic Gaussian and nonlinear root phase.
The shared derivative scale is the physical height.
-/

noncomputable section

open Complex Set
open scoped ContDiff

namespace TaoTrudgianYang2025

def atkinsonRootFourierCore (T G L α u : ℝ) : ℂ :=
  ((T ^ (-α) : ℝ) : ℂ) * atkinsonPowerProfile α (u ^ 2) *
    (zetaDivisorBandCutoff T G L (T * u ^ 2) : ℂ) * zetaSquareReflectedGammaPhase T *
      zetaGaussianQuadraticIntegral T G
        (Real.log (T * u ^ 2) - Real.log (T / (2 * Real.pi))) *
          atkinsonPhaseExponential T (atkinsonRootStationaryProfile u)

theorem exists_intervalC2Bound_atkinsonPowerRootProfile (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      IntervalC2Bound (fun u => atkinsonPowerProfile α (u ^ 2)) (1 / 4) 1 C 1 := by
  apply exists_intervalC2Bound_fixed
  intro u hu
  have hu0 : 0 < u := by linarith [hu.1]
  have hw : ContDiff ℝ 2 zetaDivisorWeight :=
    contDiff_zetaDivisorWeight.of_le (le_of_lt (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top 2)))
  have hcast : ContDiff ℝ 2 (fun x : ℝ => (x : ℂ)) := Complex.ofRealCLM.contDiff
  unfold atkinsonPowerProfile zetaMainMellinProfile
  fun_prop (disch := positivity)

theorem exists_intervalC2Bound_atkinsonRootFourierCore (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ T G L : ℝ, 1 ≤ T → 0 < G → G ^ 2 ≤ 2 * T →
      1 ≤ L → 8 * L ≤ G →
      IntervalC2Bound (atkinsonRootFourierCore T G L α) (1 / 4) 1 (C * G * T ^ (-α)) T := by
  obtain ⟨A, hA, hprofile⟩ := exists_intervalC2Bound_atkinsonPowerRootProfile α
  obtain ⟨B, hB, hcutoff⟩ := exists_intervalC2Bound_zetaDivisorBandCutoff_root
  obtain ⟨D, hD, hgaussian⟩ := exists_intervalC2Bound_zetaQuadraticLogGaussian_root
  obtain ⟨E, hE, hphase⟩ := exists_intervalC2Bound_atkinsonRootPhaseExponential
  let K : ℝ := 2 * (1 + 2 * Real.pi * Real.exp 1)
  have hK : 1 ≤ K := by dsimp [K]; have := Real.exp_pos (1 : ℝ); nlinarith [Real.pi_pos]
  refine ⟨1024 * A * B * K ^ 2 * D * E, by positivity, ?_⟩
  intro T G L hT hG hGT hL hwidth
  have hT0 : 0 < T := by linarith
  have hGbound : G ≤ 2 * T := by nlinarith
  have hscale : (1 + 2 * Real.pi * Real.exp 1) * G ≤ K * T := by
    have h := mul_le_mul_of_nonneg_left hGbound
      (show 0 ≤ 1 + 2 * Real.pi * Real.exp 1 by positivity)
    dsimp [K]
    nlinarith
  have hc : IntervalC2Bound
      (fun u => (zetaDivisorBandCutoff T G L (T * u ^ 2) : ℂ))
      (1 / 4) 1 (B * K ^ 2) T :=
    ((hcutoff T G L hT0 hG hL hwidth).mono le_rfl hscale).absorb_scale hK hT0.le
  have ht : IntervalC2Bound (fun _ : ℝ => ((T ^ (-α) : ℝ) : ℂ))
      (1 / 4) 1 (T ^ (-α)) T := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hT0 _)] using
      intervalC2Bound_const ((T ^ (-α) : ℝ) : ℂ) (1 / 4) 1 hT0.le
  have hg : IntervalC2Bound (fun _ : ℝ => zetaSquareReflectedGammaPhase T) (1 / 4) 1 1 T := by
    simpa only [norm_zetaSquareReflectedGammaPhase] using
      intervalC2Bound_const (zetaSquareReflectedGammaPhase T) (1 / 4) 1 hT0.le
  have h := ((((ht.mul (hprofile.mono le_rfl hT)).mul hc).mul hg).mul
    (hgaussian T G hT hG hGT)).mul (hphase T hT)
  convert h using 1
  ring

theorem atkinsonRootFourierCore_eq_weight_phase {T : ℝ} (hT : T ≠ 0)
    (G L α u : ℝ) :
    atkinsonRootFourierCore T G L α u =
      atkinsonPowerWeight T G L α (T * u ^ 2) *
        atkinsonPhaseExponential T (atkinsonRootStationaryProfile u) := by
  have he : T * u ^ 2 / T = u ^ 2 := by field_simp
  unfold atkinsonRootFourierCore atkinsonPowerWeight
  rw [he]

end TaoTrudgianYang2025
