import GafniTao.Pintz2023DetectorEventually

/-!
# Pintz (2023), equation (4.12) at the exact source scales

All three contour errors are discharged uniformly for the high zeros used in
the source argument.  The conclusion retains the individual zero distance.
-/

open Filter

namespace GafniTao

noncomputable section

theorem eventually_exists_pintz2023Equation412_source_detector
    {eta epsilonX epsilonZeta : ℝ} {k ell : ℕ}
    (heta : 0 < eta) (hetaUpper : eta ≤ 1 / 32)
    (hepsilonX : 0 < epsilonX)
    (hepsilonZeta : 0 < epsilonZeta) (hepsilonZetaUpper : epsilonZeta ≤ 1)
    (hkTwo : 2 ≤ k) (hell : 0 < ell)
    (hcutoffExponent : epsilonX / (10 * (ell : ℝ)) ≤ 2 / (k : ℝ))
    (hdecay : pintz2023DetectorExponent eta epsilonX epsilonZeta k ell < 0) :
    ∀ᶠ T : ℝ in atTop,
      ∀ etaJ gamma : ℝ,
        0 < etaJ → etaJ ≤ eta →
        2 * Real.log T < |gamma| → |gamma| ≤ T →
        riemannZeta (pintz2023Rho etaJ gamma) = 0 →
        ∃ u : ℝ, |gamma - u| ≤ 2 * pintz2023SourceLambda T k ∧
          1 / (32 * Real.exp 2 * Real.log (pintz2023SourceLambda T k)) ≤
            ‖pintz2023TruncatedPolynomial
              (pintz2023SourceX T epsilonX ell)
              (pintz2023Cutoff (pintz2023SourceLambda T k))
              (1 - etaJ + 1 / pintz2023SourceLambda T k) u‖ := by
  have hk : 0 < k := lt_of_lt_of_le (by norm_num) hkTwo
  obtain ⟨Cleft, Kremainder, hCleft, hKremainder, hDetector⟩ :=
    exists_pintz2023Equation412_detector_constants
      hepsilonZeta hepsilonZetaUpper
  have hLeft := eventually_pintz2023_left_scale_le_eighth
    hCleft.le heta hepsilonX hepsilonZeta hk hell hdecay
  have hPole := eventually_pintz2023_pole_scale_le_eighth
    heta hetaUpper hepsilonX.le hk hell
  have hRemainder := eventually_pintz2023_remainder_scale_le_eighth
    hKremainder.le hk
  filter_upwards [hLeft, hPole, hRemainder,
    eventually_ge_atTop (Real.exp 1)] with T hLeftT hPoleT hRemainderT hT
  intro etaJ gamma hetaJ hetaJLe hgammaLow hgammaHigh hzero
  have hTPos : 0 < T := (Real.exp_pos 1).trans_le hT
  have hTOne : 1 ≤ T := by
    have hExpOne : 1 ≤ Real.exp 1 := by
      simpa only [Real.exp_zero] using
        (Real.exp_lt_exp.mpr zero_lt_one).le
    exact hExpOne.trans hT
  have hlogOne : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr (Real.exp_pos 1)) (Set.mem_Ioi.mpr hTPos) hT
  have hepsilonExponent : 0 ≤ epsilonX / (10 * (ell : ℝ)) := by
    have hellReal : (0 : ℝ) < ell := by exact_mod_cast hell
    positivity
  have hX : 0 < pintz2023SourceX T epsilonX ell := by
    apply pintz2023SourceX_pos
    exact Real.one_le_rpow hTOne hepsilonExponent
  have hCutoff := pintz2023SourceX_le_cutoff hTOne hcutoffExponent
  have hgammaOne : 1 ≤ |gamma| := by linarith
  have hkReal : (2 : ℝ) ≤ k := by exact_mod_cast hkTwo
  have hLambdaLe : pintz2023SourceLambda T k ≤ Real.log T := by
    unfold pintz2023SourceLambda
    have htwoK : (2 : ℝ) / k ≤ 1 := (div_le_one (by positivity)).2 hkReal
    nlinarith [Real.log_nonneg hTOne]
  have hgammaLambda :
      2 * pintz2023SourceLambda T k ≤ |gamma| := by
    linarith
  have hgammaNe : gamma ≠ 0 := by
    intro hgamma
    subst gamma
    norm_num at hgammaLow
    linarith
  have hleftScale := hLeftT.2.2 etaJ gamma hetaJ hetaJLe hgammaHigh
  have hpoleScale := hPoleT.2.2 gamma hgammaOne hgammaLambda
  exact hDetector (pintz2023SourceX T epsilonX ell) eta etaJ gamma
    (pintz2023SourceLambda T k) hX heta hetaJ hetaJLe hetaUpper
    hLeftT.2.1 hCutoff hzero hgammaNe hleftScale hpoleScale hRemainderT

#print axioms eventually_exists_pintz2023Equation412_source_detector

end

end GafniTao
