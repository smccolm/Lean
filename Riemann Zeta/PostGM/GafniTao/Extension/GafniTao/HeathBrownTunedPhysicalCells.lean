import GafniTao.HeathBrownActualSourceColorPhysicalCells
import GafniTao.HeathBrownLowParameterAlgebra

/-!
# The explicit selector applied to the actual Heath--Brown source colors

This theorem consumes `HeathBrownFullyUniformSourceColorOutput` itself.  It
therefore closes the finite-parameter side conditions for the real classified
Type-I/Type-II alternatives rather than proving a detached optimization fact.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem eventually_tuned_actual_source_color_physical_low_cells
    {sigma epsilon K C Cp Cmv C0 C2 C4 : Real}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma <= 3 / 4)
    (hepsilon : 0 < epsilon)
    (hC : 0 < C) (hCp : 0 < Cp) (hCmv : 0 < Cmv)
    (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4) :
    ∀ᶠ U : Real in atTop,
      ∀ {D : ClassicalBinaryShellDetectorData sigma U
          (heathBrownTuneD sigma epsilon)
          (Nat.floor (U ^ heathBrownTuneDelta1 sigma))
          (Nat.floor (U ^ (heathBrownTuneDelta2 sigma epsilon / 2)))
          (Nat.floor (sharpZetaCutoff U))
          (U ^ (-heathBrownTuneDelta2 sigma epsilon))}
        {label : Fin (D.kI * 2 + D.kII * 2) × Fin 2}
        (_out : HeathBrownFullyUniformSourceColorOutput sigma U
          (heathBrownTuneD sigma epsilon)
          (heathBrownTuneDelta1 sigma)
          (heathBrownTuneDelta2 sigma epsilon)
          (heathBrownTuneEta sigma epsilon)
          (heathBrownTuneDetectorEpsilon sigma epsilon)
          K C Cp Cmv C0 C2 C4 D label),
        (classicalBinaryColorFamily D label).Nonempty ->
        (ApproxAddEnergy 1 (classicalBinaryColorFamily D label) : Real) <=
          (heathBrownLongTailReassemblyFactor U *
            heathBrownSourceReassemblyFactor U) *
            max
              (heathBrownTypeIPhysicalMajorant sigma U
                (heathBrownTuneD sigma epsilon)
                (heathBrownTuneExtract sigma epsilon)
                (heathBrownTuneSigma0 sigma epsilon)
                (heathBrownTuneRel sigma epsilon)
                (heathBrownTuneCard sigma epsilon)
                (heathBrownTuneP sigma epsilon))
              (heathBrownTypeIIPhysicalMajorant sigma U
                (heathBrownTuneEta sigma epsilon)
                (heathBrownTuneShell sigma epsilon)
                (heathBrownTuneConst sigma epsilon)
                (heathBrownTuneDil sigma epsilon)
                (heathBrownTuneRel sigma epsilon)
                (heathBrownTuneCard sigma epsilon)
                (heathBrownTuneDelta2 sigma epsilon)) := by
  have hq := heathBrownTuneQ_pos hsigma hepsilon
  have hd := heathBrownTuneD_pos hsigma hepsilon
  have hdelta1 := heathBrownTuneDelta1_pos hsigma
  have hdelta2 := heathBrownTuneDelta2_pos hsigma hepsilon
  have hTypeII := heathBrownTune_typeII_effective_between
    hsigma hsigmaUpper hepsilon
  apply eventually_actual_source_color_physical_low_cells
    (hsigma := hsigma) (hsigmaUpper := hsigmaUpper)
    (hd := hd)
    (hdGap := heathBrownTuneD_le_gap_div_thousand hsigma hsigmaUpper)
    (hdelta2D := heathBrownTuneDelta2_le_d hsigma hepsilon)
    (huTerminal := by
      simpa only [heathBrownTuneGap] using
        heathBrownTuneDelta2_lt_gap hsigma hsigmaUpper hepsilon)
    (hdelta1 := hdelta1) (hdelta2 := hdelta2)
    (hdelta2Upper := heathBrownTuneDelta2_le_one hsigma hsigmaUpper hepsilon)
    (hdeltaOrder := heathBrownTuneDelta2_half_le_delta1
      hsigma hsigmaUpper hepsilon)
    (hCube := heathBrownTuneCube hsigma hsigmaUpper hepsilon)
    (heta := by unfold heathBrownTuneEta; positivity)
    (hepsilon := by unfold heathBrownTuneDetectorEpsilon; positivity)
    (hzetaLog := by unfold heathBrownTuneLog; positivity)
    (hzetaPower := by unfold heathBrownTunePower; positivity)
    (hzetaScale := heathBrownTuneScale_pos hsigma hepsilon)
    (hzetaScaleUpper := heathBrownTuneScale_lt_two_thirds hsigma hsigmaUpper)
    (hzetaDil := by unfold heathBrownTuneDil; positivity)
    (hzetaRel := by unfold heathBrownTuneRel; positivity)
    (hzetaCard := by unfold heathBrownTuneCard; positivity)
    (hzetaConst := by unfold heathBrownTuneConst; positivity)
    (hRelMargin := heathBrownTune_rel_margin hsigma hepsilon)
    (hWideRelMargin := heathBrownTune_wide_rel_margin
      hsigma hsigmaUpper hepsilon)
    (hPcap := rfl)
    (hC := hC) (hCp := hCp) (hCmv := hCmv)
    (hC0 := hC0) (hC2 := hC2) (hC4 := hC4)
    (hsigma0Lower := heathBrownTuneSigma0_lower hsigma)
    (hsigma0Eff := heathBrownTune_sigma0_le_lower_effective hsigma hepsilon)
    (hsigma0Wide := heathBrownTune_sigma0_le_wide_effective
      hsigma hsigmaUpper hepsilon)
    (hsigma0Upper := heathBrownTuneSigma0_upper hsigma hsigmaUpper hepsilon)
    (hScaleNear := heathBrownTune_scale_near hsigma hsigmaUpper hepsilon)
    (hzetaShell := by unfold heathBrownTuneShell; positivity)
    (hzetaReflect := by unfold heathBrownTuneReflect; positivity)
    (hloss := by unfold heathBrownTuneLoss; positivity)
    (hv := hd)
    (hzetaExtract := by
      unfold heathBrownTuneExtract
      linarith)
    (hBudget := heathBrownTune_reflected_budget hsigma hsigmaUpper hepsilon)
    (hEffective := heathBrownTune_sigma0_le_reflected_effective
      hsigma hsigmaUpper hepsilon)
    (hTypeIILower := hTypeII.1)
    (hTypeIIUpper := hTypeII.2.2.trans hsigmaUpper)

#print axioms eventually_tuned_actual_source_color_physical_low_cells

end

end GafniTao
