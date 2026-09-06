import GafniTao.HeathBrownTunedPhysicalCells
import GafniTao.HeathBrownMixedSelectionLossBound

/-!
# Uniform tuned envelope for an actual source color

The two literal logarithmic reassembly factors and both physical majorants
are absorbed here.  The conclusion still quantifies over, and consumes, the
actual source-color output.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem eventually_tuned_actual_source_color_energy_envelope
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
        {label : Fin (D.kI * 2 + D.kII * 2)}
        {sign : Fin 2}
        (_out : HeathBrownFullyUniformSourceColorOutput sigma U
          (heathBrownTuneD sigma epsilon)
          (heathBrownTuneDelta1 sigma)
          (heathBrownTuneDelta2 sigma epsilon)
          (heathBrownTuneEta sigma epsilon)
          (heathBrownTuneDetectorEpsilon sigma epsilon)
          K C Cp Cmv C0 C2 C4 D (label, sign)),
        (classicalBinaryColorFamily D (label, sign)).Nonempty ->
        (ApproxAddEnergy 1 (classicalBinaryColorFamily D (label, sign)) : Real) <=
          U ^ (max (heathBrownLowFirstSlope sigma)
            (heathBrownLowSecondSlope sigma) + epsilon / 3) := by
  have hCell := eventually_tuned_actual_source_color_physical_low_cells
    (K := K) hsigma hsigmaUpper hepsilon hC hCp hCmv hC0 hC2 hC4
  have hPhysical := eventually_heathBrown_physical_majorants_le
    (sigma := sigma)
    (d := heathBrownTuneD sigma epsilon)
    (zetaExtract := heathBrownTuneExtract sigma epsilon)
    (sigma0 := heathBrownTuneSigma0 sigma epsilon)
    (zetaRel := heathBrownTuneRel sigma epsilon)
    (zetaCard := heathBrownTuneCard sigma epsilon)
    (zetaFixed := heathBrownTuneFixed sigma epsilon)
    (eta := heathBrownTuneEta sigma epsilon)
    (zetaShell := heathBrownTuneShell sigma epsilon)
    (zetaConst := heathBrownTuneConst sigma epsilon)
    (zetaDil := heathBrownTuneDil sigma epsilon)
    (delta2 := heathBrownTuneDelta2 sigma epsilon)
    (Pcap := heathBrownTuneP sigma epsilon)
    (by
      have hq := heathBrownTuneQ_pos hsigma hepsilon
      unfold heathBrownTuneFixed
      linarith)
  have hReassembly := eventually_heathBrown_reassembly_factors_le_rpow
    (heathBrownTuneD_pos hsigma hepsilon)
  have hExponent := heathBrownTune_physical_exponents_le
    hsigma hsigmaUpper hepsilon
  have hdBound : 2 * heathBrownTuneD sigma epsilon + epsilon / 4 <=
      epsilon / 3 := by
    have hqEpsilon := heathBrownTuneQ_le_epsilon
      (sigma := sigma) (epsilon := epsilon)
    have hqPos := heathBrownTuneQ_pos hsigma hepsilon
    have hgap := heathBrownTuneGap_le_quarter hsigmaUpper
    have hd : heathBrownTuneD sigma epsilon <=
        heathBrownTuneQ sigma epsilon / 4000 := by
      unfold heathBrownTuneD
      nlinarith
    nlinarith
  filter_upwards [hCell, hPhysical, hReassembly,
      eventually_ge_atTop (1 : Real)] with U hCellU hPhysicalU hFactors hU
  intro D label sign out hNonempty
  have hRaw := hCellU out hNonempty
  have hMajorant := hPhysicalU
  have hUPos : 0 < U := zero_lt_one.trans_le hU
  have hSourceNonneg : 0 <= heathBrownSourceReassemblyFactor U := by
    unfold heathBrownSourceReassemblyFactor
    positivity
  have hLongNonneg : 0 <= heathBrownLongTailReassemblyFactor U := by
    unfold heathBrownLongTailReassemblyFactor
    positivity
  have hFactorsProduct :
      heathBrownLongTailReassemblyFactor U *
          heathBrownSourceReassemblyFactor U <=
        U ^ (2 * heathBrownTuneD sigma epsilon) := by
    calc
      heathBrownLongTailReassemblyFactor U *
          heathBrownSourceReassemblyFactor U <=
        U ^ heathBrownTuneD sigma epsilon *
          U ^ heathBrownTuneD sigma epsilon := by
        exact mul_le_mul hFactors.2 hFactors.1 hSourceNonneg
          (Real.rpow_nonneg hUPos.le _)
      _ = U ^ (2 * heathBrownTuneD sigma epsilon) := by
        rw [← Real.rpow_add hUPos]
        congr 1
        ring
  calc
    (ApproxAddEnergy 1 (classicalBinaryColorFamily D (label, sign)) : Real) <=
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
              (heathBrownTuneDelta2 sigma epsilon)) := hRaw
    _ <= U ^ (2 * heathBrownTuneD sigma epsilon) *
        U ^ max
          (heathBrownTypeIEnvelopeExponent
            (heathBrownTuneD sigma epsilon)
            (heathBrownTuneExtract sigma epsilon)
            (heathBrownTuneSigma0 sigma epsilon)
            (heathBrownTuneRel sigma epsilon)
            (heathBrownTuneCard sigma epsilon)
            (heathBrownTuneFixed sigma epsilon))
          (heathBrownTypeIIEnvelopeExponent sigma
            (heathBrownTuneEta sigma epsilon)
            (heathBrownTuneShell sigma epsilon)
            (heathBrownTuneConst sigma epsilon)
            (heathBrownTuneDil sigma epsilon)
            (heathBrownTuneRel sigma epsilon)
            (heathBrownTuneCard sigma epsilon)
            (heathBrownTuneDelta2 sigma epsilon)
            (heathBrownTuneFixed sigma epsilon)) := by
      have hMajorantNonneg : 0 <=
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
        unfold heathBrownTypeIPhysicalMajorant
          heathBrownTypeIIPhysicalMajorant
        positivity
      exact mul_le_mul hFactorsProduct hMajorant hMajorantNonneg
        (Real.rpow_nonneg hUPos.le _)
    _ = U ^ (2 * heathBrownTuneD sigma epsilon +
        max
          (heathBrownTypeIEnvelopeExponent
            (heathBrownTuneD sigma epsilon)
            (heathBrownTuneExtract sigma epsilon)
            (heathBrownTuneSigma0 sigma epsilon)
            (heathBrownTuneRel sigma epsilon)
            (heathBrownTuneCard sigma epsilon)
            (heathBrownTuneFixed sigma epsilon))
          (heathBrownTypeIIEnvelopeExponent sigma
            (heathBrownTuneEta sigma epsilon)
            (heathBrownTuneShell sigma epsilon)
            (heathBrownTuneConst sigma epsilon)
            (heathBrownTuneDil sigma epsilon)
            (heathBrownTuneRel sigma epsilon)
            (heathBrownTuneCard sigma epsilon)
            (heathBrownTuneDelta2 sigma epsilon)
            (heathBrownTuneFixed sigma epsilon))) := by
      rw [Real.rpow_add hUPos]
    _ <= U ^ (max (heathBrownLowFirstSlope sigma)
          (heathBrownLowSecondSlope sigma) + epsilon / 3) := by
      apply Real.rpow_le_rpow_of_exponent_le hU
      linarith

#print axioms eventually_tuned_actual_source_color_energy_envelope

end

end GafniTao
