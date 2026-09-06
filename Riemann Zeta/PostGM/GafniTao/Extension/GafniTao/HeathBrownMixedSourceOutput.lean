import GafniTao.MixedClassicalBinaryShellExtraction
import GafniTao.HeathBrownSourceColorOutput

/-!
# Four-coordinate source output

This file combines the literal four-shell detector extraction with the
source-cutoff Heath--Brown alternative.  The four dyadic lengths and all four
detector labels remain independent.  Empty selected colours are handled by
the implication in each output field rather than by inventing a dummy
analytic packet.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The exact output of applying the source detector to four possibly
different absolute dyadic slabs. -/
structure HeathBrownMixedSourceOutput
    (sigma delta delta1 delta2 eta epsilon : Real)
    (U0 U1 U2 U3 : Real)
    (d0 : ClassicalBinaryShellDetectorData sigma U0 delta
      (Nat.floor (U0 ^ delta1)) (Nat.floor (U0 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U0)) (U0 ^ (-delta2)))
    (d1 : ClassicalBinaryShellDetectorData sigma U1 delta
      (Nat.floor (U1 ^ delta1)) (Nat.floor (U1 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U1)) (U1 ^ (-delta2)))
    (d2 : ClassicalBinaryShellDetectorData sigma U2 delta
      (Nat.floor (U2 ^ delta1)) (Nat.floor (U2 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U2)) (U2 ^ (-delta2)))
    (d3 : ClassicalBinaryShellDetectorData sigma U3 delta
      (Nat.floor (U3 ^ delta1)) (Nat.floor (U3 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U3)) (U3 ^ (-delta2))) where
  label0 : Fin (d0.kI * 2 + d0.kII * 2) × Fin 2
  label1 : Fin (d1.kI * 2 + d1.kII * 2) × Fin 2
  label2 : Fin (d2.kI * 2 + d2.kII * 2) × Fin 2
  label3 : Fin (d3.kI * 2 + d3.kII * 2) × Fin 2
  separated0 : IsSeparated 1 (classicalBinaryColorFamily d0 label0)
  separated1 : IsSeparated 1 (classicalBinaryColorFamily d1 label1)
  separated2 : IsSeparated 1 (classicalBinaryColorFamily d2 label2)
  separated3 : IsSeparated 1 (classicalBinaryColorFamily d3 label3)
  energy_le :
    weightedMixedAdditiveEnergyOn
        (absoluteDyadicZeroSlab sigma U0)
        (absoluteDyadicZeroSlab sigma U1)
        (absoluteDyadicZeroSlab sigma U2)
        (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 ≤
      (((d0.kI * 2 + d0.kII * 2) * 2) *
        ((d1.kI * 2 + d1.kII * 2) * 2) *
        ((d2.kI * 2 + d2.kII * 2) * 2) *
        ((d3.kI * 2 + d3.kII * 2) * 2)) *
        (((2 * ⌈U0 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U0) *
          ((2 * ⌈U1 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U1) *
          ((2 * ⌈U2 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U2) *
          ((2 * ⌈U3 ^ delta + 1⌉₊ + 1) * sharpShellLocalMultiplicityCap U3)) *
        MixedApproxAddEnergy
          (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)
          (classicalBinaryColorFamily d0 label0)
          (classicalBinaryColorFamily d1 label1)
          (classicalBinaryColorFamily d2 label2)
          (classicalBinaryColorFamily d3 label3)
  output0 : (classicalBinaryColorFamily d0 label0).Nonempty →
    Nonempty (HeathBrownSourceColorOutput
      sigma U0 delta delta1 delta2 eta epsilon d0 label0)
  output1 : (classicalBinaryColorFamily d1 label1).Nonempty →
    Nonempty (HeathBrownSourceColorOutput
      sigma U1 delta delta1 delta2 eta epsilon d1 label1)
  output2 : (classicalBinaryColorFamily d2 label2).Nonempty →
    Nonempty (HeathBrownSourceColorOutput
      sigma U2 delta delta1 delta2 eta epsilon d2 label2)
  output3 : (classicalBinaryColorFamily d3 label3).Nonempty →
    Nonempty (HeathBrownSourceColorOutput
      sigma U3 delta delta1 delta2 eta epsilon d3 label3)

/-- Uniform four-coordinate source output.  This theorem consumes the actual
four-coordinate pigeonhole result, and then applies the actual source
alternative to each selected colour. -/
theorem eventually_heathBrownMixedSourceOutput
    {sigma delta delta1 delta2 eta epsilon : Real}
    (hsigma : 0 ≤ sigma) (hdelta : delta < 1)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 ≤ delta1)
    (hdelta1Upper : delta1 ≤ 1)
    (hCube : 3 * (delta1 + delta2 / 2) ≤ 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ Ubase : Real, 8 ≤ Ubase ∧
      ∀ U0 U1 U2 U3 : Real,
        Ubase ≤ U0 → Ubase ≤ U1 → Ubase ≤ U2 → Ubase ≤ U3 →
        ∀ (d0 : ClassicalBinaryShellDetectorData sigma U0 delta
          (Nat.floor (U0 ^ delta1)) (Nat.floor (U0 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U0)) (U0 ^ (-delta2)))
          (d1 : ClassicalBinaryShellDetectorData sigma U1 delta
          (Nat.floor (U1 ^ delta1)) (Nat.floor (U1 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U1)) (U1 ^ (-delta2)))
          (d2 : ClassicalBinaryShellDetectorData sigma U2 delta
          (Nat.floor (U2 ^ delta1)) (Nat.floor (U2 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U2)) (U2 ^ (-delta2)))
          (d3 : ClassicalBinaryShellDetectorData sigma U3 delta
          (Nat.floor (U3 ^ delta1)) (Nat.floor (U3 ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U3)) (U3 ^ (-delta2))),
          Nonempty (HeathBrownMixedSourceOutput
            sigma delta delta1 delta2 eta epsilon U0 U1 U2 U3
            d0 d1 d2 d3) := by
  obtain ⟨Ubase, hUbase, hOutput⟩ :=
    eventually_heathBrownSourceColorOutput hsigma hdelta hdelta1 hdelta2
      hdeltaOrder hdelta1Upper hCube heta hepsilon
  refine ⟨Ubase, hUbase, ?_⟩
  intro U0 U1 U2 U3 hU0 hU1 hU2 hU3 d0 d1 d2 d3
  obtain ⟨label0, label1, label2, label3, hExtract⟩ :=
    mixed_absoluteSlabs_classical_binary_detector_extraction
      sigma delta U0 U1 U2 U3
      (Nat.floor (U0 ^ delta1)) (Nat.floor (U0 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U0))
      (Nat.floor (U1 ^ delta1)) (Nat.floor (U1 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U1))
      (Nat.floor (U2 ^ delta1)) (Nat.floor (U2 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U2))
      (Nat.floor (U3 ^ delta1)) (Nat.floor (U3 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U3))
      (U0 ^ (-delta2)) (U1 ^ (-delta2))
      (U2 ^ (-delta2)) (U3 ^ (-delta2))
      d0 d1 d2 d3 (by linarith) (by linarith) (by linarith) (by linarith)
  dsimp only at hExtract
  rcases hExtract with
    ⟨hSep0, hSep1, hSep2, hSep3, _hLarge0, _hLarge1, _hLarge2,
      _hLarge3, _hCard0, _hCard1, _hCard2, _hCard3, hEnergy⟩
  refine ⟨⟨label0, label1, label2, label3,
    hSep0, hSep1, hSep2, hSep3,
    ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [classicalBinaryColorFamily] using hEnergy
  · exact fun hW => hOutput U0 hU0 d0 label0 hW
  · exact fun hW => hOutput U1 hU1 d1 label1 hW
  · exact fun hW => hOutput U2 hU2 d2 label2 hW
  · exact fun hW => hOutput U3 hU3 d3 label3 hW

#print axioms eventually_heathBrownMixedSourceOutput

end

end GafniTao
