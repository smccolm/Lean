import GafniTao.MixedClassicalBinaryShellExtraction
import GafniTao.ClassicalBinaryUniformSourceAlternative

/-!
# Four-coordinate uniform source output

The four dyadic zero shells select detector colours independently.  This
module combines their genuine mixed-energy extraction with the repaired
uniform source alternative for each nonempty colour.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Four independently selected source colours carrying fully consumed
uniform Heath--Brown outputs. -/
structure HeathBrownUniformMixedSourceOutput
    (sigma delta delta1 delta2 eta epsilon C0 C2 C4 : Real)
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
    Nonempty (HeathBrownUniformSourceColorOutput sigma U0 delta delta1
      delta2 eta epsilon C0 C2 C4 d0 label0)
  output1 : (classicalBinaryColorFamily d1 label1).Nonempty →
    Nonempty (HeathBrownUniformSourceColorOutput sigma U1 delta delta1
      delta2 eta epsilon C0 C2 C4 d1 label1)
  output2 : (classicalBinaryColorFamily d2 label2).Nonempty →
    Nonempty (HeathBrownUniformSourceColorOutput sigma U2 delta delta1
      delta2 eta epsilon C0 C2 C4 d2 label2)
  output3 : (classicalBinaryColorFamily d3 label3).Nonempty →
    Nonempty (HeathBrownUniformSourceColorOutput sigma U3 delta delta1
      delta2 eta epsilon C0 C2 C4 d3 label3)

/-- Uniform four-coordinate source output with common finite-relation
constants. -/
theorem eventually_heathBrownUniformMixedSourceOutput
    {sigma delta delta1 delta2 eta epsilon : Real}
    (hsigma : 0 ≤ sigma) (hdelta : delta < 1)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 ≤ delta1)
    (hdelta1Upper : delta1 ≤ 1)
    (hCube : 3 * (delta1 + delta2 / 2) ≤ 1)
    (heta : 0 < eta) (hepsilon : 0 < epsilon) :
    ∃ C0 C2 C4 B0 Ubase : Real,
      0 < C0 ∧ 0 < C2 ∧ 0 < C4 ∧ 1 ≤ B0 ∧ 8 ≤ Ubase ∧
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
          Nonempty (HeathBrownUniformMixedSourceOutput sigma delta delta1
            delta2 eta epsilon C0 C2 C4 U0 U1 U2 U3 d0 d1 d2 d3) := by
  obtain ⟨C0, C2, C4, B0, Ubase, hC0, hC2, hC4, hB0,
      hUbase, hOutput⟩ :=
    eventually_heathBrownUniformSourceColorOutput hsigma hdelta hdelta1
      hdelta2 hdeltaOrder hdelta1Upper hCube heta hepsilon
  refine ⟨C0, C2, C4, B0, Ubase, hC0, hC2, hC4, hB0, hUbase, ?_⟩
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
    hSep0, hSep1, hSep2, hSep3, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [classicalBinaryColorFamily] using hEnergy
  · exact fun hW => hOutput U0 hU0 d0 label0 hW
  · exact fun hW => hOutput U1 hU1 d1 label1 hW
  · exact fun hW => hOutput U2 hU2 d2 label2 hW
  · exact fun hW => hOutput U3 hU3 d3 label3 hW

#print axioms HeathBrownUniformMixedSourceOutput
#print axioms eventually_heathBrownUniformMixedSourceOutput

end

end GafniTao
