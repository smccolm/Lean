import GafniTao.HeathBrownUniformMixedSourceOutput
import GafniTao.RealEnergyDiscretization

/-!
# Uniform mixed-to-self source reduction

This is the exact four-coordinate reduction for the repaired uniform source
output.  All detector-colour, local-multiplicity, and doubled-floor losses
remain literal.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

noncomputable def heathBrownUniformMixedSelectionLoss
    {sigma delta delta1 delta2 eta epsilon C0 C2 C4 : Real}
    {U0 U1 U2 U3 : Real}
    {d0 : ClassicalBinaryShellDetectorData sigma U0 delta
      (Nat.floor (U0 ^ delta1)) (Nat.floor (U0 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U0)) (U0 ^ (-delta2))}
    {d1 : ClassicalBinaryShellDetectorData sigma U1 delta
      (Nat.floor (U1 ^ delta1)) (Nat.floor (U1 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U1)) (U1 ^ (-delta2))}
    {d2 : ClassicalBinaryShellDetectorData sigma U2 delta
      (Nat.floor (U2 ^ delta1)) (Nat.floor (U2 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U2)) (U2 ^ (-delta2))}
    {d3 : ClassicalBinaryShellDetectorData sigma U3 delta
      (Nat.floor (U3 ^ delta1)) (Nat.floor (U3 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U3)) (U3 ^ (-delta2))}
    (_output : HeathBrownUniformMixedSourceOutput sigma delta delta1
      delta2 eta epsilon C0 C2 C4 U0 U1 U2 U3 d0 d1 d2 d3) : Nat :=
  (((d0.kI * 2 + d0.kII * 2) * 2) *
    ((d1.kI * 2 + d1.kII * 2) * 2) *
    ((d2.kI * 2 + d2.kII * 2) * 2) *
    ((d3.kI * 2 + d3.kII * 2) * 2)) *
  (((2 * Nat.ceil (U0 ^ delta + 1) + 1) * sharpShellLocalMultiplicityCap U0) *
    ((2 * Nat.ceil (U1 ^ delta + 1) + 1) * sharpShellLocalMultiplicityCap U1) *
    ((2 * Nat.ceil (U2 ^ delta + 1) + 1) * sharpShellLocalMultiplicityCap U2) *
    ((2 * Nat.ceil (U3 ^ delta + 1) + 1) * sharpShellLocalMultiplicityCap U3)) *
  (doubleFloorDefectWindow
    (5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta)).card

theorem HeathBrownUniformMixedSourceOutput.energy_le_sum_self
    {sigma delta delta1 delta2 eta epsilon C0 C2 C4 : Real}
    {U0 U1 U2 U3 : Real}
    {d0 : ClassicalBinaryShellDetectorData sigma U0 delta
      (Nat.floor (U0 ^ delta1)) (Nat.floor (U0 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U0)) (U0 ^ (-delta2))}
    {d1 : ClassicalBinaryShellDetectorData sigma U1 delta
      (Nat.floor (U1 ^ delta1)) (Nat.floor (U1 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U1)) (U1 ^ (-delta2))}
    {d2 : ClassicalBinaryShellDetectorData sigma U2 delta
      (Nat.floor (U2 ^ delta1)) (Nat.floor (U2 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U2)) (U2 ^ (-delta2))}
    {d3 : ClassicalBinaryShellDetectorData sigma U3 delta
      (Nat.floor (U3 ^ delta1)) (Nat.floor (U3 ^ (delta2 / 2)))
      (Nat.floor (sharpZetaCutoff U3)) (U3 ^ (-delta2))}
    (output : HeathBrownUniformMixedSourceOutput sigma delta delta1 delta2
      eta epsilon C0 C2 C4 U0 U1 U2 U3 d0 d1 d2 d3) :
    4 * (weightedMixedAdditiveEnergyOn
        (absoluteDyadicZeroSlab sigma U0)
        (absoluteDyadicZeroSlab sigma U1)
        (absoluteDyadicZeroSlab sigma U2)
        (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 : Real) ≤
      (heathBrownUniformMixedSelectionLoss output : Real) *
        ((ApproxAddEnergy 1 (classicalBinaryColorFamily d0 output.label0) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d1 output.label1) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d2 output.label2) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d3 output.label3) : Real)) := by
  let Q : Nat :=
    (((d0.kI * 2 + d0.kII * 2) * 2) *
      ((d1.kI * 2 + d1.kII * 2) * 2) *
      ((d2.kI * 2 + d2.kII * 2) * 2) *
      ((d3.kI * 2 + d3.kII * 2) * 2)) *
    (((2 * Nat.ceil (U0 ^ delta + 1) + 1) * sharpShellLocalMultiplicityCap U0) *
      ((2 * Nat.ceil (U1 ^ delta + 1) + 1) * sharpShellLocalMultiplicityCap U1) *
      ((2 * Nat.ceil (U2 ^ delta + 1) + 1) * sharpShellLocalMultiplicityCap U2) *
      ((2 * Nat.ceil (U3 ^ delta + 1) + 1) * sharpShellLocalMultiplicityCap U3))
  let D : Real := 5 + U0 ^ delta + U1 ^ delta + U2 ^ delta + U3 ^ delta
  have hExtract :
      (weightedMixedAdditiveEnergyOn
          (absoluteDyadicZeroSlab sigma U0)
          (absoluteDyadicZeroSlab sigma U1)
          (absoluteDyadicZeroSlab sigma U2)
          (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 : Real) ≤
        (Q : Real) *
          (MixedApproxAddEnergy D
            (classicalBinaryColorFamily d0 output.label0)
            (classicalBinaryColorFamily d1 output.label1)
            (classicalBinaryColorFamily d2 output.label2)
            (classicalBinaryColorFamily d3 output.label3) : Real) := by
    exact_mod_cast output.energy_le
  have hMixed := four_mul_mixedApproxAddEnergy_le_window_mul_sum_self
    (eta := D) output.separated0 output.separated1
      output.separated2 output.separated3
  calc
    4 * (weightedMixedAdditiveEnergyOn
        (absoluteDyadicZeroSlab sigma U0)
        (absoluteDyadicZeroSlab sigma U1)
        (absoluteDyadicZeroSlab sigma U2)
        (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 : Real) ≤
      4 * ((Q : Real) *
        (MixedApproxAddEnergy D
          (classicalBinaryColorFamily d0 output.label0)
          (classicalBinaryColorFamily d1 output.label1)
          (classicalBinaryColorFamily d2 output.label2)
          (classicalBinaryColorFamily d3 output.label3) : Real)) := by gcongr
    _ = (Q : Real) *
        (4 * (MixedApproxAddEnergy D
          (classicalBinaryColorFamily d0 output.label0)
          (classicalBinaryColorFamily d1 output.label1)
          (classicalBinaryColorFamily d2 output.label2)
          (classicalBinaryColorFamily d3 output.label3) : Real)) := by ring
    _ ≤ (Q : Real) * (doubleFloorDefectWindow D).card *
        ((ApproxAddEnergy 1 (classicalBinaryColorFamily d0 output.label0) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d1 output.label1) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d2 output.label2) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d3 output.label3) : Real)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hMixed (by positivity)
    _ = (heathBrownUniformMixedSelectionLoss output : Real) *
        ((ApproxAddEnergy 1 (classicalBinaryColorFamily d0 output.label0) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d1 output.label1) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d2 output.label2) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d3 output.label3) : Real)) := by
      simp only [heathBrownUniformMixedSelectionLoss, Q, D, Nat.cast_mul]

#print axioms HeathBrownUniformMixedSourceOutput.energy_le_sum_self

end

end GafniTao
