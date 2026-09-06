import GafniTao.HeathBrownFullyUniformMixedSourceOutput
import GafniTao.HeathBrownUniformMixedSelfReduction

/-!
# Fully uniform mixed-to-self reduction

This theorem applies the already audited finite mixed-energy reduction to
the stronger source object.  The loss is kept literally as the loss of the
converted output, so no asymptotic factor is silently discarded.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem HeathBrownFullyUniformMixedSourceOutput.energy_le_sum_self
    {sigma delta delta1 delta2 eta epsilon K C Cp Cmv C0 C2 C4 : Real}
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
    (output : HeathBrownFullyUniformMixedSourceOutput sigma delta delta1
      delta2 eta epsilon K C Cp Cmv C0 C2 C4
      U0 U1 U2 U3 d0 d1 d2 d3)
    (hK : 0 < K) (hC : 0 < C) :
    let old := output.toUniform hK hC
    4 * (weightedMixedAdditiveEnergyOn
        (absoluteDyadicZeroSlab sigma U0)
        (absoluteDyadicZeroSlab sigma U1)
        (absoluteDyadicZeroSlab sigma U2)
        (absoluteDyadicZeroSlab sigma U3) zeroMultiplicity 1 : Real) ≤
      (heathBrownUniformMixedSelectionLoss old : Real) *
        ((ApproxAddEnergy 1 (classicalBinaryColorFamily d0 output.label0) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d1 output.label1) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d2 output.label2) : Real) +
          (ApproxAddEnergy 1 (classicalBinaryColorFamily d3 output.label3) : Real)) := by
  dsimp only
  simpa only [HeathBrownFullyUniformMixedSourceOutput.toUniform] using
    (output.toUniform hK hC).energy_le_sum_self

#print axioms HeathBrownFullyUniformMixedSourceOutput.energy_le_sum_self

end

end GafniTao
