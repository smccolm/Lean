import GafniTao.HeathBrownUniformPoweredEnergy
import GafniTao.HeathBrownFiniteSelfElimination

/-!
# Scalar elimination for uniform powered outputs

The self-energy and cardinality eliminations are identical to the packet
version, but no height-threshold premise remains: it was discharged when the
uniform output was constructed.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem HeathBrownUniformPoweredEnergyOutput.energy_le_scalar
    {epsilon B R : Real} {N p : Nat} {eta L : Real}
    {W : Finset Real} {a : Nat → Complex} {C0 C2 C4 : Real}
    (output : HeathBrownUniformPoweredEnergyOutput
      epsilon B R N p eta L W a C0 C2 C4)
    (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2) (hC4 : 0 ≤ C4)
    (hB : 0 ≤ B) (hSep : IsSeparated 1 W) {R0 : Real}
    (hCard : (W.card : Real) ≤ R0) :
    4 * (ApproxAddEnergy 1 W : Real) ≤
      ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
        (4 * heathBrownFiniteScalarBound epsilon C0 C2 C4 B
          (heathBrownPoweredThreshold N p L output.Cp eta)
          ((2 ^ p * N ^ p : Nat) : Real) R0) := by
  have hOutput := output.energy_le_common_power hC0 hC2 hC4 hB
  have hFamily := heathBrownFiniteFamilyBound_le_scalar
    (epsilon := epsilon) (C0 := C0) (C2 := C2) (C4 := C4) (B := B)
    (V := heathBrownPoweredThreshold N p L output.Cp eta)
    (M := 2 ^ p * N ^ p) (W := W) hC0 hC4 hB hSep
  have hScalar := heathBrownFiniteScalarBound_mono
    (epsilon := epsilon) (C0 := C0) (C2 := C2) (C4 := C4) (B := B)
    (V := heathBrownPoweredThreshold N p L output.Cp eta)
    hC0 hC2 hC4 hB (Nat.cast_nonneg (2 ^ p * N ^ p))
    (Nat.cast_nonneg W.card) (le_refl ((2 ^ p * N ^ p : Nat) : Real)) hCard
  have hFactor : 0 ≤
      ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card := by
    positivity
  calc
    4 * (ApproxAddEnergy 1 W : Real) ≤
        ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
          (4 * heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
            (heathBrownPoweredThreshold N p L output.Cp eta)
            (2 ^ p * N ^ p) W) := hOutput
    _ ≤ ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
          (4 * heathBrownFiniteScalarBound epsilon C0 C2 C4 B
            (heathBrownPoweredThreshold N p L output.Cp eta)
            ((2 ^ p * N ^ p : Nat) : Real) (W.card : Real)) := by
      gcongr
    _ ≤ ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
          (4 * heathBrownFiniteScalarBound epsilon C0 C2 C4 B
            (heathBrownPoweredThreshold N p L output.Cp eta)
            ((2 ^ p * N ^ p : Nat) : Real) R0) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hScalar (by norm_num)) hFactor

theorem HeathBrownUniformPoweredEnergyOutput.energy_le_two_cardinality_bounds
    {epsilon B R : Real} {N p : Nat} {eta L : Real}
    {W : Finset Real} {a : Nat → Complex} {C0 C2 C4 : Real}
    (energyOutput : HeathBrownUniformPoweredEnergyOutput
      epsilon B R N p eta L W a C0 C2 C4)
    (cardPacket : HeathBrownPoweredCardinalityPacket B R N p eta L W a)
    (nextPacket : HeathBrownPoweredCardinalityPacket
      B R N (p + 1) eta L W a)
    (hC0 : 0 ≤ C0) (hC2 : 0 ≤ C2) (hC4 : 0 ≤ C4)
    (hB : 0 ≤ B) (hSep : IsSeparated 1 W) :
    4 * (ApproxAddEnergy 1 W : Real) ≤
      ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
        (4 * heathBrownFiniteScalarBound epsilon C0 C2 C4 B
          (heathBrownPoweredThreshold N p L energyOutput.Cp eta)
          ((2 ^ p * N ^ p : Nat) : Real)
          (min cardPacket.bound nextPacket.bound)) := by
  apply energyOutput.energy_le_scalar hC0 hC2 hC4 hB hSep
  exact le_min cardPacket.card_le_bound nextPacket.card_le_bound

#print axioms HeathBrownUniformPoweredEnergyOutput.energy_le_scalar
#print axioms HeathBrownUniformPoweredEnergyOutput.energy_le_two_cardinality_bounds

end

end GafniTao
