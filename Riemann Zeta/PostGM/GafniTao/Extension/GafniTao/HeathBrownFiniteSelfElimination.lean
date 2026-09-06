import GafniTao.HeathBrownPoweredPacketBounds
import RiemannZeta.GuthMaynard.LargeValuesEnergyFinal

/-!
# Eliminating the finite self-energy from the Heath--Brown shape

The fourth-moment input contains `ApproxAddEnergy 1 W`.  For a genuinely
one-separated family this quantity is at most `3 * |W|^3`.  This file makes
that substitution explicitly and packages the resulting expression as a
monotone scalar function.  It is the finite, non-circular form needed before
passing to logarithmic exponents.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Literal mean-value upper bound stored in a powered cardinality packet. -/
noncomputable def HeathBrownPoweredCardinalityPacket.bound
    {B R : Real} {N p : Nat} {eta L : Real}
    {W : Finset Real} {a : Nat -> Complex}
    (packet : HeathBrownPoweredCardinalityPacket B R N p eta L W a) : Real :=
  p * packet.Cmv *
    (((2 ^ packet.r * N ^ p : Nat) : Real) ^ 2 /
        (heathBrownPoweredThreshold N p L packet.Cp eta) ^ 2 +
      B * ((2 ^ packet.r * N ^ p : Nat) : Real) /
        (heathBrownPoweredThreshold N p L packet.Cp eta) ^ 2)

theorem HeathBrownPoweredCardinalityPacket.card_le_bound
    {B R : Real} {N p : Nat} {eta L : Real}
    {W : Finset Real} {a : Nat -> Complex}
    (packet : HeathBrownPoweredCardinalityPacket B R N p eta L W a) :
    (W.card : Real) <= packet.bound := by
  exact packet.card_le_meanValue

/-- The second-moment polynomial after replacing the family cardinality by a
real upper bound `R`. -/
noncomputable def heathBrownSecondScalarShape
    (B M R : Real) : Real :=
  R ^ 2 * M + R * M ^ 2 + R ^ (5 / 4 : Real) * B ^ (1 / 2 : Real) * M

/-- The fourth-moment polynomial after the exact separated-set estimate
`ApproxAddEnergy 1 W <= 3 * |W|^3`. -/
noncomputable def heathBrownFourthScalarShape
    (B M R : Real) : Real :=
  R ^ 4 * M + 3 * R ^ 3 * M ^ 2 +
    (3 * R ^ 3) ^ (3 / 4 : Real) * R * B ^ (1 / 2 : Real) * M

/-- The resulting non-circular upper bound for one finite family. -/
noncomputable def heathBrownFiniteScalarBound
    (epsilon C0 C2 C4 B V M R : Real) : Real :=
  (C0 * B ^ (epsilon / 2) *
      Real.sqrt (C2 * B ^ (epsilon / 2) *
        heathBrownSecondScalarShape B M R) *
      Real.sqrt (C4 * B ^ (epsilon / 2) *
        heathBrownFourthScalarShape B M R)) / V ^ 2

theorem heathBrownSecondScalarShape_nonneg
    {B M R : Real} (hB : 0 <= B) (hM : 0 <= M) (hR : 0 <= R) :
    0 <= heathBrownSecondScalarShape B M R := by
  unfold heathBrownSecondScalarShape
  positivity

theorem heathBrownFourthScalarShape_nonneg
    {B M R : Real} (hB : 0 <= B) (hM : 0 <= M) (hR : 0 <= R) :
    0 <= heathBrownFourthScalarShape B M R := by
  unfold heathBrownFourthScalarShape
  positivity

theorem heathBrownSecondMomentShape_eq_scalar
    (B : Real) (M : Nat) (W : Finset Real) :
    heathBrownSecondMomentShape B M W =
      heathBrownSecondScalarShape B (M : Real) (W.card : Real) := by
  rfl

/-- Exact removal of the self-energy occurrence from the fourth-moment
shape. -/
theorem heathBrownFourthMomentShape_le_scalar
    {B : Real} {M : Nat} {W : Finset Real}
    (hB : 0 <= B) (hSep : IsSeparated 1 W) :
    heathBrownFourthMomentShape B M W <=
      heathBrownFourthScalarShape B (M : Real) (W.card : Real) := by
  have hEnergyNat : ApproxAddEnergy 1 W <= 3 * W.card ^ 3 :=
    approxAddEnergy_le_three_card_cubed W hSep
  have hEnergy : (ApproxAddEnergy 1 W : Real) <=
      3 * (W.card : Real) ^ 3 := by
    exact_mod_cast hEnergyNat
  have hEnergyPow : (ApproxAddEnergy 1 W : Real) ^ (3 / 4 : Real) <=
      (3 * (W.card : Real) ^ 3) ^ (3 / 4 : Real) :=
    Real.rpow_le_rpow (by positivity) hEnergy (by norm_num)
  unfold heathBrownFourthMomentShape heathBrownFourthScalarShape
  have hRoot : 0 <= B ^ (1 / 2 : Real) := Real.rpow_nonneg hB _
  gcongr

/-- One-family finite Heath--Brown bound with no occurrence of the unknown
self-energy on the right-hand side. -/
theorem heathBrownFiniteFamilyBound_le_scalar
    {epsilon C0 C2 C4 B V : Real} {M : Nat} {W : Finset Real}
    (hC0 : 0 <= C0) (hC4 : 0 <= C4)
    (hB : 0 <= B) (hSep : IsSeparated 1 W) :
    heathBrownFiniteFamilyBound epsilon C0 C2 C4 B V M W <=
      heathBrownFiniteScalarBound epsilon C0 C2 C4 B V
        (M : Real) (W.card : Real) := by
  unfold heathBrownFiniteFamilyBound heathBrownFiniteScalarBound
  apply div_le_div_of_nonneg_right _ (sq_nonneg V)
  have hPow : 0 <= B ^ (epsilon / 2) := Real.rpow_nonneg hB _
  have hSecondNonneg := heathBrownSecondMomentShape_nonneg B M W hB
  have hSecondScalarNonneg := heathBrownSecondScalarShape_nonneg hB
    (Nat.cast_nonneg M) (Nat.cast_nonneg W.card)
  have hFourthNonneg := heathBrownFourthMomentShape_nonneg B M W hB
  have hFourthScalarNonneg := heathBrownFourthScalarShape_nonneg hB
    (Nat.cast_nonneg M) (Nat.cast_nonneg W.card)
  have hSecondEq := heathBrownSecondMomentShape_eq_scalar B M W
  have hFourth := heathBrownFourthMomentShape_le_scalar
    (M := M) (W := W) hB hSep
  rw [hSecondEq]
  gcongr

/-- The scalar family bound is monotone in both the length and the
cardinality variables on the nonnegative cone. -/
theorem heathBrownFiniteScalarBound_mono
    {epsilon C0 C2 C4 B V M M' R R' : Real}
    (hC0 : 0 <= C0) (hC2 : 0 <= C2) (hC4 : 0 <= C4)
    (hB : 0 <= B) (hM : 0 <= M) (hR : 0 <= R)
    (hMM' : M <= M') (hRR' : R <= R') :
    heathBrownFiniteScalarBound epsilon C0 C2 C4 B V M R <=
      heathBrownFiniteScalarBound epsilon C0 C2 C4 B V M' R' := by
  have hM' : 0 <= M' := hM.trans hMM'
  have hR' : 0 <= R' := hR.trans hRR'
  unfold heathBrownFiniteScalarBound
  apply div_le_div_of_nonneg_right _ (sq_nonneg V)
  have hPow : 0 <= B ^ (epsilon / 2) := Real.rpow_nonneg hB _
  have hSecond : heathBrownSecondScalarShape B M R <=
      heathBrownSecondScalarShape B M' R' := by
    unfold heathBrownSecondScalarShape
    have hRpow : R ^ (5 / 4 : Real) <= R' ^ (5 / 4 : Real) :=
      Real.rpow_le_rpow hR hRR' (by norm_num)
    gcongr
  have hFourth : heathBrownFourthScalarShape B M R <=
      heathBrownFourthScalarShape B M' R' := by
    unfold heathBrownFourthScalarShape
    have hInner : 3 * R ^ 3 <= 3 * R' ^ 3 := by gcongr
    have hInnerPow : (3 * R ^ 3) ^ (3 / 4 : Real) <=
        (3 * R' ^ 3) ^ (3 / 4 : Real) :=
      Real.rpow_le_rpow (by positivity) hInner (by norm_num)
    gcongr
  have hSecondNonneg := heathBrownSecondScalarShape_nonneg hB hM hR
  have hSecond'Nonneg := heathBrownSecondScalarShape_nonneg hB hM' hR'
  have hFourthNonneg := heathBrownFourthScalarShape_nonneg hB hM hR
  have hFourth'Nonneg := heathBrownFourthScalarShape_nonneg hB hM' hR'
  gcongr

/-- A powered energy packet, with the self-energy removed and the family
cardinality replaced by any explicit nonnegative upper bound `R0`. -/
theorem HeathBrownPoweredEnergyPacket.energy_le_scalar
    {epsilon B R : Real} {N p : Nat} {eta L : Real}
    {W : Finset Real} {a : Nat -> Complex}
    (packet : HeathBrownPoweredEnergyPacket epsilon B R N p eta L W a)
    (hB : 0 <= B) (hThreshold : packet.B0 <= B)
    (hSep : IsSeparated 1 W) {R0 : Real}
    (hCard : (W.card : Real) <= R0) :
    4 * (ApproxAddEnergy 1 W : Real) <=
      ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
        (4 * heathBrownFiniteScalarBound epsilon packet.C0 packet.C2
          packet.C4 B (heathBrownPoweredThreshold N p L packet.Cp eta)
          ((2 ^ p * N ^ p : Nat) : Real) R0) := by
  have hPacket := packet.energy_le_common_power hB hThreshold
  have hFamily := heathBrownFiniteFamilyBound_le_scalar
    (epsilon := epsilon) (C0 := packet.C0) (C2 := packet.C2)
    (C4 := packet.C4) (B := B)
    (V := heathBrownPoweredThreshold N p L packet.Cp eta)
    (M := 2 ^ p * N ^ p) (W := W)
    packet.hC0.le packet.hC4.le hB hSep
  have hScalar := heathBrownFiniteScalarBound_mono
    (epsilon := epsilon) (C0 := packet.C0) (C2 := packet.C2)
    (C4 := packet.C4) (B := B)
    (V := heathBrownPoweredThreshold N p L packet.Cp eta)
    packet.hC0.le packet.hC2.le packet.hC4.le hB
    (Nat.cast_nonneg (2 ^ p * N ^ p)) (Nat.cast_nonneg W.card)
    (le_refl ((2 ^ p * N ^ p : Nat) : Real)) hCard
  have hFactor : 0 <=
      ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card := by
    positivity
  calc
    4 * (ApproxAddEnergy 1 W : Real) <=
        ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
          (4 * heathBrownFiniteFamilyBound epsilon packet.C0 packet.C2
            packet.C4 B (heathBrownPoweredThreshold N p L packet.Cp eta)
            (2 ^ p * N ^ p) W) := hPacket
    _ <= ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
          (4 * heathBrownFiniteScalarBound epsilon packet.C0 packet.C2
            packet.C4 B (heathBrownPoweredThreshold N p L packet.Cp eta)
            ((2 ^ p * N ^ p : Nat) : Real) (W.card : Real)) := by
      gcongr
    _ <= ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
          (4 * heathBrownFiniteScalarBound epsilon packet.C0 packet.C2
            packet.C4 B (heathBrownPoweredThreshold N p L packet.Cp eta)
            ((2 ^ p * N ^ p : Nat) : Real) R0) := by
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hScalar
        (by norm_num)) hFactor

/-- The exact finite relation obtained from one energy-producing power and
the two consecutive cardinality powers.  The minimum is literal: both
mean-value packets bound the same original family. -/
theorem HeathBrownPoweredEnergyPacket.energy_le_two_cardinality_bounds
    {epsilon B R : Real} {N p : Nat} {eta L : Real}
    {W : Finset Real} {a : Nat -> Complex}
    (energyPacket : HeathBrownPoweredEnergyPacket
      epsilon B R N p eta L W a)
    (cardPacket : HeathBrownPoweredCardinalityPacket
      B R N p eta L W a)
    (nextPacket : HeathBrownPoweredCardinalityPacket
      B R N (p + 1) eta L W a)
    (hB : 0 <= B) (hThreshold : energyPacket.B0 <= B)
    (hSep : IsSeparated 1 W) :
    4 * (ApproxAddEnergy 1 W : Real) <=
      ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
        (4 * heathBrownFiniteScalarBound epsilon energyPacket.C0
          energyPacket.C2 energyPacket.C4 B
          (heathBrownPoweredThreshold N p L energyPacket.Cp eta)
          ((2 ^ p * N ^ p : Nat) : Real)
          (min cardPacket.bound nextPacket.bound)) := by
  apply energyPacket.energy_le_scalar hB hThreshold hSep
  exact le_min cardPacket.card_le_bound nextPacket.card_le_bound

#print axioms heathBrownFourthMomentShape_le_scalar
#print axioms heathBrownFiniteFamilyBound_le_scalar
#print axioms heathBrownFiniteScalarBound_mono
#print axioms HeathBrownPoweredEnergyPacket.energy_le_scalar
#print axioms HeathBrownPoweredEnergyPacket.energy_le_two_cardinality_bounds

end

end GafniTao
