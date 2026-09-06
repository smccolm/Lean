import GafniTao.HeathBrownFiniteMonotone

/-!
# Exact scalar bounds extracted from powered packets

The packet structures retain every selected subfamily.  These theorems
collapse only the finite colouring, translation, and fixed dyadic factors;
the cardinality, energy, threshold, and physical scale remain explicit.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem HeathBrownPoweredCardinalityPacket.card_le_meanValue
    {B R : Real} {N p : Nat} {eta L : Real}
    {W : Finset Real} {a : Nat → Complex}
    (packet : HeathBrownPoweredCardinalityPacket B R N p eta L W a) :
    (W.card : Real) ≤ p * packet.Cmv *
      (((2 ^ packet.r * N ^ p : Nat) : Real) ^ 2 /
          (heathBrownPoweredThreshold N p L packet.Cp eta) ^ 2 +
        B * ((2 ^ packet.r * N ^ p : Nat) : Real) /
          (heathBrownPoweredThreshold N p L packet.Cp eta) ^ 2) := by
  calc
    (W.card : Real) ≤ p * (packet.W'.card : Real) := packet.hCard
    _ ≤ p * (packet.Cmv *
        (((2 ^ packet.r * N ^ p : Nat) : Real) ^ 2 /
            (heathBrownPoweredThreshold N p L packet.Cp eta) ^ 2 +
          B * ((2 ^ packet.r * N ^ p : Nat) : Real) /
            (heathBrownPoweredThreshold N p L packet.Cp eta) ^ 2)) :=
      mul_le_mul_of_nonneg_left packet.hMeanValue (by positivity)
    _ = _ := by ring

/-- Arbitrary-power common-length form of the powered energy packet.  The
literal common length is `2^p * N^p`; no bound on `p` is hidden here. -/
theorem HeathBrownPoweredEnergyPacket.energy_le_common_power
    {epsilon B R : Real} {N p : Nat} {eta L : Real}
    {W : Finset Real} {a : Nat → Complex}
    (packet : HeathBrownPoweredEnergyPacket epsilon B R N p eta L W a)
    (hB : 0 <= B) (hThreshold : packet.B0 <= B) :
    4 * (ApproxAddEnergy 1 W : Real) <=
      ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
        (4 * heathBrownFiniteFamilyBound epsilon packet.C0 packet.C2
          packet.C4 B (heathBrownPoweredThreshold N p L packet.Cp eta)
          (2 ^ p * N ^ p) W) := by
  obtain ⟨label, Wi, hSubset, _hSep, _hBase, _hUnit, _hLarge, hEnergy⟩ :=
    packet.consume hThreshold
  have hEach : forall i : Fin 4,
      heathBrownFiniteFamilyBound epsilon packet.C0 packet.C2 packet.C4 B
          (heathBrownPoweredThreshold N p L packet.Cp eta)
          (2 ^ (label i).val * N ^ p) (Wi i) <=
        heathBrownFiniteFamilyBound epsilon packet.C0 packet.C2 packet.C4 B
          (heathBrownPoweredThreshold N p L packet.Cp eta)
          (2 ^ p * N ^ p) W := by
    intro i
    have hFactor : 2 ^ (label i).val <= 2 ^ p :=
      Nat.pow_le_pow_right (by omega) (label i).isLt.le
    have hLength : 2 ^ (label i).val * N ^ p <= 2 ^ p * N ^ p :=
      Nat.mul_le_mul_right (N ^ p) hFactor
    have hCardT : (Wi i).card <= (gmTranslate R W).card :=
      Finset.card_le_card (hSubset i)
    have hEnergyMono : ApproxAddEnergy 1 (Wi i) <=
        ApproxAddEnergy 1 (gmTranslate R W) :=
      approxAddEnergy_mono_family (hSubset i)
    have hMono := heathBrownFiniteFamilyBound_mono
      (epsilon := epsilon)
      (V := heathBrownPoweredThreshold N p L packet.Cp eta)
      packet.hC0.le packet.hC2.le packet.hC4.le hB hLength
      hCardT hEnergyMono
    simpa only [heathBrownFiniteFamilyBound, heathBrownSecondMomentShape,
      heathBrownFourthMomentShape, card_gmTranslate,
      approxAddEnergy_translate] using hMono
  have hSum :
      (∑ i : Fin 4,
        heathBrownFiniteFamilyBound epsilon packet.C0 packet.C2 packet.C4 B
          (heathBrownPoweredThreshold N p L packet.Cp eta)
          (2 ^ (label i).val * N ^ p) (Wi i)) <=
        4 * heathBrownFiniteFamilyBound epsilon packet.C0 packet.C2
          packet.C4 B (heathBrownPoweredThreshold N p L packet.Cp eta)
          (2 ^ p * N ^ p) W := by
    rw [Fin.sum_univ_four]
    nlinarith [hEach 0, hEach 1, hEach 2, hEach 3]
  exact hEnergy.trans (mul_le_mul_of_nonneg_left hSum (by positivity))

private theorem dyadic_factor_le_eight_of_two_or_three
    {p r : Nat} (hp : p = 2 ∨ p = 3) (hr : r < p) :
    2 ^ r ≤ 8 := by
  rcases hp with rfl | rfl <;> interval_cases r <;> norm_num

/-- All four powered energy colours are bounded by one common finite family
shape at length `8*N^p`.  Translation disappears exactly from the resulting
cardinality and additive-energy terms. -/
theorem HeathBrownPoweredEnergyPacket.energy_le_common
    {epsilon B R : Real} {N p : Nat} {eta L : Real}
    {W : Finset Real} {a : Nat → Complex}
    (packet : HeathBrownPoweredEnergyPacket epsilon B R N p eta L W a)
    (hB : 0 ≤ B) (hThreshold : packet.B0 ≤ B)
    (hp : p = 2 ∨ p = 3) :
    4 * (ApproxAddEnergy 1 W : Real) ≤
      ((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card *
        (4 * heathBrownFiniteFamilyBound epsilon packet.C0 packet.C2
          packet.C4 B (heathBrownPoweredThreshold N p L packet.Cp eta)
          (8 * N ^ p) W) := by
  obtain ⟨label, Wi, hSubset, _hSep, _hBase, _hUnit, _hLarge, hEnergy⟩ :=
    packet.consume hThreshold
  have hEach : ∀ i : Fin 4,
      heathBrownFiniteFamilyBound epsilon packet.C0 packet.C2 packet.C4 B
          (heathBrownPoweredThreshold N p L packet.Cp eta)
          (2 ^ (label i).val * N ^ p) (Wi i) ≤
        heathBrownFiniteFamilyBound epsilon packet.C0 packet.C2 packet.C4 B
          (heathBrownPoweredThreshold N p L packet.Cp eta)
          (8 * N ^ p) W := by
    intro i
    have hFactor : 2 ^ (label i).val ≤ 8 :=
      dyadic_factor_le_eight_of_two_or_three hp (label i).isLt
    have hLength : 2 ^ (label i).val * N ^ p ≤ 8 * N ^ p :=
      Nat.mul_le_mul_right (N ^ p) hFactor
    have hCardT : (Wi i).card ≤ (gmTranslate R W).card :=
      Finset.card_le_card (hSubset i)
    have hEnergyMono : ApproxAddEnergy 1 (Wi i) ≤
        ApproxAddEnergy 1 (gmTranslate R W) :=
      approxAddEnergy_mono_family (hSubset i)
    have hMono := heathBrownFiniteFamilyBound_mono
      (epsilon := epsilon)
      (V := heathBrownPoweredThreshold N p L packet.Cp eta)
      packet.hC0.le packet.hC2.le packet.hC4.le hB hLength
      hCardT hEnergyMono
    simpa only [heathBrownFiniteFamilyBound, heathBrownSecondMomentShape,
      heathBrownFourthMomentShape, card_gmTranslate,
      approxAddEnergy_translate] using hMono
  have hSum :
      (∑ i : Fin 4,
        heathBrownFiniteFamilyBound epsilon packet.C0 packet.C2 packet.C4 B
          (heathBrownPoweredThreshold N p L packet.Cp eta)
          (2 ^ (label i).val * N ^ p) (Wi i)) ≤
        4 * heathBrownFiniteFamilyBound epsilon packet.C0 packet.C2
          packet.C4 B (heathBrownPoweredThreshold N p L packet.Cp eta)
          (8 * N ^ p) W := by
    rw [Fin.sum_univ_four]
    nlinarith [hEach 0, hEach 1, hEach 2, hEach 3]
  exact hEnergy.trans (mul_le_mul_of_nonneg_left hSum (by positivity))

#print axioms HeathBrownPoweredCardinalityPacket.card_le_meanValue
#print axioms HeathBrownPoweredEnergyPacket.energy_le_common_power
#print axioms HeathBrownPoweredEnergyPacket.energy_le_common

end

end GafniTao
