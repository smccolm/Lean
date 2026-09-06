import GafniTao.HeathBrownLogarithmicRelation
import GafniTao.HeathBrownFullyUniformOutputs

/-!
# Logarithmic relation for an actual fully uniform Type-II output

This module consumes the real powered-energy output.  It does not accept an
independently supplied relation or energy exponent.  The source power length,
threshold, family cardinality, and self-energy are read directly from the
output and the selected colour.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- An actual fully uniform powered output satisfies Heath--Brown's
logarithmic relation up to the one displayed loss exponent `zeta`. -/
theorem HeathBrownFullyUniformOutputs.logarithmic_relation
    {epsilon B R eta L zeta : Real} {N p : Nat}
    {W : Finset Real} {a : Nat -> Complex}
    {Cp Cmv C0 C2 C4 : Real}
    (full : HeathBrownFullyUniformOutputs epsilon B R N p eta L W a
      Cp Cmv C0 C2 C4)
    (hN : 0 < N) (hp : 0 < p) (hL : 0 < L)
    (hB : 0 < B) (hC0 : 0 <= C0) (hC2 : 0 <= C2) (hC4 : 0 <= C4)
    (hW : W.Nonempty)
    (hLoss :
      (((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
          (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          B ^ epsilon <=
        (((2 ^ p * N ^ p : Nat) : Real) ^ zeta)) :
    let x : Real := ((2 ^ p * N ^ p : Nat) : Real)
    let V := heathBrownPoweredThreshold N p L Cp eta
    let E : Real := (ApproxAddEnergy 1 W : Real)
    let sigma := heathBrownLogExponent x V
    let tau := heathBrownLogExponent x B
    let rho := heathBrownLogExponent x (W.card : Real)
    let rhoStar := heathBrownLogExponent x E
    rhoStar <= zeta +
      (1 - 2 * sigma +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho)
              (3 * rhoStar / 4 + rho + tau / 2))) := by
  dsimp only
  let x : Real := ((2 ^ p * N ^ p : Nat) : Real)
  let V := heathBrownPoweredThreshold N p L Cp eta
  let E : Real := (ApproxAddEnergy 1 W : Real)
  have hNp : 0 < N ^ p := pow_pos hN p
  have hTwoP : 2 <= 2 ^ p := by
    have hpOne : 1 <= p := hp
    calc
      2 = 2 ^ 1 := by norm_num
      _ <= 2 ^ p := Nat.pow_le_pow_right (by omega) hpOne
  have hNpOne : 1 <= N ^ p := hNp
  have hxNat : 1 < 2 ^ p * N ^ p := by
    nlinarith [Nat.le_mul_of_pos_right (2 ^ p) hNp]
  have hx : 1 < x := by
    dsimp only [x]
    exact_mod_cast hxNat
  have hV : 0 < V := by
    dsimp only [V]
    unfold heathBrownPoweredThreshold
    have hpReal : (0 : Real) < p := by exact_mod_cast hp
    have hCp : 0 < Cp := by
      have hCpEnergy := full.energy.hCp
      rw [full.energy_Cp] at hCpEnergy
      exact hCpEnergy
    positivity
  have hCard : 0 < W.card := Finset.card_pos.mpr hW
  have hEnergyNat : W.card ^ 2 <= ApproxAddEnergy 1 W :=
    card_sq_le_approxAddEnergy (by norm_num) W
  have hE : 0 < E := by
    dsimp only [E]
    exact_mod_cast (lt_of_lt_of_le (pow_pos hCard 2) hEnergyNat)
  have hRaw := full.energy.energy_le_common_power hC0 hC2 hC4 hB.le
  let F : Real := ((p ^ 4 : Nat) : Real) *
    (doubleFloorDefectWindow 1).card
  have hFamily : E <= F *
      heathBrownFiniteFamilyBound epsilon C0 C2 C4 B V
        (2 ^ p * N ^ p) W := by
    dsimp only [E, F, V]
    calc
      (ApproxAddEnergy 1 W : Real) =
          (1 / 4 : Real) * (4 * (ApproxAddEnergy 1 W : Real)) := by ring
      _ <= (1 / 4 : Real) *
          ((((p ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
            (4 * heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
              (heathBrownPoweredThreshold N p L full.energy.Cp eta)
              (2 ^ p * N ^ p) W)) := by
        gcongr
      _ = (((p ^ 4 : Nat) : Real) *
          (doubleFloorDefectWindow 1).card) *
            heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
              (heathBrownPoweredThreshold N p L full.energy.Cp eta)
              (2 ^ p * N ^ p) W := by ring
      _ = (((p ^ 4 : Nat) : Real) *
          (doubleFloorDefectWindow 1).card) *
            heathBrownFiniteFamilyBound epsilon C0 C2 C4 B
              (heathBrownPoweredThreshold N p L Cp eta)
              (2 ^ p * N ^ p) W := by rw [full.energy_Cp]
  have hM : (((2 ^ p * N ^ p : Nat) : Real)) <= x := le_rfl
  have hResult := heathBrown_logarithmic_relation_of_family_bound
    (x := x) (L := F) (E := E) (zeta := zeta)
    hx hB hV (by positivity) hE hCard hC0 hC2 hC4 hM rfl hFamily
    (by simpa only [F, x] using hLoss)
  simpa only [x, V, E] using hResult

#print axioms HeathBrownFullyUniformOutputs.logarithmic_relation

end

end GafniTao
