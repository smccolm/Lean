import GafniTao.HeathBrownCommonBaseTransfer

/-!
# Cardinality exponents for an actual fully uniform output

This module consumes the two real cardinality packets carried by one actual
Type-II output.  It proves both source caps for the same family and records
the exact `3/2` cost of transferring the companion packet back to the main
common logarithmic base.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The main and companion mean-value estimates, expressed at the exact
common source base. -/
theorem HeathBrownFullyUniformOutputs.common_cardinality_exponents
    {epsilon B R eta L sigmaMain sigmaNext zeta : Real}
    {N p P : Nat} {W : Finset Real} {a : Nat -> Complex}
    {Cp Cmv C0 C2 C4 U : Real}
    (full : HeathBrownFullyUniformOutputs epsilon B R N p eta L W a
      Cp Cmv C0 C2 C4)
    (hN : 1 < N) (hp : 2 <= p) (hpP : p <= P)
    (hU : 0 < U) (hCmv : 0 < Cmv) (hW : W.Nonempty)
    (hB : B = (2 ^ P : Real) * U)
    (hBase : ((N ^ p : Nat) : Real) <= U)
    (hNext : U <= ((N ^ (p + 1) : Nat) : Real))
    (hCube : U ^ 2 <= ((N ^ p : Nat) : Real) ^ 3)
    (hThreshold : (((2 ^ P * N ^ p : Nat) : Real)) ^ sigmaMain <=
      heathBrownPoweredThreshold N p L Cp eta)
    (hThresholdNext : (((2 ^ P * N ^ (p + 1) : Nat) : Real)) ^ sigmaNext <=
      heathBrownPoweredThreshold N (p + 1) L Cp eta)
    (hCoeff : 2 * ((P : Real) * Cmv) <=
      (((2 ^ P * N ^ p : Nat) : Real)) ^ zeta)
    (hCoeffNext : 2 * (((P + 1 : Nat) : Real) * Cmv) <=
      (((2 ^ P * N ^ (p + 1) : Nat) : Real)) ^ zeta) :
    let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
    let xNext : Real := ((2 ^ P * N ^ (p + 1) : Nat) : Real)
    let tau := heathBrownLogExponent x B
    let tauNext := heathBrownLogExponent xNext B
    let rho := heathBrownLogExponent x (W.card : Real)
    1 <= tau /\ tau <= 3 / 2 /\ tauNext <= 1 /\
      rho <= zeta + tau + 1 - 2 * sigmaMain /\
      rho <= (3 / 2 : Real) * (zeta + 2 - 2 * sigmaNext) := by
  dsimp only
  let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
  let xNext : Real := ((2 ^ P * N ^ (p + 1) : Nat) : Real)
  let V := heathBrownPoweredThreshold N p L Cp eta
  let VNext := heathBrownPoweredThreshold N (p + 1) L Cp eta
  have hNpos : 0 < N := by omega
  have hppos : 0 < p := by omega
  have hPpos : 0 < P := lt_of_lt_of_le hppos hpP
  have hxNat : 1 < 2 ^ P * N ^ p := by
    have hNpOne : 1 < N ^ p := one_lt_pow₀ hN (by omega)
    exact hNpOne.trans_le
      (Nat.le_mul_of_pos_left (N ^ p)
        (pow_pos (by norm_num : (0 : Nat) < 2) P))
  have hxNextNat : 1 < 2 ^ P * N ^ (p + 1) := by
    have hNpOne : 1 < N ^ (p + 1) := one_lt_pow₀ hN (by omega)
    exact hNpOne.trans_le
      (Nat.le_mul_of_pos_left (N ^ (p + 1))
        (pow_pos (by norm_num : (0 : Nat) < 2) P))
  have hx : 1 < x := by dsimp only [x]; exact_mod_cast hxNat
  have hxNext : 1 < xNext := by
    dsimp only [xNext]
    exact_mod_cast hxNextNat
  have hBpos : 0 < B := by rw [hB]; positivity
  have hVpos : 0 < V := by
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hx) sigmaMain).trans_le
      hThreshold
  have hVNextPos : 0 < VNext := by
    exact (Real.rpow_pos_of_pos (zero_lt_one.trans hxNext) sigmaNext).trans_le
      hThresholdNext
  have hCardNat : 0 < W.card := Finset.card_pos.mpr hW
  have hCard : (0 : Real) < W.card := by exact_mod_cast hCardNat
  have hCardOne : (1 : Real) <= W.card := by exact_mod_cast hCardNat
  have hScale := heathBrown_common_logarithmic_scale hU hNpos hppos hpP
    hBase hCube
  dsimp only at hScale
  have hTauLower : 1 <= heathBrownLogExponent x B := by
    simpa only [x, hB, Nat.cast_mul, Nat.cast_pow] using hScale.2.1
  have hTauUpper : heathBrownLogExponent x B <= 3 / 2 := by
    simpa only [x, hB, Nat.cast_mul, Nat.cast_pow] using hScale.2.2
  have hBNext : B <= xNext := by
    rw [hB]
    dsimp only [xNext]
    norm_num
    simpa only [Nat.cast_pow] using hNext
  have hTauNext : heathBrownLogExponent xNext B <= 1 := by
    have hPower : xNext ^ heathBrownLogExponent xNext B <=
        xNext ^ (1 : Real) := by
      simpa only [rpow_heathBrownLogExponent hxNext hBpos,
        Real.rpow_one] using hBNext
    exact (Real.strictMono_rpow_of_base_gt_one hxNext).le_iff_le.mp hPower
  have hBPower : x ^ heathBrownLogExponent x B = B :=
    rpow_heathBrownLogExponent hx hBpos
  have hBNextPower : xNext ^ heathBrownLogExponent xNext B = B :=
    rpow_heathBrownLogExponent hxNext hBpos
  have hCardMain := full.card_le_common hpP hCmv.le hBpos.le
  have hCardComp := full.next_le_common hpP hCmv.le hBpos.le
  have hRhoMain := heathBrown_card_log_le_main hx hBpos hCard
    (mul_nonneg (Nat.cast_nonneg P) hCmv.le) hTauLower hThreshold hBPower
    (by simpa only [x, V, Nat.cast_mul, Nat.cast_pow] using hCardMain) hCoeff
  have hRhoNext := heathBrown_card_log_le_companion hxNext hBpos hCard
    (mul_nonneg (Nat.cast_nonneg (P + 1)) hCmv.le) hTauNext
    hThresholdNext hBNextPower
    (by simpa only [xNext, VNext, Nat.cast_mul, Nat.cast_pow] using hCardComp)
    hCoeffNext
  have hTransfer := heathBrown_common_cardinality_base_transfer
    (P := P) hN (by omega : 2 <= p) hCardOne
  have hRhoComp : heathBrownLogExponent x (W.card : Real) <=
      (3 / 2 : Real) * (zeta + 2 - 2 * sigmaNext) := by
    calc
      heathBrownLogExponent x (W.card : Real) <=
          (3 / 2 : Real) *
            heathBrownLogExponent xNext (W.card : Real) := by
        simpa only [x, xNext] using hTransfer
      _ <= (3 / 2 : Real) * (zeta + 2 - 2 * sigmaNext) := by
        gcongr
  exact ⟨hTauLower, hTauUpper, hTauNext, hRhoMain, hRhoComp⟩

#print axioms HeathBrownFullyUniformOutputs.common_cardinality_exponents

end

end GafniTao
