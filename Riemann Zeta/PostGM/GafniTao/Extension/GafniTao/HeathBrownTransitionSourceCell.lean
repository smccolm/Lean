import GafniTao.HeathBrownSquareSourceCell

/-!
# The constant-factor square transition

Dyadic localization only gives `P < 2Q`.  Hence the boundary case
`Q^2 <= U < P^2` genuinely lives at the enlarged physical height `4U`.
This module proves that cell with the fixed power two and retains the factor
four until the final exponent transfer.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem eventually_transition_source_dyadic_physical_cell
    {sigma delta delta1 delta2 u eta epsilon zetaLog zetaPower zetaDil
        zetaRel zetaCard sigma0 Cp Cmv C0 C2 C4 : Real}
    {Pcap : Nat}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdelta2Upper : delta2 <= 1)
    (hsigmaNonneg : 0 <= sigma) (hsigmaUpper : sigma <= 1)
    (hu : 0 <= u) (heta : 0 < eta)
    (hzetaLog : 0 < zetaLog) (hzetaPower : 0 < zetaPower)
    (hzetaDil : 0 < zetaDil) (hzetaRel : 0 < zetaRel)
    (hzetaCard : 0 < zetaCard)
    (hRelMargin : epsilon < (2 / 3 : Real) * zetaRel)
    (hPcap : Pcap = Nat.ceil (4 / delta2))
    (hCp : 0 < Cp) (hCmv : 0 < Cmv)
    (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4)
    (hsigma0Lower : 1 / 2 <= sigma0)
    (hsigma0Eff : sigma0 <= heathBrownLowerSourceEffectiveSigma
      sigma u eta zetaLog zetaPower zetaDil delta1)
    (hsigma0Upper : sigma0 <= 3 / 4) :
    ∀ᶠ U : Real in atTop,
      let A := Nat.floor (sharpZetaCutoff U)
      ∀ {Q P : Nat} (W : Finset Real) (a : Nat -> Complex) (L : Real)
          (_full : HeathBrownFullyUniformOutputs epsilon
            ((2 ^ Pcap : Real) * (4 * U)) (2 * U + U ^ delta) P 2
              eta L W a Cp Cmv C0 C2 C4),
        U ^ (delta1 / 2) <= (P : Real) ->
        U < (P : Real) ^ 2 -> (P : Real) ^ 2 <= 4 * U ->
        P < 2 * Q -> W.Nonempty -> 0 < L ->
        L = (((Q : Real) / 2) ^ sigma *
          (((3 / 4 : Real) * (U ^ (-u) / 2)) /
            ((Nat.clog 2 A + 1 : Nat) : Real))) /
          (Nat.clog 2 (A + 1) : Real) ->
        (ApproxAddEnergy 1 W : Real) <=
          ((2 ^ Pcap : Real) * (4 * U)) ^
            (max (heathBrownLowFirstSlope sigma0)
                (heathBrownLowSecondSlope sigma0) +
              4 * (zetaRel + heathBrownCardinalityShift zetaCard)) := by
  have hLargeP : ∀ᶠ U : Real in atTop, 4 <= U ^ (delta1 / 2) :=
    (tendsto_atTop.1 (tendsto_rpow_atTop (by positivity))) 4
  have hLog := eventually_lower_source_log_loss (sigma := sigma) hzetaLog
  have hDen := eventually_const_le_rpow
    (D := Cp * ((Pcap + 1 : Nat) : Real) *
      (2 : Real) ^ (((Pcap + 1 : Nat) : Real) * eta)) hzetaPower
  let sigmaRaw := sigma - 2 * eta -
    (u + zetaLog + zetaPower) / (delta1 / 2)
  have hRawUpper : sigmaRaw <= 1 := by
    dsimp only [sigmaRaw]
    have hLoss : 0 <= 2 * eta +
        (u + zetaLog + zetaPower) / (delta1 / 2) := by positivity
    linarith
  have hCommon := eventually_common_base_threshold
    (D := (2 : Real) ^ Pcap) (one_le_pow₀ (by norm_num)) hRawUpper hzetaDil
  have hGeneric := eventually_generic_powered_physical_low_cells
    (P := Pcap) hCmv hC0 hC2 hC4 hzetaRel hzetaCard hRelMargin
      hsigma0Lower hsigma0Upper
  have hGenericScaled :=
    (tendsto_id.const_mul_atTop (by norm_num : (0 : Real) < 4)).eventually
      hGeneric
  filter_upwards [hLargeP, hLog, hDen, hCommon, hGenericScaled,
      eventually_ge_atTop (8 : Real)]
    with U hLargePU hLogU hDenU hCommonU hGenericU hUEight
  dsimp only
  intro Q P W a L _full hPLower hUSquare hPSquare hPUpper hW hL hLEq
  have hUOne : 1 <= U := by linarith
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hPRealFour : (4 : Real) <= P := hLargePU.trans hPLower
  have hPOne : 1 < P := by exact_mod_cast (show (1 : Real) < P by linarith)
  have hPPos : 0 < P := by omega
  have hPcapTwo : 2 <= Pcap := by
    rw [hPcap]
    have hReal : (2 : Real) <= 4 / delta2 := by
      rw [le_div_iff₀ hdelta2]
      nlinarith
    exact_mod_cast hReal.trans (Nat.le_ceil (4 / delta2))
  have hDenMain : Cp * (2 : Real) *
      (2 : Real) ^ ((2 : Real) * eta) <= U ^ zetaPower :=
    (powered_normalization_denominator_le hCp.le heta.le
      (show (2 : Nat) <= Pcap + 1 by omega)).trans hDenU
  have hNormNext : Cp * (3 : Real) *
      (2 : Real) ^ ((3 : Real) * eta) <=
        Cp * ((Pcap + 1 : Nat) : Real) *
          (2 : Real) ^ (((Pcap + 1 : Nat) : Real) * eta) := by
    simpa only [Nat.cast_ofNat] using
      (powered_normalization_denominator_le hCp.le heta.le
        (show (3 : Nat) <= Pcap + 1 by omega))
  have hDenNext : Cp * (3 : Real) *
      (2 : Real) ^ ((3 : Real) * eta) <= U ^ zetaPower :=
    hNormNext.trans hDenU
  let A := Nat.floor (sharpZetaCutoff U)
  have hAOne : 1 < A := by
    dsimp only [A]
    apply lt_of_lt_of_le (by omega : 1 < (2 : Nat))
    apply Nat.le_floor
    exact (show (2 : Real) <= 4 * U by nlinarith).trans
      (four_mul_lt_sharpZetaCutoff U).le
  have hSource : U ^ (-(u + zetaLog)) *
      (P : Real) ^ (sigma - eta) <= L := by
    rw [hLEq]
    exact lower_source_dyadic_threshold hUPos hsigmaNonneg heta.le hAOne
      hPPos hPUpper (by simpa only [A] using hLogU)
  have hThresholdRaw : ((P ^ 2 : Nat) : Real) ^ sigmaRaw <=
      heathBrownPoweredThreshold P 2 L Cp eta := by
    simpa only [sigmaRaw, add_assoc] using
      heathBrownTypeIPoweredThreshold_lower_on_power_scale hUOne hPPos
        (by norm_num : 0 < (2 : Nat)) heta (by positivity : 0 < delta1 / 2)
        (add_nonneg hu hzetaLog.le) hzetaPower.le hCp hSource hDenMain hPLower
  have hThresholdNextRaw : ((P ^ 3 : Nat) : Real) ^ sigmaRaw <=
      heathBrownPoweredThreshold P 3 L Cp eta := by
    simpa only [sigmaRaw, add_assoc] using
      heathBrownTypeIPoweredThreshold_lower_on_power_scale hUOne hPPos
        (by norm_num : 0 < (3 : Nat)) heta (by positivity : 0 < delta1 / 2)
        (add_nonneg hu hzetaLog.le) hzetaPower.le hCp hSource hDenNext hPLower
  have hBase : ((P ^ 2 : Nat) : Real) <= 4 * U := by
    simpa only [Nat.cast_pow] using hPSquare
  have hNext : 4 * U <= ((P ^ 3 : Nat) : Real) := by
    push_cast
    have hFourP2 : 4 * U < 4 * (P : Real) ^ 2 := by nlinarith
    calc
      4 * U <= 4 * (P : Real) ^ 2 := hFourP2.le
      _ <= (P : Real) * (P : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right hPRealFour (sq_nonneg (P : Real))
      _ = (P : Real) ^ 3 := by ring
  have hCube : (4 * U) ^ 2 <= ((P ^ 2 : Nat) : Real) ^ 3 := by
    push_cast
    have hU2 : U ^ 2 <= ((P : Real) ^ 2) ^ 2 :=
      pow_le_pow_left₀ hUPos.le hUSquare.le 2
    have hSixteen : (16 : Real) <= (P : Real) ^ 2 := by
      have hsq := mul_self_le_mul_self
        (by norm_num : (0 : Real) <= 4) hPRealFour
      norm_num at hsq ⊢
      simpa only [pow_two] using hsq
    calc
      (4 * U) ^ 2 = 16 * U ^ 2 := by ring
      _ <= 16 * ((P : Real) ^ 2) ^ 2 := by gcongr
      _ <= (P : Real) ^ 2 * ((P : Real) ^ 2) ^ 2 := by gcongr
      _ = ((P : Real) ^ 2) ^ 3 := by ring
  have hPowMono : ((P ^ 2 : Nat) : Real) <= ((P ^ 3 : Nat) : Real) := by
    push_cast
    calc
      (P : Real) ^ 2 = 1 * (P : Real) ^ 2 := by ring
      _ <= (P : Real) * (P : Real) ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith : (1 : Real) <= P)
          (sq_nonneg (P : Real))
      _ = (P : Real) ^ 3 := by ring
  have hCubeNext : (4 * U) ^ 2 <= ((P ^ 3 : Nat) : Real) ^ 3 :=
    hCube.trans (pow_le_pow_left₀ (by positivity) hPowMono 3)
  have hLowerMain := rpow_two_thirds_le_of_sq_le_cube
    (by positivity : 0 <= 4 * U) (Nat.cast_nonneg (P ^ 2)) hCube
  have hLowerNext := rpow_two_thirds_le_of_sq_le_cube
    (by positivity : 0 <= 4 * U) (Nat.cast_nonneg (P ^ 3)) hCubeNext
  let sigmaEff := heathBrownLowerSourceEffectiveSigma
    sigma u eta zetaLog zetaPower zetaDil delta1
  have hThreshold : ((2 ^ Pcap * P ^ 2 : Nat) : Real) ^ sigmaEff <=
      heathBrownPoweredThreshold P 2 L Cp eta := by
    have hUtoP2 : U ^ (1 : Real) <= ((P ^ 2 : Nat) : Real) := by
      simpa only [Real.rpow_one, Nat.cast_pow] using hUSquare.le
    have h := hCommonU ((P ^ 2 : Nat) : Real)
      (heathBrownPoweredThreshold P 2 L Cp eta) hUOne
      ((Real.rpow_le_rpow_of_exponent_le hUOne (by norm_num :
        (2 / 3 : Real) <= 1)).trans hUtoP2)
      hThresholdRaw
    simpa only [sigmaEff, sigmaRaw, heathBrownLowerSourceEffectiveSigma,
      Nat.cast_mul, Nat.cast_pow, add_assoc] using h
  have hThresholdNext : ((2 ^ Pcap * P ^ 3 : Nat) : Real) ^ sigmaEff <=
      heathBrownPoweredThreshold P 3 L Cp eta := by
    have h := hCommonU ((P ^ 3 : Nat) : Real)
      (heathBrownPoweredThreshold P 3 L Cp eta) hUOne
      (by
        have hUtoP2 : U ^ (1 : Real) <= (P : Real) ^ 2 := by
          simpa only [Real.rpow_one] using hUSquare.le
        have hP2 : U ^ (2 / 3 : Real) <= (P : Real) ^ 2 :=
          (Real.rpow_le_rpow_of_exponent_le hUOne (by norm_num :
            (2 / 3 : Real) <= 1)).trans hUtoP2
        exact hP2.trans (by
          simpa only [Nat.cast_pow] using hPowMono))
      hThresholdNextRaw
    simpa only [sigmaEff, sigmaRaw, heathBrownLowerSourceEffectiveSigma,
      Nat.cast_mul, Nat.cast_pow, add_assoc] using h
  exact hGenericU W a _full
    (by simpa only [id] using (show (1 : Real) <= 4 * U by linarith))
    hPOne (by norm_num) hPcapTwo hL hW
    hBase hNext hCube hThreshold hThresholdNext hsigma0Eff hsigma0Eff

#print axioms eventually_transition_source_dyadic_physical_cell

end

end GafniTao
