import GafniTao.HeathBrownLowerSourceCell
import GafniTao.HeathBrownGenericPhysicalCells
import GafniTao.HeathBrownLongCommonThresholds
import GafniTao.HeathBrownTypeIPoweredThreshold

/-!
# A physical Heath--Brown cell below the square threshold

This is the exact `tau >= 2` source regime.  Its assumptions say directly
that the localized dyadic length has square at most the physical height and
has the small positive lower power needed to bound the selected natural
power.  It is independent of the endpoint-density certificate.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem eventually_square_source_dyadic_physical_cell
    {sigma delta delta2 u eta epsilon zetaLog zetaPower zetaDil
        zetaRel zetaCard sigma0 Cp Cmv C0 C2 C4 : Real}
    {Pcap : Nat}
    (hdelta2 : 0 < delta2)
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
      sigma u eta zetaLog zetaPower zetaDil delta2)
    (hsigma0Upper : sigma0 <= 3 / 4) :
    ∀ᶠ U : Real in atTop,
      let A := Nat.floor (sharpZetaCutoff U)
      ∀ {Q P : Nat} (W : Finset Real) (a : Nat -> Complex) (L : Real)
          (_full : HeathBrownFullyUniformOutputs epsilon
            ((2 ^ Pcap : Real) * U) (2 * U + U ^ delta) P
              (heathBrownSourcePower P U) eta L W a Cp Cmv C0 C2 C4),
        U ^ (delta2 / 4) <= (P : Real) ->
        (P : Real) ^ 2 <= U ->
        P < 2 * Q -> W.Nonempty -> 0 < L ->
        L = (((Q : Real) / 2) ^ sigma *
          (((3 / 4 : Real) * (U ^ (-u) / 2)) /
            ((Nat.clog 2 A + 1 : Nat) : Real))) /
          (Nat.clog 2 (A + 1) : Real) ->
        (ApproxAddEnergy 1 W : Real) <=
          ((2 ^ Pcap : Real) * U) ^
            (max (heathBrownLowFirstSlope sigma0)
                (heathBrownLowSecondSlope sigma0) +
              4 * (zetaRel + heathBrownCardinalityShift zetaCard)) := by
  have hLog := eventually_lower_source_log_loss (sigma := sigma) hzetaLog
  have hDen := eventually_const_le_rpow
    (D := Cp * ((Pcap + 1 : Nat) : Real) *
      (2 : Real) ^ (((Pcap + 1 : Nat) : Real) * eta)) hzetaPower
  let sigmaRaw := sigma - 2 * eta -
    (u + zetaLog + zetaPower) / (delta2 / 4)
  have hRawUpper : sigmaRaw <= 1 := by
    dsimp only [sigmaRaw]
    have hLoss : 0 <= 2 * eta +
        (u + zetaLog + zetaPower) / (delta2 / 4) := by positivity
    linarith
  have hCommon := eventually_common_base_threshold
    (D := (2 : Real) ^ Pcap) (one_le_pow₀ (by norm_num)) hRawUpper hzetaDil
  have hGeneric := eventually_generic_powered_physical_low_cells
    (P := Pcap) hCmv hC0 hC2 hC4 hzetaRel hzetaCard hRelMargin
      hsigma0Lower hsigma0Upper
  filter_upwards [hLog, hDen, hCommon, hGeneric,
      eventually_ge_atTop (8 : Real)]
    with U hLogU hDenU hCommonU hGenericU hUEight
  dsimp only
  intro Q P W a L _full hPLower hPSquare hPUpper hW hL hLEq
  let p := heathBrownSourcePower P U
  have hUOne : 1 <= U := by linarith
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hPRealOne : (1 : Real) < P := by
    have hLowerOne : 1 < U ^ (delta2 / 4) :=
      Real.one_lt_rpow (by linarith) (by positivity)
    exact hLowerOne.trans_le hPLower
  have hPOne : 1 < P := by exact_mod_cast hPRealOne
  have hPPos : 0 < P := by omega
  have hPower := heathBrownSourcePower_spec_two hPOne hUPos hPSquare
  dsimp only at hPower
  have hp : 2 <= p := by simpa only [p] using hPower.1
  have hpPos : 0 < p := by omega
  have hpCap : p <= Pcap := by
    rw [hPcap]
    simpa only [p] using
      heathBrownSourcePower_le_ceil_of_rpow_le hPOne (by linarith)
        hdelta2 hPLower
  have hpNextCap : p + 1 <= Pcap + 1 := Nat.add_le_add_right hpCap 1
  have hpMainCap : p <= Pcap + 1 := hpCap.trans (Nat.le_succ Pcap)
  have hDenMain : Cp * (p : Real) *
      (2 : Real) ^ ((p : Real) * eta) <= U ^ zetaPower :=
    (powered_normalization_denominator_le hCp.le heta.le hpMainCap).trans hDenU
  have hDenNext : Cp * ((p + 1 : Nat) : Real) *
      (2 : Real) ^ (((p + 1 : Nat) : Real) * eta) <= U ^ zetaPower :=
    (powered_normalization_denominator_le hCp.le heta.le hpNextCap).trans hDenU
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
  have hThresholdRaw : ((P ^ p : Nat) : Real) ^ sigmaRaw <=
      heathBrownPoweredThreshold P p L Cp eta := by
    simpa only [sigmaRaw, add_assoc] using
      heathBrownTypeIPoweredThreshold_lower_on_power_scale hUOne hPPos hpPos
        heta (by positivity : 0 < delta2 / 4)
        (add_nonneg hu hzetaLog.le) hzetaPower.le hCp hSource hDenMain
        hPLower
  have hThresholdNextRaw : ((P ^ (p + 1) : Nat) : Real) ^ sigmaRaw <=
      heathBrownPoweredThreshold P (p + 1) L Cp eta := by
    simpa only [sigmaRaw, add_assoc] using
      heathBrownTypeIPoweredThreshold_lower_on_power_scale hUOne hPPos
        (by omega : 0 < p + 1) heta (by positivity : 0 < delta2 / 4)
        (add_nonneg hu hzetaLog.le) hzetaPower.le hCp hSource hDenNext
        hPLower
  have hBase : ((P ^ p : Nat) : Real) <= U := by
    simpa only [p, Nat.cast_pow] using hPower.2.1
  have hNext : U <= ((P ^ (p + 1) : Nat) : Real) := by
    simpa only [p, Nat.cast_pow] using hPower.2.2.1.le
  have hCube : U ^ 2 <= ((P ^ p : Nat) : Real) ^ 3 := by
    simpa only [p, Nat.cast_pow] using hPower.2.2.2
  have hPowMono : ((P ^ p : Nat) : Real) <=
      ((P ^ (p + 1) : Nat) : Real) := by
    exact_mod_cast (show P ^ p <= P ^ (p + 1) by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ hPPos)
  have hCubeNext : U ^ 2 <= ((P ^ (p + 1) : Nat) : Real) ^ 3 :=
    hCube.trans (pow_le_pow_left₀ (by positivity) hPowMono 3)
  have hLowerMain := rpow_two_thirds_le_of_sq_le_cube
    (zero_le_one.trans hUOne) (Nat.cast_nonneg (P ^ p)) hCube
  have hLowerNext := rpow_two_thirds_le_of_sq_le_cube
    (zero_le_one.trans hUOne) (Nat.cast_nonneg (P ^ (p + 1))) hCubeNext
  let sigmaEff := heathBrownLowerSourceEffectiveSigma
    sigma u eta zetaLog zetaPower zetaDil delta2
  have hThreshold : ((2 ^ Pcap * P ^ p : Nat) : Real) ^ sigmaEff <=
      heathBrownPoweredThreshold P p L Cp eta := by
    have h := hCommonU ((P ^ p : Nat) : Real)
      (heathBrownPoweredThreshold P p L Cp eta) hUOne hLowerMain hThresholdRaw
    simpa only [sigmaEff, sigmaRaw, heathBrownLowerSourceEffectiveSigma,
      Nat.cast_mul, Nat.cast_pow, add_assoc] using h
  have hThresholdNext : ((2 ^ Pcap * P ^ (p + 1) : Nat) : Real) ^ sigmaEff <=
      heathBrownPoweredThreshold P (p + 1) L Cp eta := by
    have h := hCommonU ((P ^ (p + 1) : Nat) : Real)
      (heathBrownPoweredThreshold P (p + 1) L Cp eta) hUOne hLowerNext
        hThresholdNextRaw
    simpa only [sigmaEff, sigmaRaw, heathBrownLowerSourceEffectiveSigma,
      Nat.cast_mul, Nat.cast_pow, add_assoc] using h
  exact hGenericU W a _full hUOne hPOne hp hpCap hL hW hBase hNext hCube
    hThreshold hThresholdNext hsigma0Eff hsigma0Eff

#print axioms eventually_square_source_dyadic_physical_cell

end

end GafniTao
