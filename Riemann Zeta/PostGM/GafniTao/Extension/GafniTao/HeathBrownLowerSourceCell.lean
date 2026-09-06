import GafniTao.HeathBrownLowerSourceThreshold
import GafniTao.HeathBrownGenericPhysicalCells
import GafniTao.HeathBrownLongCommonThresholds
import GafniTao.HeathBrownTypeIPoweredThreshold

/-!
# A physical Heath--Brown bound for one lower source dyadic cell

This is the analytic consumer of the exact lower-source scale and threshold
bridges.  The fully uniform output remains an argument so that the eventual
family theorem can pass the actual `out.powered` result selected before any
energy colouring.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

noncomputable def heathBrownLowerSourceEffectiveSigma
    (sigma u eta zetaLog zetaPower zetaDil delta1 : Real) : Real :=
  sigma - 2 * eta - (u + zetaLog + zetaPower) / (delta1 / 2) - zetaDil

theorem eventually_lower_source_dyadic_physical_cell
    {sigma delta delta1 delta2 u eta epsilon zetaLog zetaPower zetaDil
        zetaRel zetaCard sigma0 Cp Cmv C0 C2 C4 : Real}
    {Pcap : Nat}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 <= delta1)
    (hCube : 3 * (delta1 + delta2 / 2) <= 1)
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
      let Y := Nat.floor (U ^ delta1)
      let A := Nat.floor (sharpZetaCutoff U)
      ∀ {r P : Nat} (W : Finset Real) (a : Nat -> Complex) (L : Real)
          (_full : HeathBrownFullyUniformOutputs epsilon
            ((2 ^ Pcap : Real) * U) (2 * U + U ^ delta) P
              (heathBrownSourcePower P U) eta L W a Cp Cmv C0 C2 C4),
        r < 2 -> P < 2 * (2 ^ r * Y) -> 2 ^ r * Y < 4 * P ->
        W.Nonempty -> 0 < L ->
        L = ((((2 ^ r * Y : Nat) : Real) / 2) ^ sigma *
          (((3 / 4 : Real) * (U ^ (-u) / 2)) /
            ((Nat.clog 2 A + 1 : Nat) : Real))) /
          (Nat.clog 2 (A + 1) : Real) ->
        (ApproxAddEnergy 1 W : Real) <=
          ((2 ^ Pcap : Real) * U) ^
            (max (heathBrownLowFirstSlope sigma0)
                (heathBrownLowSecondSlope sigma0) +
              4 * (zetaRel + heathBrownCardinalityShift zetaCard)) := by
  have hScale := eventually_heathBrown_lower_source_scale hdelta1 hdelta2
    hdeltaOrder hCube
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
  filter_upwards [hScale, hLog, hDen, hCommon, hGeneric,
      eventually_ge_atTop (8 : Real)]
    with U hScaleU hLogU hDenU hCommonU hGenericU hUEight
  dsimp only
  intro r P W a L _full hr hPUpper hPLower hW hL hLEq
  let p := heathBrownSourcePower P U
  have hScaleData := hScaleU hr hPUpper hPLower
  dsimp only at hScaleData
  have hUOne : 1 <= U := by linarith
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hPPos : 0 < P := by omega
  have hp : 2 <= p := by simpa only [p] using hScaleData.2.2.1
  have hpPos : 0 < p := by omega
  have hpCap : p <= Pcap := by simpa only [p, hPcap] using hScaleData.2.2.2.2.2.2
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
  have hLower : U ^ (delta1 / 2) <= (P : Real) := hScaleData.2.1
  have hThresholdRaw : ((P ^ p : Nat) : Real) ^ sigmaRaw <=
      heathBrownPoweredThreshold P p L Cp eta := by
    simpa only [sigmaRaw, add_assoc] using
      heathBrownTypeIPoweredThreshold_lower_on_power_scale hUOne hPPos hpPos
        heta (by positivity : 0 < delta1 / 2)
        (add_nonneg hu hzetaLog.le) hzetaPower.le hCp hSource hDenMain hLower
  have hThresholdNextRaw : ((P ^ (p + 1) : Nat) : Real) ^ sigmaRaw <=
      heathBrownPoweredThreshold P (p + 1) L Cp eta := by
    simpa only [sigmaRaw, add_assoc] using
      heathBrownTypeIPoweredThreshold_lower_on_power_scale hUOne hPPos
        (by omega : 0 < p + 1) heta (by positivity : 0 < delta1 / 2)
        (add_nonneg hu hzetaLog.le) hzetaPower.le hCp hSource hDenNext hLower
  have hCubeMain : U ^ 2 <= ((P ^ p : Nat) : Real) ^ 3 := by
    simpa only [p, Nat.cast_pow] using hScaleData.2.2.2.2.2.1
  have hPowMono : ((P ^ p : Nat) : Real) <=
      ((P ^ (p + 1) : Nat) : Real) := by
    exact_mod_cast (show P ^ p <= P ^ (p + 1) by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ hPPos)
  have hCubeNext : U ^ 2 <= ((P ^ (p + 1) : Nat) : Real) ^ 3 :=
    hCubeMain.trans (pow_le_pow_left₀ (by positivity) hPowMono 3)
  have hLowerMain := rpow_two_thirds_le_of_sq_le_cube (zero_le_one.trans hUOne)
    (Nat.cast_nonneg (P ^ p)) hCubeMain
  have hLowerNext := rpow_two_thirds_le_of_sq_le_cube (zero_le_one.trans hUOne)
    (Nat.cast_nonneg (P ^ (p + 1))) hCubeNext
  let sigmaEff := heathBrownLowerSourceEffectiveSigma
    sigma u eta zetaLog zetaPower zetaDil delta1
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
  exact hGenericU W a _full hUOne hScaleData.1 hp hpCap hL hW
    (by simpa only [p, Nat.cast_pow] using hScaleData.2.2.2.1)
    (by simpa only [p, Nat.cast_pow] using hScaleData.2.2.2.2.1.le)
    hCubeMain hThreshold hThresholdNext hsigma0Eff hsigma0Eff

#print axioms heathBrownLowerSourceEffectiveSigma
#print axioms eventually_lower_source_dyadic_physical_cell

end

end GafniTao
