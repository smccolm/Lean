import GafniTao.HeathBrownLowerSourceThreshold
import GafniTao.HeathBrownTypeIPoweredThreshold
import GafniTao.HeathBrownMainOnlyCells
import GafniTao.HeathBrownPhysicalExponentTransfer

/-!
# The height-comparable source cell

This is the genuine `p = 1` edge left out by the usual consecutive-power
common-base lemma.  The extracted source length is comparable with the
physical height.  Consequently its main mean-value estimate supplies both
ordinary-cardinality caps, while the exact finite energy packet supplies the
self-referential Heath--Brown relation.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

noncomputable def heathBrownWideSourceEffectiveSigma
    (sigma u eta zetaLog zetaPower zetaScale zetaDil : Real) : Real :=
  sigma - 2 * eta -
    (u + zetaLog + zetaPower) / (1 - zetaScale) - zetaDil

theorem eventually_wide_source_dyadic_physical_cell
    {sigma delta u eta epsilon zetaLog zetaPower zetaScale zetaDil
        zetaRel zetaCard sigma0 Cp Cmv C0 C2 C4 : Real}
    {Pcap : Nat}
    (hsigmaNonneg : 0 <= sigma) (hsigmaUpper : sigma <= 1)
    (hu : 0 <= u) (heta : 0 < eta)
    (hzetaLog : 0 < zetaLog) (hzetaPower : 0 < zetaPower)
    (hzetaScale : 0 < zetaScale) (hzetaScaleUpper : zetaScale < 2 / 3)
    (hzetaDil : 0 < zetaDil) (hzetaRel : 0 < zetaRel)
    (hzetaCard : 0 < zetaCard)
    (hScaleNear : 3 * zetaScale <= 1 - sigma0)
    (hRelMargin : epsilon < (1 - zetaScale) * zetaRel)
    (hPcap : 1 <= Pcap)
    (hCp : 0 < Cp) (hCmv : 0 < Cmv)
    (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4)
    (hsigma0Lower : 1 / 2 <= sigma0)
    (hsigma0Eff : sigma0 <= heathBrownWideSourceEffectiveSigma
      sigma u eta zetaLog zetaPower zetaScale zetaDil)
    (hsigma0Upper : sigma0 <= 3 / 4) :
    ∀ᶠ U : Real in atTop,
      let A := Nat.floor (sharpZetaCutoff U)
      ∀ {Q P : Nat} (W : Finset Real) (a : Nat -> Complex) (L : Real)
          (_full : HeathBrownFullyUniformOutputs epsilon
            ((2 ^ Pcap : Real) * (6 * U)) (2 * U + U ^ delta) P 1 eta L
              W a Cp Cmv C0 C2 C4),
        U <= (Q : Real) -> P < 2 * Q -> Q < 4 * P -> 2 * Q <= A ->
        W.Nonempty -> 0 < L ->
        L = ((((Q : Real) / 2) ^ sigma *
          (((3 / 4 : Real) * (U ^ (-u) / 2)) /
            ((Nat.clog 2 A + 1 : Nat) : Real))) /
          (Nat.clog 2 (A + 1) : Real)) ->
        (ApproxAddEnergy 1 W : Real) <=
          ((2 ^ Pcap : Real) * (6 * U)) ^
            (max (heathBrownLowFirstSlope sigma0)
                (heathBrownLowSecondSlope sigma0) +
              4 * (zetaRel + zetaCard)) := by
  let alpha := 1 - zetaScale
  have halpha : 0 < alpha := by dsimp only [alpha]; linarith
  have hAlphaScale : 1 < alpha * (1 + 3 * zetaScale) := by
    dsimp only [alpha]
    nlinarith [mul_pos hzetaScale (sub_pos.mpr hzetaScaleUpper)]
  have hScaleAbsorb := eventually_const_mul_rpow_le_rpow
    (D := (4 : Real)) (a := alpha) (b := 1) (by linarith)
  have hNearAbsorb := eventually_const_mul_rpow_le_rpow
    (D := (6 : Real) * (2 : Real) ^ Pcap)
    (a := (1 : Real)) (b := alpha * (1 + 3 * zetaScale)) hAlphaScale
  have hLog := eventually_lower_source_log_loss (sigma := sigma) hzetaLog
  have hDen := eventually_const_le_rpow
    (D := Cp * (1 : Real) * (2 : Real) ^ eta) hzetaPower
  let sigmaRaw := sigma - 2 * eta -
    (u + zetaLog + zetaPower) / alpha
  have hRawUpper : sigmaRaw <= 1 := by
    dsimp only [sigmaRaw, alpha]
    have hLoss : 0 <= 2 * eta +
        (u + zetaLog + zetaPower) / (1 - zetaScale) := by positivity
    nlinarith
  have hCommon := eventually_common_base_threshold
    (D := (2 : Real) ^ Pcap) (one_le_pow₀ (by norm_num)) hRawUpper hzetaDil
  let Krel : Real :=
    ((doubleFloorDefectWindow 1).card : Real) *
      (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
      (((2 : Real) ^ Pcap * 6) ^ epsilon)
  have hLossAbsorb := eventually_const_mul_rpow_le_rpow
    (D := Krel) (a := epsilon) (b := alpha * zetaRel) hRelMargin
  have hCardAbsorb := eventually_const_mul_rpow_le_rpow
    (D := 2 * ((Pcap : Real) * Cmv))
    (a := (0 : Real)) (b := alpha * zetaCard) (by positivity)
  filter_upwards [hScaleAbsorb, hNearAbsorb, hLog, hDen, hCommon,
      hLossAbsorb, hCardAbsorb, eventually_ge_atTop (8 : Real)]
    with U hScaleAbsorbU hNearAbsorbU hLogU hDenU hCommonU
      hLossAbsorbU hCardAbsorbU hUEight
  dsimp only
  intro Q P W a L _full hUQ hPUpper hPLower hQA hW hL hLEq
  let A := Nat.floor (sharpZetaCutoff U)
  have hUOne : 1 <= U := by linarith
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hPPos : 0 < P := by omega
  have hPAlpha : U ^ alpha <= (P : Real) := by
    have hScaleAbsorbU' : 4 * U ^ alpha <= U := by
      simpa only [Real.rpow_one] using hScaleAbsorbU
    have hUFourP : U < 4 * (P : Real) := by
      exact hUQ.trans_lt (by exact_mod_cast hPLower)
    have hFour : 4 * U ^ alpha <= 4 * (P : Real) :=
      hScaleAbsorbU'.trans hUFourP.le
    exact le_of_mul_le_mul_left hFour (by norm_num : (0 : Real) < 4)
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
  have hDenOne : Cp * (1 : Real) * (2 : Real) ^ eta <= U ^ zetaPower :=
    hDenU
  have hThresholdRaw : (P : Real) ^ sigmaRaw <=
      heathBrownPoweredThreshold P 1 L Cp eta := by
    simpa only [sigmaRaw, alpha, Nat.cast_pow, pow_one, add_assoc] using
      heathBrownTypeIPoweredThreshold_lower_on_power_scale hUOne hPPos
        (by omega : 0 < (1 : Nat)) heta halpha
        (add_nonneg hu hzetaLog.le) hzetaPower.le hCp hSource
        (by simpa only [Nat.cast_one, one_mul] using hDenOne) hPAlpha
  let sigmaEff := heathBrownWideSourceEffectiveSigma
    sigma u eta zetaLog zetaPower zetaScale zetaDil
  have hThreshold : ((2 ^ Pcap * P : Nat) : Real) ^ sigmaEff <=
      heathBrownPoweredThreshold P 1 L Cp eta := by
    have h := hCommonU (P : Real)
      (heathBrownPoweredThreshold P 1 L Cp eta) hUOne
      (by
        have hTwoThird : (2 / 3 : Real) <= alpha := by
          dsimp only [alpha]
          linarith
        exact (Real.rpow_le_rpow_of_exponent_le hUOne hTwoThird).trans hPAlpha)
      hThresholdRaw
    simpa only [sigmaEff, sigmaRaw, alpha,
      heathBrownWideSourceEffectiveSigma, Nat.cast_mul, Nat.cast_pow,
      add_assoc] using h
  have hCutNonneg : 0 <= sharpZetaCutoff U := by
    linarith [four_mul_lt_sharpZetaCutoff U]
  have hAUpper : (A : Real) <= 6 * U := by
    dsimp only [A]
    have hUThree : (3 / 4 : Real) <= U := by linarith
    exact (Nat.floor_le hCutNonneg).trans
      (sharpZetaCutoff_le_six_mul hUThree)
  have hPWide : (P : Real) <= 6 * U := by
    have hPA : P < A := hPUpper.trans_le hQA
    have hPAReal : (P : Real) <= (A : Real) := by exact_mod_cast hPA.le
    exact hPAReal.trans hAUpper
  let x : Real := ((2 ^ Pcap * P : Nat) : Real)
  let B : Real := (2 ^ Pcap : Real) * (6 * U)
  let V := heathBrownPoweredThreshold P 1 L Cp eta
  let E : Real := (ApproxAddEnergy 1 W : Real)
  let sigmaLog := heathBrownLogExponent x V
  let tau := heathBrownLogExponent x B
  let rho := heathBrownLogExponent x (W.card : Real)
  let rhoStar := heathBrownLogExponent x E
  have hPcapPos : 0 < Pcap := lt_of_lt_of_le (by omega) hPcap
  have hx : 1 < x := by
    dsimp only [x]
    have hPow : 1 < 2 ^ Pcap :=
      one_lt_pow₀ (by omega : 1 < (2 : Nat)) hPcapPos.ne'
    exact_mod_cast hPow.trans_le (Nat.le_mul_of_pos_right _ hPPos)
  have hBPos : 0 < B := by dsimp only [B]; positivity
  have hxB : x <= B := by
    dsimp only [x, B]
    norm_num
    gcongr
  have hTauLower : 1 <= tau := heathBrownLogExponent_one_le hx hxB
  have hPowerLower : U ^ (alpha * (1 + 3 * zetaScale)) <=
      x ^ (1 + 3 * zetaScale) := by
    calc
      U ^ (alpha * (1 + 3 * zetaScale)) =
          (U ^ alpha) ^ (1 + 3 * zetaScale) :=
        Real.rpow_mul hUPos.le alpha (1 + 3 * zetaScale)
      _ <= (P : Real) ^ (1 + 3 * zetaScale) := by
        exact Real.rpow_le_rpow (Real.rpow_nonneg hUPos.le _) hPAlpha
          (by positivity)
      _ <= x ^ (1 + 3 * zetaScale) := by
        apply Real.rpow_le_rpow (Nat.cast_nonneg P) _ (by positivity)
        dsimp only [x]
        exact_mod_cast Nat.le_mul_of_pos_left P
          (pow_pos (by omega : 0 < (2 : Nat)) Pcap)
  have hBNear : B <= x ^ (1 + 3 * zetaScale) := by
    dsimp only [B]
    calc
      (2 : Real) ^ Pcap * (6 * U) =
          6 * (2 : Real) ^ Pcap * U ^ (1 : Real) := by
        rw [Real.rpow_one]
        ring
      _ <= U ^ (alpha * (1 + 3 * zetaScale)) := hNearAbsorbU
      _ <= x ^ (1 + 3 * zetaScale) := hPowerLower
  have hTauNearRaw : tau <= 1 + 3 * zetaScale := by
    apply (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp
    simpa only [tau, rpow_heathBrownLogExponent hx hBPos] using hBNear
  have hTauNear : tau <= 2 - sigma0 := by linarith
  have hTauUpper : tau <= 3 / 2 := by linarith
  have hVPos : 0 < V :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hx) sigmaEff).trans_le
      (by simpa only [x, V] using hThreshold)
  have hSigmaToLog : sigmaEff <= sigmaLog := by
    apply (Real.strictMono_rpow_of_base_gt_one hx).le_iff_le.mp
    simpa only [sigmaLog, rpow_heathBrownLogExponent hx hVPos, x, V] using
      hThreshold
  have hCardNat : 0 < W.card := Finset.card_pos.mpr hW
  have hCardPos : (0 : Real) < W.card := by exact_mod_cast hCardNat
  have hCardBound := _full.card_le_common (P := Pcap)
    hPcap hCmv.le hBPos.le
  have hCoeff : 2 * ((Pcap : Real) * Cmv) <= x ^ zetaCard := by
    have hUPower : U ^ (alpha * zetaCard) <= x ^ zetaCard := by
      calc
        U ^ (alpha * zetaCard) = (U ^ alpha) ^ zetaCard :=
          Real.rpow_mul hUPos.le alpha zetaCard
        _ <= (P : Real) ^ zetaCard :=
          Real.rpow_le_rpow (Real.rpow_nonneg hUPos.le _) hPAlpha hzetaCard.le
        _ <= x ^ zetaCard := by
          apply Real.rpow_le_rpow (Nat.cast_nonneg P) _ hzetaCard.le
          dsimp only [x]
          exact_mod_cast Nat.le_mul_of_pos_left P
            (pow_pos (by omega : 0 < (2 : Nat)) Pcap)
    have h := hCardAbsorbU.trans hUPower
    simpa only [Real.rpow_zero, mul_one] using h
  have hBExact : x ^ tau = B := rpow_heathBrownLogExponent hx hBPos
  have hRhoMain : rho <= zetaCard + tau + 1 - 2 * sigmaLog := by
    exact heathBrown_card_log_le_main
      (x := x) (B := B) (V := V) (card := (W.card : Real))
      (C := (Pcap : Real) * Cmv) (sigma := sigmaLog)
      (tau := tau) (zeta := zetaCard)
      hx hBPos hCardPos
      (mul_nonneg (Nat.cast_nonneg Pcap) hCmv.le) hTauLower
      (by simpa only [sigmaLog] using
        (rpow_heathBrownLogExponent hx hVPos).le)
      hBExact
      (by
        simpa only [x, B, V, Nat.cast_mul, Nat.cast_pow, pow_one,
          Nat.cast_one] using hCardBound)
      hCoeff
  have hLoss :
      (((1 ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
          (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
          B ^ epsilon <= x ^ zetaRel := by
    have hFixed :
        (((1 ^ 4 : Nat) : Real) * (doubleFloorDefectWindow 1).card) *
            (C0 * Real.sqrt (3 * C2) * Real.sqrt (3 * C4)) *
            B ^ epsilon = Krel * U ^ epsilon := by
      have hBRewrite : B = ((2 : Real) ^ Pcap * 6) * U := by
        dsimp only [B]
        ring
      rw [hBRewrite, Real.mul_rpow
        (by positivity : 0 <= (2 : Real) ^ Pcap * 6) hUPos.le]
      dsimp only [Krel]
      norm_num
      ring
    rw [hFixed]
    apply hLossAbsorbU.trans
    have hUPower : U ^ (alpha * zetaRel) <= x ^ zetaRel := by
      calc
        U ^ (alpha * zetaRel) = (U ^ alpha) ^ zetaRel :=
          Real.rpow_mul hUPos.le alpha zetaRel
        _ <= (P : Real) ^ zetaRel :=
          Real.rpow_le_rpow (Real.rpow_nonneg hUPos.le _) hPAlpha hzetaRel.le
        _ <= x ^ zetaRel := by
          apply Real.rpow_le_rpow (Nat.cast_nonneg P) _ hzetaRel.le
          dsimp only [x]
          exact_mod_cast Nat.le_mul_of_pos_left P
            (pow_pos (by omega : 0 < (2 : Nat)) Pcap)
    exact hUPower
  have hRelation := _full.logarithmic_relation_common
    (P := Pcap) (zeta := zetaRel) hPPos (by omega : 0 < (1 : Nat))
    hPcap hL hBPos hC0.le hC2.le hC4.le hW
      (by
        simpa only [B, x, Nat.cast_pow, pow_one, Nat.cast_one] using hLoss)
  have hRelation' : rhoStar <= zetaRel +
      (1 - 2 * sigmaLog +
        (1 / 2 : Real) *
          max (rho + 1) (max (2 * rho) (5 * rho / 4 + tau / 2)) +
        (1 / 2 : Real) *
          max (rhoStar + 1)
            (max (4 * rho) (3 * rhoStar / 4 + rho + tau / 2))) := by
    simpa only [x, B, V, E, sigmaLog, tau, rho, rhoStar,
      Nat.cast_mul, Nat.cast_pow, pow_one, Nat.cast_one] using hRelation
  have hCell := heathBrown_lossy_low_cells_of_main
    (sigmaMain := sigmaLog) (tau := tau) (rho := rho) (rhoStar := rhoStar)
    hsigma0Lower hsigma0Upper
    (hsigma0Eff.trans hSigmaToLog) hTauLower hTauUpper hTauNear
    hzetaRel.le hzetaCard.le
    hRhoMain hRelation'
  have hEnergy : 0 < (ApproxAddEnergy 1 W : Real) := by
    have hEnergyNat : W.card ^ 2 <= ApproxAddEnergy 1 W :=
      card_sq_le_approxAddEnergy (by norm_num) W
    exact_mod_cast (lt_of_lt_of_le (pow_pos hCardNat 2) hEnergyNat)
  exact heathBrown_physical_of_packet_bound hx hEnergy hBPos hxB
    (by positivity) rfl rfl hCell

#print axioms heathBrownWideSourceEffectiveSigma
#print axioms eventually_wide_source_dyadic_physical_cell

end

end GafniTao
