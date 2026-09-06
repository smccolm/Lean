import GafniTao.HeathBrownReflectedThreshold
import GafniTao.HeathBrownGenericPhysicalCells
import GafniTao.HeathBrownCommonThresholdExponent

/-!
# Physical Heath--Brown estimate for every reflected Type-I cell

This file composes the literal Poisson-reflection threshold, the enlarged
height power choice, the uniform finite-power outputs, both consecutive
cardinality packets, and the low-cell exponent relation.  Its theorem is
uniform in the dyadic cell; no cell is chosen by cardinality.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

noncomputable def reflectedPhysicalBeta (d : Real) : Real := 1 + 2 * d

noncomputable def reflectedPhysicalAlpha (d Uscale : Real) : Real :=
  1 / (reflectedPhysicalBeta d * Uscale)

noncomputable def reflectedPhysicalPowerCap (d Uscale : Real) : Nat :=
  Nat.ceil (reflectedPhysicalBeta d * Uscale)

noncomputable def reflectedPhysicalEffectiveSigma
    (sigma loss eta zetaShell zetaPower zetaDil d Uscale : Real) : Real :=
  sigma - loss - 2 * eta -
    (zetaShell + zetaPower) / reflectedPhysicalAlpha d Uscale - zetaDil

/-- Every nonempty energy-safe reflected dyadic cell satisfies the physical
low-cell energy bound, with all constants selected before the height and the
cell. -/
theorem eventually_interior_reflected_physical_cell
    {sigma d u epsilon eta zetaShell zetaReflect zetaPower zetaDil loss
        zetaRel zetaCard sigma0 : Real}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma <= 3 / 4)
    (hd : 0 < d) (hdGap : d <= (sigma - 1 / 2) / 1000)
    (huD : u <= d)
    (hepsilon : 0 < epsilon) (heta : 0 < eta)
    (hzetaShell : 0 < zetaShell) (hzetaReflect : 0 < zetaReflect)
    (hzetaPower : 0 < zetaPower) (hzetaDil : 0 < zetaDil)
    (hloss : 0 < loss) (hzetaRel : 0 < zetaRel)
    (hzetaCard : 0 < zetaCard)
    (hRelMargin : epsilon < (2 / 3 : Real) * zetaRel)
    (hsigma0Lower : 1 / 2 <= sigma0)
    (hsigma0Upper : sigma0 <= 3 / 4)
    (hBudget :
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      let beta := reflectedPhysicalBeta d
      u + d * (2 * sigma + 1) + beta * zetaShell + zetaReflect <=
        (loss + eta) / Uscale)
    (hEffective :
      let g := (sigma - 1 / 2) / 2
      let Uscale := 2 / g
      sigma0 <= reflectedPhysicalEffectiveSigma sigma loss eta zetaShell
        zetaPower zetaDil d Uscale) :
    let g := (sigma - 1 / 2) / 2
    let Uscale := 2 / g
    let beta := reflectedPhysicalBeta d
    let Pcap := reflectedPhysicalPowerCap d Uscale
    ∀ᶠ T : Real in atTop,
        forall {tau : Real} {Y A r : Nat},
          A = Nat.floor (sharpZetaCutoff T) -> 0 < Y -> 2 <= r ->
          2 * (2 ^ r * Y) <= A ->
          tau = typeILogarithmicScale T (2 ^ r * Y) ->
          1 < tau -> tau < 2 ->
          let Q := 2 ^ r * Y
          let M := mediumTypeIDualCutoff T d Q
          let V := ((3 / 4) * (T ^ (-u) / 2)) /
            (Nat.clog 2 A + 1 : Nat)
          let Rdet := (Real.pi * V) /
            (8 * (Q : Real) * mediumTypeIStationaryKernel sigma T Q *
              (typeIDyadicCutoffMellinL1 + 1))
          let S := Rdet / (2 * (M : Real) ^ sigma)
          let L := S / Nat.clog 2 M
          forall (j : Fin (Nat.clog 2 M)) (W : Finset Real),
            W.Nonempty -> IsSeparated 1 W ->
            (∀ t ∈ W, -(3 * T) <= t /\ t <= 3 * T) ->
            (∀ n ∈ dyadicInterval (2 ^ (j : Nat)),
              norm (normalizedTypeIReflectedCoeff sigma M n) <= 1) ->
            (∀ t ∈ W, L <=
              norm (dirichletPoly (2 ^ (j : Nat))
                (normalizedTypeIReflectedCoeff sigma M) t)) ->
            (ApproxAddEnergy 1 W : Real) <=
              ((2 ^ Pcap : Real) * T ^ beta) ^
                (max (heathBrownLowFirstSlope sigma0)
                    (heathBrownLowSecondSlope sigma0) +
                  4 * (zetaRel + heathBrownCardinalityShift zetaCard)) := by
  obtain ⟨Clog, hClog, hCref, hg, hUscale, Tscalar, hTscalar, hScalar⟩ :=
    eventually_interior_reflected_dyadic_scalar_data hsigma
      (hsigmaUpper.trans_lt (by norm_num)) hd hdGap huD
  let CK : Real := 32 * 2 ^ sigma +
    (20 * (4 * Real.pi) ^ sigma + 4 * Real.pi ^ sigma) *
      4 ^ (sigma + 1 / 2)
  let Cref : Real := mediumReflectedThresholdConstant Clog CK
  let g : Real := (sigma - 1 / 2) / 2
  let Uscale : Real := 2 / g
  let beta : Real := reflectedPhysicalBeta d
  let alpha : Real := reflectedPhysicalAlpha d Uscale
  let Pcap : Nat := reflectedPhysicalPowerCap d Uscale
  have hbeta : 0 < beta := by
    dsimp only [beta, reflectedPhysicalBeta]
    linarith
  have hbetaOne : 1 < beta := by
    dsimp only [beta, reflectedPhysicalBeta]
    linarith
  have hAlpha : 0 < alpha := by
    dsimp only [alpha, reflectedPhysicalAlpha]
    positivity
  obtain ⟨Cp, Cmv, C0, C2, C4, B0, hCp, hCmv, hC0, hC2, hC4,
      hB0, hBuild⟩ :=
    finite_source_arbitrary_power_outputs_fully_uniform_native
      epsilon eta Pcap hepsilon heta
  have hCrefAbsorb := eventually_const_le_rpow
    (D := Cref) hzetaReflect
  have hDenomRaw := eventually_const_le_rpow
    (D := Cp * ((Pcap + 1 : Nat) : Real) *
      (2 : Real) ^ (((Pcap + 1 : Nat) : Real) * eta))
    (mul_pos hbeta hzetaPower)
  have hCutoffRaw := eventually_const_le_rpow (D := B0) hbeta
  have hRangeRaw := eventually_const_le_rpow
    (D := 6) (sub_pos.mpr hbetaOne)
  have hBto : Tendsto (fun T : Real => T ^ beta) atTop atTop :=
    tendsto_rpow_atTop hbeta
  dsimp only [g, Uscale, beta, Pcap]
  have hGenericB := hBto.eventually
    (eventually_generic_powered_physical_low_cells (P := Pcap)
      hCmv hC0 hC2 hC4
      hzetaRel hzetaCard hRelMargin hsigma0Lower hsigma0Upper)
  let sigmaEff : Real := reflectedPhysicalEffectiveSigma sigma loss eta
    zetaShell zetaPower zetaDil d Uscale
  have hSigmaEffOne : sigmaEff + zetaDil <= 1 := by
    dsimp only [sigmaEff, reflectedPhysicalEffectiveSigma]
    have hLossNonneg : 0 <= loss + 2 * eta +
        (zetaShell + zetaPower) / alpha := by positivity
    linarith
  have hD : (1 : Real) <= (2 : Real) ^ Pcap := one_le_pow₀ (by norm_num)
  have hCommonB := hBto.eventually
    (eventually_common_base_threshold (D := (2 : Real) ^ Pcap)
      hD hSigmaEffOne hzetaDil)
  filter_upwards [hCrefAbsorb, hDenomRaw, hCutoffRaw, hRangeRaw,
      hGenericB, hCommonB, eventually_ge_atTop Tscalar,
      eventually_ge_atTop (8 : Real)]
    with T hCrefT hDenomT hCutoffT hRangeT hGenericT hCommonT
      hTScalar hTEight
  intro tau Y A r hA hY hr hUpper hTau hTauOne hTauTwo j W hW hSep
    hRange hCoeff hLarge
  have hTOne : 1 <= T := by linarith
  have hTStrict : 1 < T := by linarith
  have hTPos : 0 < T := by linarith
  let Q : Nat := 2 ^ r * Y
  let M : Nat := mediumTypeIDualCutoff T d Q
  let V : Real := ((3 / 4) * (T ^ (-u) / 2)) /
    (Nat.clog 2 A + 1 : Nat)
  let Rdet : Real := (Real.pi * V) /
    (8 * (Q : Real) * mediumTypeIStationaryKernel sigma T Q *
      (typeIDyadicCutoffMellinL1 + 1))
  let S : Real := Rdet / (2 * (M : Real) ^ sigma)
  let L : Real := S / Nat.clog 2 M
  let P : Nat := 2 ^ (j : Nat)
  let theta : Real := typeILogarithmicScale T P
  let B : Real := T ^ beta
  let p : Nat := heathBrownSourcePower P B
  have hScalarData := hScalar hTScalar hA hY hr hUpper hTau hTauOne
    hTauTwo j W hW hCoeff hLarge
  have hPOne : 1 < P := by simpa only [P] using hScalarData.1
  have hPM : P <= M := by
    have := hScalarData.2.1
    simpa only [P, M] using this.le
  have hThetaLower : 1 / (1 / 2 + d) <= theta := by
    simpa only [theta, P] using hScalarData.2.2.1
  have hThetaUpper : theta <= Uscale := by
    simpa only [theta, P, Uscale, g] using hScalarData.2.2.2.1
  have hThetaPos : 0 < theta := by
    have hDen : 0 < 1 / 2 + d := by linarith
    exact (by positivity : 0 < 1 / (1 / 2 + d)).trans_le hThetaLower
  have hLiteral :
      T ^ (1 / 2 - u - d * sigma + (sigma - 1) / tau - d) / Cref <= L := by
    simpa only [Cref, L, S, Rdet, V, Q, M] using
      hScalarData.2.2.2.2.1
  have hQOne : 1 < Q := by
    have hPow : 4 <= 2 ^ r := by
      simpa using Nat.pow_le_pow_right (by omega : 0 < 2) hr
    have : 4 <= Q := by
      dsimp only [Q]
      exact hPow.trans (Nat.le_mul_of_pos_right _ hY)
    omega
  have hScaleQ : (Q : Real) ^ tau = T := by
    rw [hTau]
    simpa only [Q] using rpow_typeILogarithmicScale_eq hTPos hQOne
  have hMUpperRaw := mediumTypeIDualCutoff_cast_le
    (T := T) (d := d) (Q := Q) hTPos.le
  have hQEq : (Q : Real) = T ^ (1 / tau) :=
    natCast_eq_rpow_inv_of_rpow_eq hQOne (by linarith) hScaleQ
  have hMUpper : (M : Real) <= T ^ (1 + d - 1 / tau) := by
    calc
      (M : Real) <= T ^ (1 + d) / Q := by
        simpa only [M] using hMUpperRaw
      _ = T ^ (1 + d - 1 / tau) := by
        rw [hQEq, ← Real.rpow_sub hTPos]
  have hDual : 1 / theta <= 1 + d - 1 / tau :=
    reflected_dyadic_reciprocal_scale_le hTStrict hPOne hPM hThetaPos rfl
      hMUpper
  have hExponent : 2 * (1 + d - 1 / tau) <= beta := by
    dsimp only [beta, reflectedPhysicalBeta]
    have hInv := one_div_le_one_div_of_le (by linarith : 0 < tau)
      hTauTwo.le
    linarith
  have hWindow := reflected_dyadic_expanded_power_window hTStrict hPOne hPM
    hMUpper hExponent hbeta rfl hThetaPos hThetaUpper
  dsimp only at hWindow
  have hpTwo : 2 <= p := by simpa only [p, B] using hWindow.1
  have hp : 0 < p := by omega
  have hpCap : p <= Pcap := by
    simpa only [p, Pcap, B, beta] using hWindow.2.2.2.2
  have hBase : ((P ^ p : Nat) : Real) <= B := by
    simpa only [p, P, B, Nat.cast_pow] using hWindow.2.1
  have hNext : B <= ((P ^ (p + 1) : Nat) : Real) := by
    have := hWindow.2.2.1.le
    simpa only [p, P, B, Nat.cast_pow] using this
  have hCube : B ^ 2 <= ((P ^ p : Nat) : Real) ^ 3 := by
    simpa only [p, P, B, Nat.cast_pow] using hWindow.2.2.2.1
  have hBOne : 1 <= B := by
    dsimp only [B]
    exact Real.one_le_rpow hTOne hbeta.le
  have hCommonHeight : B0 <= (2 ^ Pcap : Real) * B := by
    have hCut : B0 <= B := by
      dsimp only [B]
      simpa only [← Real.rpow_mul hTPos.le] using hCutoffT
    exact hCut.trans (le_mul_of_one_le_left (by positivity) hD)
  have hRangeHeight : 2 * (3 * T) <= (2 ^ Pcap : Real) * B := by
    have hSix : (6 : Real) <= T ^ (beta - 1) := hRangeT
    have hTBeta : 6 * T <= B := by
      dsimp only [B]
      calc
        6 * T <= T ^ (beta - 1) * T := by gcongr
        _ = T ^ beta := by
          calc
            T ^ (beta - 1) * T = T ^ (beta - 1) * T ^ (1 : Real) := by
              rw [Real.rpow_one]
            _ = T ^ ((beta - 1) + 1) :=
              (Real.rpow_add hTPos (beta - 1) 1).symm
            _ = T ^ beta := by ring_nf
    calc
      2 * (3 * T) = 6 * T := by ring
      _ <= B := hTBeta
      _ <= (2 ^ Pcap : Real) * B :=
        le_mul_of_one_le_left (by positivity) hD
  let aRef : Nat → Complex :=
    conjugateCoeffs (normalizedTypeIReflectedCoeff sigma M)
  have hCoeffRef : ∀ n ∈ dyadicInterval P, norm (aRef n) <= 1 := by
    intro n hn
    rw [show norm (aRef n) = norm (normalizedTypeIReflectedCoeff sigma M n) by
      simp [aRef, norm_conjugateCoeffs]]
    exact hCoeff n (by simpa only [P] using hn)
  have hLargeRef : ∀ t ∈ W, L <= norm (sourceDirichletPoly P aRef t) := by
    intro t ht
    rw [show norm (sourceDirichletPoly P aRef t) =
        norm (dirichletPoly P (normalizedTypeIReflectedCoeff sigma M) t) by
      simpa only [aRef] using norm_sourceDirichletPoly_conjugateCoeffs
        P (normalizedTypeIReflectedCoeff sigma M) t]
    exact hLarge t ht
  have hFullNonempty := hBuild B (3 * T) L P p W aRef
    hBOne (by omega) hp hpCap
    hRangeHeight (by simpa only [Nat.cast_pow] using hBase) (by
      have hLpos : 0 < L := by
        have hMone : 1 < M := hPOne.trans_le hPM
        dsimp only [L, S, Rdet, V]
        have hKernelPos := mediumTypeIStationaryKernel_pos
          (sigma := sigma) hTPos (lt_trans Nat.zero_lt_one hQOne)
        have hMass : 0 < typeIDyadicCutoffMellinL1 + 1 := by
          linarith [typeIDyadicCutoffMellinL1_nonneg]
        have hClogMNat : 0 < Nat.clog 2 M :=
          Nat.clog_pos Nat.one_lt_two hMone
        have hClogM : (0 : Real) < Nat.clog 2 M := by exact_mod_cast hClogMNat
        have hClogA : (0 : Real) < (Nat.clog 2 A + 1 : Nat) := by positivity
        positivity
      exact hLpos) hSep hRange hCoeffRef hLargeRef hCommonHeight
  obtain ⟨full⟩ := hFullNonempty
  have hSource : B ^ (-zetaShell) *
      (P : Real) ^ (sigma - loss - eta) <= L := by
    apply reflected_source_threshold_on_expanded_height hTOne hPOne rfl
      hsigma.le (by linarith) hTauTwo.le hThetaPos hThetaUpper hbeta.le
      hzetaShell.le hloss.le heta.le hDual
    · simpa only [g, Uscale, beta] using hBudget
    · exact zero_lt_one.trans_le hCref
    · exact hCrefT
    · exact hLiteral
  have hDenCap : Cp * ((Pcap + 1 : Nat) : Real) *
      (2 : Real) ^ (((Pcap + 1 : Nat) : Real) * eta) <= B ^ zetaPower := by
    dsimp only [B]
    rw [← Real.rpow_mul hTPos.le]
    exact hDenomT
  have hDenMain : Cp * (p : Real) *
      (2 : Real) ^ ((p : Real) * eta) <= B ^ zetaPower :=
    (powered_normalization_denominator_le (zero_le_one.trans hCp) heta.le
      (by omega : p <= Pcap + 1)).trans hDenCap
  have hDenNext : Cp * ((p + 1 : Nat) : Real) *
      (2 : Real) ^ (((p + 1 : Nat) : Real) * eta) <= B ^ zetaPower :=
    (powered_normalization_denominator_le (zero_le_one.trans hCp) heta.le
      (by omega : p + 1 <= Pcap + 1)).trans hDenCap
  have hLower : B ^ alpha <= (P : Real) := by
    simpa only [B, alpha] using reflected_expanded_height_lower_scale
      hTStrict hPOne rfl hThetaPos hUscale hThetaUpper hbeta
  let sigmaRaw : Real := sigma - loss - 2 * eta -
    (zetaShell + zetaPower) / alpha
  have hSigmaRawEq : sigmaRaw = sigmaEff + zetaDil := by
    dsimp only [sigmaRaw, sigmaEff, reflectedPhysicalEffectiveSigma]
    ring
  have hThresholdRaw : ((P ^ p : Nat) : Real) ^ sigmaRaw <=
      heathBrownPoweredThreshold P p L Cp eta := by
    simpa only [sigmaRaw] using
      heathBrownTypeIPoweredThreshold_lower_on_power_scale hBOne
        (by omega : 0 < P) hp heta hAlpha hzetaShell.le hzetaPower.le
        (zero_lt_one.trans_le hCp) hSource hDenMain hLower
  have hThresholdNextRaw : ((P ^ (p + 1) : Nat) : Real) ^ sigmaRaw <=
      heathBrownPoweredThreshold P (p + 1) L Cp eta := by
    simpa only [sigmaRaw] using
      heathBrownTypeIPoweredThreshold_lower_on_power_scale hBOne
        (by omega : 0 < P) (by omega : 0 < p + 1) heta hAlpha
        hzetaShell.le hzetaPower.le (zero_lt_one.trans_le hCp) hSource
        hDenNext hLower
  have hLowerMain := rpow_two_thirds_le_of_sq_le_cube
    (zero_le_one.trans hBOne) (Nat.cast_nonneg (P ^ p)) hCube
  have hPowMono : ((P ^ p : Nat) : Real) <=
      ((P ^ (p + 1) : Nat) : Real) := by
    exact_mod_cast (show P ^ p <= P ^ (p + 1) by
      rw [pow_succ]
      exact Nat.le_mul_of_pos_right _ (by omega : 0 < P))
  have hCubeNext : B ^ 2 <= ((P ^ (p + 1) : Nat) : Real) ^ 3 :=
    hCube.trans (pow_le_pow_left₀ (by positivity) hPowMono 3)
  have hLowerNext := rpow_two_thirds_le_of_sq_le_cube
    (zero_le_one.trans hBOne) (Nat.cast_nonneg (P ^ (p + 1))) hCubeNext
  have hThreshold : ((2 ^ Pcap * P ^ p : Nat) : Real) ^
      (sigmaRaw - zetaDil) <= heathBrownPoweredThreshold P p L Cp eta := by
    have h := hCommonT ((P ^ p : Nat) : Real)
      (heathBrownPoweredThreshold P p L Cp eta) hBOne hLowerMain
      (by simpa only [hSigmaRawEq] using hThresholdRaw)
    simpa only [Nat.cast_mul, Nat.cast_pow, ← hSigmaRawEq] using h
  have hThresholdNext : ((2 ^ Pcap * P ^ (p + 1) : Nat) : Real) ^
      (sigmaRaw - zetaDil) <=
        heathBrownPoweredThreshold P (p + 1) L Cp eta := by
    have h := hCommonT ((P ^ (p + 1) : Nat) : Real)
      (heathBrownPoweredThreshold P (p + 1) L Cp eta) hBOne hLowerNext
      (by simpa only [hSigmaRawEq] using hThresholdNextRaw)
    simpa only [Nat.cast_mul, Nat.cast_pow, ← hSigmaRawEq] using h
  have hSigma0 : sigma0 <= sigmaRaw - zetaDil := by
    simpa only [sigmaRaw, sigmaEff, reflectedPhysicalEffectiveSigma,
      alpha] using hEffective
  exact hGenericT W aRef full hBOne
    hPOne hpTwo hpCap (by
      have hLpos : 0 < L := by
        exact (div_pos (Real.rpow_pos_of_pos hTPos _)
          (zero_lt_one.trans_le hCref)).trans_le hLiteral
      exact hLpos) hW hBase hNext hCube hThreshold hThresholdNext
        hSigma0 hSigma0

#print axioms reflectedPhysicalBeta
#print axioms reflectedPhysicalAlpha
#print axioms reflectedPhysicalPowerCap
#print axioms reflectedPhysicalEffectiveSigma
#print axioms eventually_interior_reflected_physical_cell

end

end GafniTao
