import GafniTao.HeathBrownCardinalityExponent
import GafniTao.HeathBrownCommonBaseTransfer
import GafniTao.HeathBrownGenericMHHCardinality
import GafniTao.HeathBrownMHHExponent

/-!
# The consecutive-power cap in the high Heath--Brown cell

The source uses the `(k+1)`-st power to obtain
`rho / k ≤ 3 - 3 * sigma`.  At the finite level that power can lie on either
side of the physical height.  We therefore use the MHH/Huxley packet when
`N^(k+1) ≤ U`, and the ordinary mean-value packet when the reverse inequality
holds.  Both results are then transferred to the common `k`-power base.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

theorem heathBrown_high_companion_exponent_cap
    {epsilon epsilonMHH U R eta L sigma0 sigmaNext zetaNext : Real}
    {N p P : Nat} {W : Finset Real} {a : Nat → Complex}
    {Cp Cmv C0 C2 C4 Cmhh : Real}
    (full : HeathBrownFullyUniformOutputs epsilon
      ((2 ^ P : Real) * U) R N p eta L W a Cp Cmv C0 C2 C4)
    (hCmv : 0 < Cmv) (hCmhh : 0 < Cmhh)
    (hepsilonMHH : 0 ≤ epsilonMHH)
    (hsigma0Upper : sigma0 < 25 / 28)
    (hSigmaNext : sigma0 ≤ sigmaNext)
    (hU : 1 ≤ U) (hN : 1 < N) (hp : 2 ≤ p) (hpNextP : p + 1 ≤ P)
    (hL : 0 < L) (hW : W.Nonempty)
    (hRB : 2 * R ≤ (2 ^ P : Real) * U)
    (hSep : IsSeparated 1 W)
    (hSymm : ∀ t ∈ W, -R ≤ t ∧ t ≤ R)
    (hThresholdNext :
      ((2 ^ P * N ^ (p + 1) : Nat) : Real) ^ sigmaNext ≤
        heathBrownPoweredThreshold N (p + 1) L Cp eta)
    (hTauNextShort :
      heathBrownLogExponent ((2 ^ P * N ^ (p + 1) : Nat) : Real)
          ((2 ^ P : Real) * U) ≤ 4 * sigma0 - 2)
    (hCoeffMHH : 2 * (((P + 1 : Nat) : Real) * Cmhh) ≤
      ((2 ^ P * N ^ (p + 1) : Nat) : Real) ^ zetaNext)
    (hCoeffMean : 2 * (((P + 1 : Nat) : Real) * Cmv) ≤
      ((2 ^ P * N ^ (p + 1) : Nat) : Real) ^ zetaNext)
    (hMHH : ∀ (M : Nat) (B R' V : Real) (W' : Finset Real)
        (b : Nat → Complex),
      0 < M → 1 ≤ B → (M : Real) ≤ B → 0 < V → 2 * R' ≤ B →
      IsSeparated 1 W' →
      (∀ t ∈ W', -R' ≤ t ∧ t ≤ R') →
      (∀ n ∈ dyadicInterval M, ‖b n‖ ≤ 1) →
      (∀ t ∈ W', V ≤ ‖sourceDirichletPoly M b t‖) →
      (W'.card : Real) ≤
        Cmhh * B ^ epsilonMHH *
          ((M : Real) ^ 2 / V ^ 2 +
            B * min ((M : Real) / V ^ 2)
              ((M : Real) ^ 4 / V ^ 6))) :
    heathBrownLogExponent ((2 ^ P * N ^ p : Nat) : Real)
        (W.card : Real) ≤
      (3 / 2 : Real) *
        (zetaNext + 2 * epsilonMHH + 2 - 2 * sigmaNext) := by
  let B : Real := (2 ^ P : Real) * U
  let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
  let xNext : Real := ((2 ^ P * N ^ (p + 1) : Nat) : Real)
  let VNext := heathBrownPoweredThreshold N (p + 1) L Cp eta
  let tauNext := heathBrownLogExponent xNext B
  have hpPos : 0 < p := by omega
  have hpP : p ≤ P := by omega
  have hNextPos : 0 < p + 1 := by omega
  have hNPos : 0 < N := by omega
  have hBPos : 0 < B := by dsimp only [B]; positivity
  have hx : 1 < x := by
    dsimp only [x]
    exact_mod_cast (show 1 < 2 ^ P * N ^ p by
      have hNp : 1 < N ^ p := one_lt_pow₀ hN (by omega)
      exact hNp.trans_le (Nat.le_mul_of_pos_left _
        (pow_pos (by norm_num : 0 < (2 : Nat)) P)))
  have hxNext : 1 < xNext := by
    dsimp only [xNext]
    exact_mod_cast (show 1 < 2 ^ P * N ^ (p + 1) by
      have hNp : 1 < N ^ (p + 1) := one_lt_pow₀ hN (by omega)
      exact hNp.trans_le (Nat.le_mul_of_pos_left _
        (pow_pos (by norm_num : 0 < (2 : Nat)) P)))
  have hVNext : 0 < VNext :=
    (Real.rpow_pos_of_pos (zero_lt_one.trans hxNext) sigmaNext).trans_le
      (by simpa only [xNext, VNext] using hThresholdNext)
  have hCardPos : (0 : Real) < W.card := by
    exact_mod_cast Finset.card_pos.mpr hW
  have hCardOne : (1 : Real) ≤ W.card := by
    exact_mod_cast Finset.card_pos.mpr hW
  have hBNextPower : xNext ^ tauNext = B :=
    rpow_heathBrownLogExponent hxNext hBPos
  have hTauShort : tauNext ≤ 4 * sigma0 - 2 := by
    simpa only [tauNext, xNext, B] using hTauNextShort
  have hTauAtSigmaNext : tauNext ≤ 4 * sigmaNext - 2 := by
    linarith
  have hTauTwo : tauNext ≤ 2 := by
    linarith
  have hNextLog : heathBrownLogExponent xNext (W.card : Real) ≤
      zetaNext + 2 * epsilonMHH + 2 - 2 * sigmaNext := by
    by_cases hLength : (N : Real) ^ (p + 1) ≤ U
    · have hRaw := full.next.card_le_mhh_common_generic hCmhh.le hMHH hU
        hNPos hNextPos hpNextP hLength hL hRB hSep hSymm
      have hCoeffPacket : 2 * (((p + 1 : Nat) : Real) * Cmhh) ≤
          xNext ^ zetaNext := by
        have hpCoeff : ((p + 1 : Nat) : Real) * Cmhh ≤
            ((P + 1 : Nat) : Real) * Cmhh := by
          gcongr
        exact (mul_le_mul_of_nonneg_left hpCoeff (by norm_num)).trans
          (by simpa only [xNext] using hCoeffMHH)
      have hLog := heathBrown_mhh_card_log_le hxNext hBPos hCardPos
        (mul_nonneg (Nat.cast_nonneg (p + 1)) hCmhh.le)
        (by simpa only [xNext, VNext] using hThresholdNext)
        hBNextPower
        (by
          simpa only [xNext, B, VNext, full.next_Cp, Nat.cast_mul,
            Nat.cast_pow, mul_assoc] using hRaw)
        hCoeffPacket
      have hMax : max (2 - 2 * sigmaNext)
          (tauNext + 4 - 6 * sigmaNext) = 2 - 2 * sigmaNext := by
        rw [max_eq_left]
        linarith
      rw [hMax] at hLog
      nlinarith
    · have hHeight : U ≤ (N : Real) ^ (p + 1) := le_of_not_ge hLength
      have hBLe : B ≤ xNext := by
        dsimp only [B, xNext]
        push_cast
        exact mul_le_mul_of_nonneg_left hHeight (by positivity)
      have hTauOne : tauNext ≤ 1 := by
        apply (Real.strictMono_rpow_of_base_gt_one hxNext).le_iff_le.mp
        simpa only [hBNextPower, Real.rpow_one] using hBLe
      have hRaw := full.next_le_common hpP hCmv.le hBPos.le
      have hLog := heathBrown_card_log_le_companion hxNext hBPos hCardPos
        (mul_nonneg (Nat.cast_nonneg (P + 1)) hCmv.le) hTauOne
        (by simpa only [xNext, VNext] using hThresholdNext)
        hBNextPower
        (by
          simpa only [xNext, B, VNext, Nat.cast_mul, Nat.cast_pow] using hRaw)
        (by simpa only [xNext] using hCoeffMean)
      linarith
  have hTransfer := heathBrown_common_cardinality_base_transfer
    (P := P) hN hp hCardOne
  calc
    heathBrownLogExponent ((2 ^ P * N ^ p : Nat) : Real)
        (W.card : Real) ≤
      (3 / 2 : Real) * heathBrownLogExponent
        ((2 ^ P * N ^ (p + 1) : Nat) : Real) (W.card : Real) := by
          simpa only [x, xNext] using hTransfer
    _ ≤ (3 / 2 : Real) *
        (zetaNext + 2 * epsilonMHH + 2 - 2 * sigmaNext) := by
      gcongr

#print axioms heathBrown_high_companion_exponent_cap

end
end GafniTao
