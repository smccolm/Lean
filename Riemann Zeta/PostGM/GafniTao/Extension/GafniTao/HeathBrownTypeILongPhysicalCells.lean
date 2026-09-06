import GafniTao.HeathBrownTypeILongExponentPacket
import GafniTao.HeathBrownLossyCells
import GafniTao.HeathBrownPhysicalExponentTransfer

/-!
# Physical low-cell bounds for an actual long Type-I colour

This theorem converts the exact Type-I logarithmic packet back to the
physical ambient height.  It is parallel to the Type-II consumer but uses
the corrected Type-I effective real part.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- A genuine Type-I colour beyond the square threshold satisfies the
unified low Heath--Brown self-energy bound. -/
theorem eventually_actualTypeI_long_physical_low_cells
    {delta1 delta2 eta epsilon zetaShell zetaConst zetaDil zetaRel zetaCard
      C Cp Cmv C0 C2 C4 : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hsigmaUpper : sigma <= 1) (heta : 0 < eta)
    (hzetaShell : 0 < zetaShell) (hzetaConst : 0 < zetaConst)
    (hzetaDil : 0 < zetaDil) (hzetaRel : 0 < zetaRel)
    (hzetaCard : 0 < zetaCard)
    (hRelMargin : epsilon < (2 / 3 : Real) * zetaRel)
    (hC : 0 < C) (hCp : 0 < Cp) (hCmv : 0 < Cmv)
    (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4)
    (hsigma0Lower : 1 / 2 <=
      heathBrownTypeIEffectiveSigma sigma delta1 delta2 eta
        zetaShell zetaConst - zetaDil)
    (hsigma0Upper :
      heathBrownTypeIEffectiveSigma sigma delta1 delta2 eta
        zetaShell zetaConst - zetaDil <= 3 / 4) :
    ∀ᶠ U : Real in atTop,
      forall (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
        (r : Fin (d.kI * 2))
        (_out : HeathBrownFullyUniformLongSourceColorOutput sigma U delta
          delta1 delta2 eta epsilon C Cp Cmv C0 C2 C4 d label),
        binaryScaleLabel label.1 = Sum.inl r ->
        (classicalBinaryColorFamily d label).Nonempty ->
        let E : Real := (ApproxAddEnergy 1
          (classicalBinaryColorFamily d label) : Real)
        let P := heathBrownLongPowerCap delta2
        let B := (2 ^ P : Real) * U
        let sigma0 := heathBrownTypeIEffectiveSigma sigma delta1 delta2 eta
          zetaShell zetaConst - zetaDil
        E <= B ^ (max (heathBrownLowFirstSlope sigma0)
              (heathBrownLowSecondSlope sigma0) +
            4 * (zetaRel + heathBrownCardinalityShift zetaCard)) := by
  have hPacket := eventually_actualTypeI_long_exponentPacket
    (sigma := sigma) (delta := delta)
    hdelta1 hdelta2 hsigmaUpper heta hzetaShell hzetaConst hzetaDil
      hzetaRel hzetaCard hRelMargin hC hCp hCmv hC0 hC2 hC4
  filter_upwards [hPacket, eventually_gt_atTop (1 : Real)]
    with U hPacketU hU
  intro d label r out hlabel hW
  let N := classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1
  let p := heathBrownSourcePower N U
  let P := heathBrownLongPowerCap delta2
  let L := classicalBinarySelectedThreshold
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
  let E : Real := (ApproxAddEnergy 1
    (classicalBinaryColorFamily d label) : Real)
  let B := (2 ^ P : Real) * U
  let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
  let xNext : Real := ((2 ^ P * N ^ (p + 1) : Nat) : Real)
  let sigmaMain := heathBrownLogExponent x
    (heathBrownPoweredThreshold N p L Cp eta)
  let sigmaNext := heathBrownLogExponent xNext
    (heathBrownPoweredThreshold N (p + 1) L Cp eta)
  let tau := heathBrownLogExponent x B
  let rho := heathBrownLogExponent x
    ((classicalBinaryColorFamily d label).card : Real)
  let rhoStar := heathBrownLogExponent x E
  let sigma0 := heathBrownTypeIEffectiveSigma sigma delta1 delta2 eta
    zetaShell zetaConst - zetaDil
  have hPack := hPacketU d label r out hlabel hW
  dsimp only at hPack
  have hCell := heathBrown_lossy_low_cells hsigma0Lower hsigma0Upper
    hPack.1 hPack.2.1 hPack.2.2.1 hPack.2.2.2.1
    hzetaRel.le hzetaCard.le hPack.2.2.2.2.1
    hPack.2.2.2.2.2.1 hPack.2.2.2.2.2.2
  have hNOne : 1 < N := by
    have hpTwo : 2 <= p := by simpa only [N, p] using out.scale.1
    have hNpos : 0 < N := by simpa only [N] using out.hN
    have hNne : N ≠ 1 := by
      intro hNIsOne
      have hpZero : p = 0 := by
        simp [p, heathBrownSourcePower, hNIsOne]
      omega
    omega
  have hN : 0 < N := by omega
  have hp : 0 < p := by
    have : 2 <= p := by simpa only [N, p] using out.scale.1
    omega
  have hBase : ((N ^ p : Nat) : Real) <= U := by
    simpa only [N, p, Nat.cast_pow] using out.scale.2.1
  have hx : 1 < x := by
    dsimp only [x]
    exact_mod_cast (show 1 < 2 ^ P * N ^ p by
      exact (one_lt_pow₀ hNOne (Nat.ne_of_gt hp)).trans_le
        (Nat.le_mul_of_pos_left _
          (pow_pos (by norm_num : (0 : Nat) < 2) P)))
  have hE : 0 < E := by
    have hCard : 0 < (classicalBinaryColorFamily d label).card :=
      Finset.card_pos.mpr hW
    have hEnergyNat :
        (classicalBinaryColorFamily d label).card ^ 2 <=
          ApproxAddEnergy 1 (classicalBinaryColorFamily d label) :=
      card_sq_le_approxAddEnergy (by norm_num)
        (classicalBinaryColorFamily d label)
    dsimp only [E]
    exact_mod_cast (lt_of_lt_of_le (pow_pos hCard 2) hEnergyNat)
  have hB : 0 < B := by dsimp only [B]; positivity
  have hxB : x <= B := by
    dsimp only [x, B]
    push_cast
    exact mul_le_mul_of_nonneg_left
      (by simpa only [Nat.cast_pow] using hBase) (by positivity)
  exact heathBrown_physical_of_packet_bound hx hE hB hxB
    (by unfold heathBrownCardinalityShift; positivity) rfl rfl hCell

#print axioms eventually_actualTypeI_long_physical_low_cells

end

end GafniTao
