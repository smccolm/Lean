import GafniTao.HeathBrownLongExponentPacket
import GafniTao.HeathBrownLossyCells
import GafniTao.HeathBrownPhysicalExponentTransfer

/-!
# Physical Heath--Brown bounds for actual long detector colours

These theorems consume the genuine branch-independent long-colour output,
the complete finite logarithmic packet, and the exact low-cell algebra.  The
conclusion is a bound for the actual self-energy at the physical common base;
all threshold, relation, and cardinality losses remain visible.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Every actual long detector colour satisfies the unified low-cell
Heath--Brown physical bound whenever the common effective real part lies in
`[1/2,3/4]`. -/
theorem eventually_heathBrownLong_physical_low_cells
    {delta1 delta2 eta epsilon zetaShell zetaConst zetaDil zetaRel zetaCard
      C Cp Cmv C0 C2 C4 : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 <= delta1)
    (hsigmaUpper : sigma <= 1) (heta : 0 < eta)
    (hzetaShell : 0 < zetaShell) (hzetaConst : 0 < zetaConst)
    (hzetaDil : 0 < zetaDil) (hzetaRel : 0 < zetaRel)
    (hzetaCard : 0 < zetaCard)
    (hRelMargin : epsilon < (2 / 3 : Real) * zetaRel)
    (hC : 0 < C) (hCp : 0 < Cp) (hCmv : 0 < Cmv)
    (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4)
    (hsigma0Lower : 1 / 2 <=
      heathBrownLongEffectiveSigma sigma delta2 eta zetaShell zetaConst
        (heathBrownLongPowerCap delta2 + 1) - zetaDil)
    (hsigma0Upper :
      heathBrownLongEffectiveSigma sigma delta2 eta zetaShell zetaConst
        (heathBrownLongPowerCap delta2 + 1) - zetaDil <= 3 / 4) :
    Filter.Eventually (fun U : Real =>
      forall (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
        (_out : HeathBrownFullyUniformLongSourceColorOutput sigma U delta
          delta1 delta2 eta epsilon C Cp Cmv C0 C2 C4 d label),
        (classicalBinaryColorFamily d label).Nonempty ->
        let P := heathBrownLongPowerCap delta2
        let E : Real := (ApproxAddEnergy 1
          (classicalBinaryColorFamily d label) : Real)
        let B := (2 ^ P : Real) * U
        let sigma0 := heathBrownLongEffectiveSigma sigma delta2 eta
          zetaShell zetaConst (P + 1) - zetaDil
        E <= B ^ (max (heathBrownLowFirstSlope sigma0)
            (heathBrownLowSecondSlope sigma0) +
          4 * (zetaRel + heathBrownCardinalityShift zetaCard))) atTop := by
  have hPacket := eventually_heathBrownLong_exponentPacket
    (sigma := sigma) (delta := delta) (epsilon := epsilon)
    hdelta1 hdelta2 hdeltaOrder hsigmaUpper heta hzetaShell hzetaConst
      hzetaDil hzetaRel hzetaCard hRelMargin hC hCp hCmv hC0 hC2 hC4
  filter_upwards [hPacket, eventually_gt_atTop (1 : Real)]
    with U hPacketU hU
  intro d label out hW
  let P := heathBrownLongPowerCap delta2
  let N := classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1
  let p := heathBrownSourcePower N U
  let E : Real := (ApproxAddEnergy 1
    (classicalBinaryColorFamily d label) : Real)
  let B := (2 ^ P : Real) * U
  let x : Real := ((2 ^ P * N ^ p : Nat) : Real)
  let sigma0 := heathBrownLongEffectiveSigma sigma delta2 eta
    zetaShell zetaConst (P + 1) - zetaDil
  let sigmaMain := heathBrownLogExponent x
    (heathBrownPoweredThreshold N p
      (classicalBinarySelectedThreshold
        (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
        d.kI d.kII sigma (U ^ (-delta2)) eta C label.1) Cp eta)
  let xNext : Real := ((2 ^ P * N ^ (p + 1) : Nat) : Real)
  let sigmaNext := heathBrownLogExponent xNext
    (heathBrownPoweredThreshold N (p + 1)
      (classicalBinarySelectedThreshold
        (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
        d.kI d.kII sigma (U ^ (-delta2)) eta C label.1) Cp eta)
  let tau := heathBrownLogExponent x B
  let rho := heathBrownLogExponent x
    ((classicalBinaryColorFamily d label).card : Real)
  let rhoStar := heathBrownLogExponent x E
  have hPack := hPacketU d label out hW
  dsimp only at hPack
  have hCell := heathBrown_lossy_low_cells hsigma0Lower hsigma0Upper
    hPack.1 hPack.2.1 hPack.2.2.1 hPack.2.2.2.1 hzetaRel.le
    hzetaCard.le hPack.2.2.2.2.1 hPack.2.2.2.2.2.1
    hPack.2.2.2.2.2.2
  have hScale := out.scale
  dsimp only at hScale
  have hN : 0 < N := by simpa only [N] using out.hN
  have hpTwo : 2 <= p := by simpa only [p] using hScale.1
  have hp : 0 < p := by omega
  have hP : 1 <= P := by
    dsimp only [P, heathBrownLongPowerCap]
    omega
  have hx : 1 < x := by
    have hPowTwo : 1 < 2 ^ P :=
      one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hP)
    have hFactor : 2 ^ P <= 2 ^ P * N ^ p :=
      Nat.le_mul_of_pos_right _ (pow_pos hN p)
    dsimp only [x]
    exact_mod_cast hPowTwo.trans_le hFactor
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
  have hB : 0 < B := by
    dsimp only [B]
    positivity
  have hxB : x <= B := by
    dsimp only [x, B]
    push_cast
    exact mul_le_mul_of_nonneg_left hScale.2.1 (by positivity)
  exact heathBrown_physical_of_packet_bound hx hE hB hxB
    (by unfold heathBrownCardinalityShift; positivity) rfl rfl hCell

#print axioms eventually_heathBrownLong_physical_low_cells

end

end GafniTao
