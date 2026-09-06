import GafniTao.HeathBrownActualExponentPacket
import GafniTao.HeathBrownLossyCells
import GafniTao.HeathBrownPhysicalExponentTransfer

/-!
# Physical low-cell bounds for the actual Type-II branch

Unlike the branch-independent long experiment, this file uses the genuine
Type-II threshold.  Consequently the effective real-part loss contains
`zetaShell * P`, not the spurious `delta2 * P`; it can therefore be made
arbitrarily small while the physical detector scales remain fixed.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The exact actual-Type-II packet implies a physical self-energy bound in
the unified low Heath--Brown cells. -/
theorem eventually_actualTypeII_physical_low_cells
    {delta1 delta2 eta epsilon zetaShell zetaConst zetaDil zetaRel zetaCard
      C Cp Cmv C0 C2 C4 : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hCube : 3 * (delta1 + delta2 / 2) <= 1)
    (hsigmaUpper : sigma <= 1) (heta : 0 < eta)
    (hzetaShell : 0 < zetaShell) (hzetaConst : 0 < zetaConst)
    (hzetaDil : 0 < zetaDil) (hzetaRel : 0 < zetaRel)
    (hzetaCard : 0 < zetaCard)
    (hRelMargin : epsilon < (2 / 3 : Real) * zetaRel)
    (hC : 0 < C) (hCp : 0 < Cp) (hCmv : 0 < Cmv)
    (hC0 : 0 < C0) (hC2 : 0 < C2) (hC4 : 0 < C4)
    (hsigma0Lower : 1 / 2 <=
      heathBrownEffectiveSigma sigma eta zetaShell zetaConst
        (Nat.ceil (4 / delta2) + 1) - zetaDil)
    (hsigma0Upper :
      heathBrownEffectiveSigma sigma eta zetaShell zetaConst
        (Nat.ceil (4 / delta2) + 1) - zetaDil <= 3 / 4) :
    Filter.Eventually (fun U : Real =>
      forall (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
        (r : Fin (d.kII * 2)),
        binaryScaleLabel label.1 = Sum.inr r ->
        let N := classicalBinarySelectedN
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII label.1
        let p := heathBrownSourcePower N U
        let P := Nat.ceil (4 / delta2)
        let L := classicalBinarySelectedThreshold
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
        let a := classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          d.kI d.kII sigma eta C label.1
        forall (_full : HeathBrownFullyUniformOutputs epsilon
            ((2 ^ P : Real) * U) (2 * U + U ^ delta)
            N p eta L (classicalBinaryColorFamily d label) a
            Cp Cmv C0 C2 C4),
          (classicalBinaryColorFamily d label).Nonempty ->
          let E : Real := (ApproxAddEnergy 1
            (classicalBinaryColorFamily d label) : Real)
          let B := (2 ^ P : Real) * U
          let sigma0 := heathBrownEffectiveSigma sigma eta zetaShell
            zetaConst (P + 1) - zetaDil
          E <= B ^ (max (heathBrownLowFirstSlope sigma0)
              (heathBrownLowSecondSlope sigma0) +
            4 * (zetaRel + heathBrownCardinalityShift zetaCard)))
      Filter.atTop := by
  have hPacket := eventually_actualTypeII_exponentPacket
    (sigma := sigma) (delta := delta) (epsilon := epsilon)
    hdelta1 hdelta2 hCube hsigmaUpper heta hzetaShell hzetaConst
      hzetaDil hzetaRel hzetaCard hRelMargin hC hCp hCmv hC0 hC2 hC4
  obtain ⟨Uscale, _hUscale, hScale⟩ :=
    eventually_heathBrown_source_typeII_scale hdelta1 hdelta2 hCube
  filter_upwards [hPacket, eventually_ge_atTop Uscale,
      eventually_gt_atTop (1 : Real)] with U hPacketU hUscaleU hU
  intro d label r hlabel
  let N := classicalBinarySelectedN
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII label.1
  let p := heathBrownSourcePower N U
  let P := Nat.ceil (4 / delta2)
  let L := classicalBinarySelectedThreshold
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII sigma (U ^ (-delta2)) eta C label.1
  let a := classicalBinarySelectedCoeff (Nat.floor (sharpZetaCutoff U))
    (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
    d.kI d.kII sigma eta C label.1
  dsimp only
  intro full hW
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
  let sigma0 := heathBrownEffectiveSigma sigma eta zetaShell
    zetaConst (P + 1) - zetaDil
  have hPack := hPacketU d label r hlabel full hW
  dsimp only at hPack
  have hSigmaMain : sigma0 <= sigmaMain := by
    have hmono : heathBrownEffectiveSigma sigma eta zetaShell zetaConst
          (P + 1) <=
        heathBrownEffectiveSigma sigma eta zetaShell zetaConst P := by
      unfold heathBrownEffectiveSigma
      push_cast
      nlinarith [hzetaShell]
    dsimp only [sigma0, sigmaMain, P]
    exact sub_le_sub_right hmono zetaDil |>.trans hPack.2.1
  have hCell := heathBrown_lossy_low_cells hsigma0Lower hsigma0Upper
    hSigmaMain hPack.2.2.1 hPack.2.2.2.1 hPack.2.2.2.2.1
    hzetaRel.le hzetaCard.le hPack.2.2.2.2.2.1
    hPack.2.2.2.2.2.2.1 hPack.2.2.2.2.2.2.2
  have hScaleData := hScale U hUscaleU (by rw [d.hkII_eq]) label.1 r hlabel
  have hNOne : 1 < N := by simpa only [N] using hScaleData.1
  have hN : 0 < N := by omega
  have hpThree : 3 <= p := by
    simpa only [N, p] using hScaleData.2.2.2.2.1
  have hBase : ((N ^ p : Nat) : Real) <= U := by
    simpa only [N, p, Nat.cast_pow] using hScaleData.2.2.2.2.2.1
  have hx : 1 < x := by
    dsimp only [x]
    exact_mod_cast (show 1 < 2 ^ P * N ^ p by
      exact (one_lt_pow₀ hNOne (by omega)).trans_le
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

#print axioms eventually_actualTypeII_physical_low_cells

end

end GafniTao
