import GafniTao.HeathBrownActualTypeIIThresholds

/-!
# Cardinality bounds for an actual fully uniform Type-II output

This is the first consumer that simultaneously uses the retained Type-II
label, the physical source-power choice, both consecutive threshold bounds,
and the two actual cardinality packets.
-/

open Filter

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The two source cardinality bounds after all exact finite bridges have
been composed.  The only losses remaining in the exponents are displayed in
`heathBrownEffectiveSigma`; fixed dyadic and mean-value constants remain
literal coefficients. -/
theorem eventually_actualTypeII_cardinalityBounds
    {delta1 delta2 eta zetaShell zetaConst C Cp Cmv : Real}
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hCube : 3 * (delta1 + delta2 / 2) ≤ 1)
    (heta : 0 < eta) (hzetaShell : 0 < zetaShell)
    (hzetaConst : 0 < zetaConst) (hC : 0 < C)
    (hCp : 0 < Cp) (hCmv : 0 < Cmv) :
    ∀ᶠ U : Real in atTop,
      ∀ (d : ClassicalBinaryShellDetectorData sigma U delta
          (Nat.floor (U ^ delta1)) (Nat.floor (U ^ (delta2 / 2)))
          (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2)))
        (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
        (r : Fin (d.kII * 2)),
        binaryScaleLabel label.1 = Sum.inr r →
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
        ∀ full : HeathBrownFullyUniformOutputs epsilon
            ((2 ^ P : Real) * U) (2 * U + U ^ delta)
            N p eta L (classicalBinaryColorFamily d label) a
            Cp Cmv C0 C2 C4,
          ((classicalBinaryColorFamily d label).card : Real) ≤
              P * Cmv *
                (((2 ^ P : Nat) : Real) ^ 2 *
                    ((N ^ p : Nat) : Real) ^
                      (2 - 2 * heathBrownEffectiveSigma sigma eta
                        zetaShell zetaConst P) +
                  ((2 ^ P : Nat) : Real) * ((2 ^ P : Real) * U) *
                    ((N ^ p : Nat) : Real) ^
                      (1 - 2 * heathBrownEffectiveSigma sigma eta
                        zetaShell zetaConst P)) ∧
          ((classicalBinaryColorFamily d label).card : Real) ≤
              ((P + 1 : Nat) : Real) * Cmv *
                (((2 ^ P : Nat) : Real) ^ 2 *
                    ((N ^ (p + 1) : Nat) : Real) ^
                      (2 - 2 * heathBrownEffectiveSigma sigma eta
                        zetaShell zetaConst (P + 1)) +
                  ((2 ^ P : Nat) : Real) * ((2 ^ P : Real) * U) *
                    ((N ^ (p + 1) : Nat) : Real) ^
                      (1 - 2 * heathBrownEffectiveSigma sigma eta
                        zetaShell zetaConst (P + 1))) ∧
          full.card.Cmv = Cmv ∧ full.next.Cmv = Cmv := by
  have hThresholds := eventually_actualTypeII_consecutiveThresholds
    (sigma := sigma) (delta := delta)
    hdelta1 hdelta2 hCube heta hzetaShell hzetaConst hC hCp
  filter_upwards [hThresholds, eventually_ge_atTop (1 : Real)]
    with U hThresholdU hUOne
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
  have hData := hThresholdU d label r hlabel
  dsimp only at hData
  dsimp only
  intro full
  have hB : 0 ≤ (2 ^ P : Real) * U := by
    positivity
  refine ⟨full.card_le_physical hData.1 hData.2.2.1 hCmv.le hB
      hData.2.2.2.2.2.1,
    full.next_le_physical hData.1 hData.2.2.1 hCmv.le hB
      hData.2.2.2.2.2.2, full.card_Cmv, full.next_Cmv⟩

#print axioms eventually_actualTypeII_cardinalityBounds

end

end GafniTao
