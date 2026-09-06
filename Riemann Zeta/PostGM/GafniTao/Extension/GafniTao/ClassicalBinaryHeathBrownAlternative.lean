import GafniTao.ClassicalBinaryHeathBrownPowered
import GafniTao.ClassicalBinaryLongTypeI

/-!
# Exhaustive Heath--Brown alternative for one detector colour

This module combines the selected-scale alternative with both genuine
analytic consumers.  In accordance with the source zero-density-energy
reduction, every Type-I colour is sent to the frozen zeta-polynomial MHH
bound, while a Type-II colour supplies the exact powered fourth-energy and
companion mean-value packets.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The exact frozen MHH output attached to a Type-I detector colour. -/
def ClassicalBinaryTypeIOutput
    (K sigma U delta q0 : Real) (Y X A : Nat)
  (d : ClassicalBinaryShellDetectorData sigma U delta Y X A q0)
  (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2) : Prop :=
  ∃ r : Fin (d.kI * 2),
    binaryScaleLabel label.1 = Sum.inl r ∧
    X ≤ classicalTypeIShellScaleN Y r ∧
    classicalTypeIShellScaleN Y r < A ∧
    ((classicalBinaryColorFamily d label).card : Real) ≤
      K * (1 + (((harmonic (classicalTypeIShellScaleN Y r) : Rat) : Real))) *
        ((classicalTypeIShellScaleN Y r : Real) ^ 2 /
            ((classicalTypeIShellScaleN Y r : Real) ^ sigma *
              (((3 / 4 : Real) * (q0 / 2)) / (d.kI : Real))) ^ 2 +
          (3 * U) * min
            ((classicalTypeIShellScaleN Y r : Real) /
              ((classicalTypeIShellScaleN Y r : Real) ^ sigma *
                (((3 / 4 : Real) * (q0 / 2)) / (d.kI : Real))) ^ 2)
            ((classicalTypeIShellScaleN Y r : Real) ^ 4 /
              ((classicalTypeIShellScaleN Y r : Real) ^ sigma *
                (((3 / 4 : Real) * (q0 / 2)) / (d.kI : Real))) ^ 6))

/-- Every actual nonempty colour is consumed by the appropriate analytic
branch.  No scale, coefficient family, or large-value set is supplied
independently of the detector. -/
theorem classicalBinaryColorFamily_heathBrown_alternative_native
    {sigma U delta D eta epsilon : Real} {A : Nat}
    (d : ClassicalBinaryShellDetectorData sigma U delta
      (classicalBinaryHeathBrownCutoff U)
      (classicalBinaryHeathBrownCutoff U) A (U ^ (-D)))
    (label : Fin (d.kI * 2 + d.kII * 2) × Fin 2)
    (hU : 2 ≤ U)
    (hX : 0 < classicalBinaryHeathBrownCutoff U)
    (hsigma : 0 ≤ sigma)
    (hdelta : delta ≤ 1)
    (hShift : U ^ delta ≤ U / 2)
    (heta : 0 < eta)
    (hepsilon : 0 < epsilon)
    (hBLower : 16 * U ≤ classicalBinaryHeathBrownHeight U)
    (hW : (classicalBinaryColorFamily d label).Nonempty) :
    ∃ K C : Real, 0 < K ∧ 0 < C ∧
      let N := classicalBinarySelectedN
        (classicalBinaryHeathBrownCutoff U)
        (classicalBinaryHeathBrownCutoff U) d.kI d.kII label.1
      let a := classicalBinarySelectedCoeff A
        (classicalBinaryHeathBrownCutoff U)
        (classicalBinaryHeathBrownCutoff U) d.kI d.kII sigma eta C label.1
      let L := classicalBinarySelectedThreshold
        (classicalBinaryHeathBrownCutoff U)
        (classicalBinaryHeathBrownCutoff U) d.kI d.kII sigma
          (U ^ (-D)) eta C label.1
      let B := classicalBinaryHeathBrownHeight U
      let R := 2 * U + U ^ delta
      let p := heathBrownPhysicalLowPower N B
      0 < N ∧
      (∀ n ∈ dyadicInterval N, ‖a n‖ ≤ 1) ∧
      (∀ t ∈ classicalBinaryColorFamily d label,
        L ≤ ‖sourceDirichletPoly N a t‖) ∧
      ((Nonempty (HeathBrownPoweredEnergyPacket epsilon (8 * B) R
          N p eta L (classicalBinaryColorFamily d label) a) ∧
        Nonempty (HeathBrownPoweredCardinalityPacket (8 * B) R
          N p eta L (classicalBinaryColorFamily d label) a) ∧
        Nonempty (HeathBrownPoweredCardinalityPacket (8 * B) R
          N (p + 1) eta L (classicalBinaryColorFamily d label) a)) ∨
        ClassicalBinaryTypeIOutput K sigma U delta (U ^ (-D))
          (classicalBinaryHeathBrownCutoff U)
          (classicalBinaryHeathBrownCutoff U) A d label) := by
  obtain ⟨K, hK, hMHH⟩ := classicalBinaryColorFamily_typeI_mhh_native
  obtain ⟨C, hC, hCoeff⟩ := sharpMollifiedCoeff_bound eta heta
  have hkIProduct : 0 < d.kI * 2 := d.hkI
  have hkI : 0 < d.kI := by omega
  have hData := classicalBinarySelectedFamily_alternative
    (A := A) (X := classicalBinaryHeathBrownCutoff U)
    (kI := d.kI) (kII := d.kII)
    hX (Real.rpow_pos_of_pos (show 0 < U by linarith) _) hkI d.hkII_eq
    hC heta.le hsigma (fun n hn => hCoeff _ _ n hn) label.1
    (classicalBinaryColorFamily d label) hW
    (classicalBinaryColorFamily_large d label)
  dsimp only at hData
  refine ⟨K, C, hK, hC, hData.1, hData.2.1, hData.2.2.1, ?_⟩
  rcases hData.2.2.2 with hTypeI | hTypeII
  · right
    rcases hTypeI with ⟨r, hrLabel, hrLower, hrUpper⟩
    refine ⟨r, hrLabel, ?_, ?_, ?_⟩
    · simpa only [classicalBinarySelectedN, hrLabel, Sum.elim_inl] using
        hrLower
    · simpa only [classicalBinarySelectedN, hrLabel, Sum.elim_inl] using
        hrUpper
    · have hNr : 0 < classicalTypeIShellScaleN
          (classicalBinaryHeathBrownCutoff U) r := by
        simpa only [classicalBinarySelectedN, hrLabel, Sum.elim_inl] using
          hData.1
      exact hMHH d label r hrLabel hsigma hU
        (Real.rpow_pos_of_pos (show 0 < U by linarith) _) hShift hNr
  · left
    rcases hTypeII with ⟨r, hrLabel, _hrLower, _hrUpper⟩
    have hWindow := classicalBinarySelected_typeII_heathBrown_powerWindow
      hX (by rw [d.hkII_eq]) label.1 r hrLabel
    exact classicalBinaryColorFamily_powerWindow_heathBrown_native d label
      (show 1 ≤ U by linarith) hX hdelta heta hepsilon hC hBLower
      hData.1 hData.2.1 hData.2.2.1 hWindow

#print axioms classicalBinaryColorFamily_heathBrown_alternative_native

end

end GafniTao
