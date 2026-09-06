import GafniTao.ClassicalBinaryShellDetectorData

/-!
# Source-parameter classical detector for Heath--Brown's energy argument

The zero-density-energy reduction first fixes two small exponents with
`delta2 / 2 <= delta1`.  Its Type-I cutoff is
`Y = floor (U ^ delta1)`, its Type-II cutoff is
`X = floor (U ^ (delta2 / 2))`, and the detector threshold is
`U ^ (-delta2)`.  Keeping these exponents distinct is essential: the final
argument sends `delta2 / delta1` to zero.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- Complete classical binary detector at the literal two source cutoffs.
All sharp-truncation, floor, mass, and short-product hypotheses are derived
inside this theorem. -/
theorem exists_heathBrown_source_classicalBinaryShellDetectorData
    {sigma shiftDelta delta1 delta2 : Real}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma <= 1)
    (hshiftDelta : 0 < shiftDelta)
    (hdelta1 : 0 < delta1) (hdelta2 : 0 < delta2)
    (hdeltaOrder : delta2 / 2 <= delta1)
    (hdelta1Upper : delta1 <= 1) (hdelta2Sigma : delta2 < sigma) :
    exists U0 : Real, 8 <= U0 /\ forall U : Real, U0 <= U ->
      let X := Nat.floor (U ^ (delta2 / 2))
      let Y := Nat.floor (U ^ delta1)
      Nonempty (ClassicalBinaryShellDetectorData sigma U shiftDelta Y X
        (Nat.floor (sharpZetaCutoff U)) (U ^ (-delta2))) := by
  obtain ⟨Udet, hUdet, hDetector⟩ :=
    exists_classicalBinaryShellDetectorData sigma shiftDelta 2 delta2 4 1
      hsigma hsigmaUpper hshiftDelta
  obtain ⟨Ucut, hUcut, hCut⟩ :=
    eventually_classical_dichotomy_cutoffs delta1 delta2 hdelta1 hdelta2
      hdeltaOrder hdelta1Upper
  obtain ⟨Ushort, hUshort, hShort⟩ :=
    eventually_classical_short_product_le_quarter delta2 hdelta2
  obtain ⟨Uerror, hUerror, hError⟩ :=
    eventually_sharp_full_error_le_split_threshold sigma delta2
      (by linarith) hdelta2Sigma
  let U0 := max Udet (max Ucut (max Ushort Uerror))
  refine ⟨U0, hUdet.trans (le_max_left _ _), ?_⟩
  intro U hU
  dsimp only
  let X := Nat.floor (U ^ (delta2 / 2))
  let Y := Nat.floor (U ^ delta1)
  have hUdet' : Udet <= U := (le_max_left _ _).trans hU
  have hRest : max Ucut (max Ushort Uerror) <= U :=
    (le_max_right _ _).trans hU
  have hUcut' : Ucut <= U := (le_max_left _ _).trans hRest
  have hRest' : max Ushort Uerror <= U := (le_max_right _ _).trans hRest
  have hUshort' : Ushort <= U := (le_max_left _ _).trans hRest'
  have hUerror' : Uerror <= U := (le_max_right _ _).trans hRest'
  have hUEight : 8 <= U := hUdet.trans hUdet'
  have hCutData := hCut U hUcut'
  dsimp only at hCutData
  obtain ⟨hMassI, hThresholdI, hMassII, hThresholdII⟩ :=
    classical_dichotomy_mass_and_threshold_bounds U delta2 Y X hUEight
      hCutData.2.2.2.2.2 hCutData.2.2.2.2.1
  apply hDetector U Y X hUdet' hCutData.1 hCutData.2.1
      hCutData.2.2.1 hCutData.2.2.2.1
  · intro rho hrho
    exact hError U hUerror' rho hrho
  · exact hShort U hUshort'
  · exact hMassI
  · exact hThresholdI
  · exact hMassII
  · exact hThresholdII

#print axioms exists_heathBrown_source_classicalBinaryShellDetectorData

end

end GafniTao
