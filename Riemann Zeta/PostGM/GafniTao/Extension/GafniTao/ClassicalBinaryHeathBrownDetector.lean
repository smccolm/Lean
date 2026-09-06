import GafniTao.ClassicalBinaryHeathBrownCutoff

/-!
# Heath--Brown physical specialization of the classical binary detector

This module supplies the actual detector data at
`X = Y = 4 * floor (U^(1/4))`.  Every analytic and finite cutoff premise of
the frozen Type-I/Type-II dichotomy is derived from the displayed strict
exponent margins.
-/

namespace GafniTao

noncomputable section

open Filter RiemannZeta.GuthMaynard

/-- The short mollifier product is eventually below one quarter at the
expanded cutoff whenever the detector threshold exponent is strictly larger
than one quarter. -/
theorem eventually_threshold_mul_heathBrownCutoff_le_quarter
    {D : Real} (hD : 1 / 4 < D) :
    ∃ U0 : Real, 8 ≤ U0 ∧ ∀ U : Real, U0 ≤ U →
      U ^ (-D) * (classicalBinaryHeathBrownCutoff U : Real) ≤ 1 / 4 := by
  obtain ⟨Uf, hUf, hSpec⟩ :=
    eventually_classicalBinaryHeathBrownCutoff_spec
  have hDecay : 0 < D - 1 / 4 := by linarith
  have hTend : Tendsto (fun U : Real => U ^ (-(D - 1 / 4)))
      atTop (nhds 0) := tendsto_rpow_neg_atTop hDecay
  have hSmallLt : ∀ᶠ U : Real in atTop,
      U ^ (-(D - 1 / 4)) < 1 / 16 :=
    (tendsto_order.1 hTend).2 (1 / 16) (by norm_num)
  have hSmall : ∀ᶠ U : Real in atTop,
      U ^ (-(D - 1 / 4)) ≤ 1 / 16 :=
    hSmallLt.mono fun _ h => h.le
  rw [eventually_atTop] at hSmall
  obtain ⟨Us, hUs⟩ := hSmall
  let U0 := max Uf Us
  refine ⟨U0, hUf.trans (le_max_left _ _), ?_⟩
  intro U hU
  have hUfU : Uf ≤ U := (le_max_left _ _).trans hU
  have hUsU : Us ≤ U := (le_max_right _ _).trans hU
  have hCut := hSpec U hUfU
  dsimp only at hCut
  have hUOne : 1 ≤ U := by linarith [hUf.trans hUfU]
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hUnderlyingUpper :
      (classicalBinaryPhysicalCutoff U (1 / 4) : Real) ≤
        U ^ (1 / 4 : Real) := by
    exact Nat.floor_le (Real.rpow_nonneg hUPos.le _)
  have hExpandedUpper : (classicalBinaryHeathBrownCutoff U : Real) ≤
      4 * U ^ (1 / 4 : Real) := by
    unfold classicalBinaryHeathBrownCutoff
    push_cast
    gcongr
  have hPowNonneg : 0 ≤ U ^ (-D) := Real.rpow_nonneg hUPos.le _
  calc
    U ^ (-D) * (classicalBinaryHeathBrownCutoff U : Real) ≤
        U ^ (-D) * (4 * U ^ (1 / 4 : Real)) :=
      mul_le_mul_of_nonneg_left hExpandedUpper hPowNonneg
    _ = 4 * (U ^ (-D) * U ^ (1 / 4 : Real)) := by ring
    _ = 4 * U ^ (-(D - 1 / 4)) := by
      rw [← Real.rpow_add hUPos]
      congr 2
      ring
    _ ≤ 4 * (1 / 16 : Real) :=
      mul_le_mul_of_nonneg_left (hUs U hUsU) (by norm_num)
    _ = 1 / 4 := by norm_num

/-- Complete shell detector data at the exact finite cutoff used in the
Heath--Brown energy argument. -/
theorem exists_heathBrown_classicalBinaryShellDetectorData
    {sigma delta D : Real}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma ≤ 1)
    (hdelta : 0 < delta) (hdeltaUpper : delta ≤ 1)
    (hDLower : 1 / 4 < D) (hDUpper : D < sigma) :
    ∃ U0 : Real, 8 ≤ U0 ∧ ∀ U : Real, U0 ≤ U →
      let X := classicalBinaryHeathBrownCutoff U
      Nonempty (ClassicalBinaryShellDetectorData sigma U delta X X
        (Nat.floor (sharpZetaCutoff U)) (U ^ (-D))) := by
  obtain ⟨Udet, hUdet, hDetector⟩ :=
    exists_classicalBinaryShellDetectorData sigma delta 2 D 4 1
      hsigma hsigmaUpper hdelta
  obtain ⟨Ucut, hUcut, hCut⟩ :=
    eventually_classicalBinaryHeathBrownCutoff_spec
  obtain ⟨Ushort, hUshort, hShort⟩ :=
    eventually_threshold_mul_heathBrownCutoff_le_quarter hDLower
  obtain ⟨Uerror, hUerror, hError⟩ :=
    eventually_sharp_full_error_le_split_threshold sigma D
      (by linarith) hDUpper
  obtain ⟨Uheight, hUheight, _hHeight⟩ :=
    eventually_classicalBinaryHeathBrownHeight_contains_shell hdeltaUpper
  let U0 := max Udet (max Ucut (max Ushort (max Uerror Uheight)))
  refine ⟨U0, hUdet.trans (le_max_left _ _), ?_⟩
  intro U hU
  dsimp only
  let X := classicalBinaryHeathBrownCutoff U
  have hUdet' : Udet ≤ U := (le_max_left _ _).trans hU
  have hRest : max Ucut (max Ushort (max Uerror Uheight)) ≤ U :=
    (le_max_right _ _).trans hU
  have hUcut' : Ucut ≤ U := (le_max_left _ _).trans hRest
  have hRest' : max Ushort (max Uerror Uheight) ≤ U :=
    (le_max_right _ _).trans hRest
  have hUshort' : Ushort ≤ U := (le_max_left _ _).trans hRest'
  have hRest'' : max Uerror Uheight ≤ U := (le_max_right _ _).trans hRest'
  have hUerror' : Uerror ≤ U := (le_max_left _ _).trans hRest''
  have hUEight : 8 ≤ U := hUdet.trans hUdet'
  have hCutData := hCut U hUcut'
  dsimp only at hCutData
  have hXPos : 0 < X := by simpa only [X] using hCutData.1
  have hXOne : 1 ≤ X := hXPos
  have hXMore : 1 < X := by
    have hXGeFour : 4 ≤ X := by
      unfold X classicalBinaryHeathBrownCutoff at hXPos ⊢
      omega
    omega
  have hXU : (X : Real) ≤ U := by simpa only [X] using hCutData.2.1
  have hXSharp : X ≤ Nat.floor (sharpZetaCutoff U) := by
    simpa only [X] using hCutData.2.2.1
  obtain ⟨hMassI, hThresholdI, hMassII, hThresholdII⟩ :=
    classical_dichotomy_mass_and_threshold_bounds U D X X hUEight hXU hXU
  apply hDetector U X X hUdet' hXOne hXMore (le_refl X) hXSharp
  · intro rho hrho
    exact hError U hUerror' rho hrho
  · exact hShort U hUshort'
  · exact hMassI
  · exact hThresholdI
  · exact hMassII
  · exact hThresholdII

#print axioms eventually_threshold_mul_heathBrownCutoff_le_quarter
#print axioms exists_heathBrown_classicalBinaryShellDetectorData

end

end GafniTao
