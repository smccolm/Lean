import GafniTao.ClassicalBinaryPhysicalCutoff
import GafniTao.ClassicalBinaryShellDetectorData

/-!
# Physical specialization of the classical binary detector

The detector threshold exponent and its common physical cutoff exponent play
different roles.  Keeping them independent permits the source cutoff
`X = Y = floor(U^alpha)` whenever `alpha < D < sigma`.  This module
discharges the sharp-truncation error, short-product, mass, localization,
floor, and ambient-cutoff hypotheses of the exact signed-shell detector.
-/

namespace GafniTao

noncomputable section

open RiemannZeta.GuthMaynard

/-- The detector short product tends to zero whenever the threshold exponent
is strictly larger than the physical cutoff exponent. -/
theorem eventually_threshold_mul_physicalCutoff_le_quarter
    {alpha D : Real} (hgap : alpha < D) :
    exists U0 : Real, 1 <= U0 /\ forall U : Real, U0 <= U ->
      U ^ (-D) * (classicalBinaryPhysicalCutoff U alpha : Real) <= 1 / 4 := by
  have hDecay : 0 < D - alpha := by linarith
  have hTendsto : Filter.Tendsto (fun U : Real => U ^ (-(D - alpha)))
      Filter.atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hDecay
  have hEventually : ∀ᶠ U : Real in Filter.atTop,
      U ^ (-(D - alpha)) < 1 / 4 :=
    (tendsto_order.1 hTendsto).2 (1 / 4) (by norm_num)
  rw [Filter.eventually_atTop] at hEventually
  obtain ⟨Uscale, hUscale⟩ := hEventually
  let U0 : Real := max 1 Uscale
  refine ⟨U0, le_max_left _ _, ?_⟩
  intro U hU
  have hUOne : 1 <= U := (le_max_left _ _).trans hU
  have hUPos : 0 < U := zero_lt_one.trans_le hUOne
  have hScale : Uscale <= U := (le_max_right _ _).trans hU
  have hFloor : (classicalBinaryPhysicalCutoff U alpha : Real) <=
      U ^ alpha := by
    exact Nat.floor_le (Real.rpow_nonneg hUPos.le _)
  have hNonneg : 0 <= U ^ (-D) := Real.rpow_nonneg hUPos.le _
  calc
    U ^ (-D) * (classicalBinaryPhysicalCutoff U alpha : Real) <=
        U ^ (-D) * U ^ alpha :=
      mul_le_mul_of_nonneg_left hFloor hNonneg
    _ = U ^ (-(D - alpha)) := by
      rw [← Real.rpow_add hUPos]
      congr 1
      ring
    _ <= 1 / 4 := (hUscale U hScale).le

/-- Complete detector data at the equal source cutoffs
`X = Y = floor(U^alpha)`.  Every premise of the signed pointwise detector is
derived here from the displayed exponent inequalities. -/
theorem exists_physical_classicalBinaryShellDetectorData
    {sigma delta alpha D : Real}
    (hsigma : 1 / 2 < sigma) (hsigmaUpper : sigma <= 1)
    (hdelta : 0 < delta) (halpha : 0 < alpha)
    (halphaUpper : alpha <= 1) (halphaD : alpha < D)
    (hDsigma : D < sigma) :
    exists U0 : Real, 8 <= U0 /\ forall U : Real, U0 <= U ->
      let X := classicalBinaryPhysicalCutoff U alpha
      Nonempty (ClassicalBinaryShellDetectorData sigma U delta X X
        (Nat.floor (sharpZetaCutoff U)) (U ^ (-D))) := by
  obtain ⟨Udet, hUdet, hDetector⟩ :=
    exists_classicalBinaryShellDetectorData sigma delta 2 D 4 1
      hsigma hsigmaUpper hdelta
  obtain ⟨Ucut, hUcut, hCutoff⟩ :=
    eventually_classical_dichotomy_cutoffs alpha (2 * alpha)
      halpha (by positivity) (by linarith) halphaUpper
  obtain ⟨Ushort, hUshort, hShort⟩ :=
    eventually_threshold_mul_physicalCutoff_le_quarter halphaD
  obtain ⟨Uerror, hUerror, hError⟩ :=
    eventually_sharp_full_error_le_split_threshold sigma D
      (by linarith) hDsigma
  let U0 := max Udet (max Ucut (max Ushort Uerror))
  refine ⟨U0, hUdet.trans (le_max_left _ _), ?_⟩
  intro U hU
  dsimp only
  let X := classicalBinaryPhysicalCutoff U alpha
  have hUdet' : Udet <= U := (le_max_left _ _).trans hU
  have hRest : max Ucut (max Ushort Uerror) <= U :=
    (le_max_right _ _).trans hU
  have hUcut' : Ucut <= U := (le_max_left _ _).trans hRest
  have hRest' : max Ushort Uerror <= U := (le_max_right _ _).trans hRest
  have hUshort' : Ushort <= U := (le_max_left _ _).trans hRest'
  have hUerror' : Uerror <= U := (le_max_right _ _).trans hRest'
  have hUEight : 8 <= U := hUdet.trans hUdet'
  have hCut := hCutoff U hUcut'
  dsimp only at hCut
  have hXDef : Nat.floor (U ^ alpha) = X := rfl
  have hAlpha : 2 * alpha / 2 = alpha := by ring
  have hCut' : 1 <= X /\ 1 < X /\ X <= X /\
      X <= Nat.floor (sharpZetaCutoff U) /\
      (X : Real) <= U /\ (X : Real) <= U := by
    simpa only [hAlpha, hXDef] using hCut
  obtain ⟨hMassI, hThresholdI, hMassII, hThresholdII⟩ :=
    classical_dichotomy_mass_and_threshold_bounds U D X X hUEight
      hCut'.2.2.2.2.2 hCut'.2.2.2.2.1
  apply hDetector U X X hUdet' hCut'.1 hCut'.2.1 hCut'.2.2.1
      hCut'.2.2.2.1
  · intro rho hrho
    exact hError U hUerror' rho hrho
  · exact hShort U hUshort'
  · exact hMassI
  · exact hThresholdI
  · exact hMassII
  · exact hThresholdII

#print axioms eventually_threshold_mul_physicalCutoff_le_quarter
#print axioms exists_physical_classicalBinaryShellDetectorData

end

end GafniTao
