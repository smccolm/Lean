import RiemannZeta.GuthMaynard.HughesYoungActiveCentralSource
import RiemannZeta.GuthMaynard.HughesYoungNativeCentralAssembly

open Complex MeasureTheory Set
open scoped BigOperators Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Native assembly on the actual active dyadic source

This module replaces the rectangular-completion route by the exact active
source obtained by summing the product-truncated dyadic family first.
-/

/-- The actual active equation-(85) source for all mollifier variables. -/
noncomputable def hughesYoungActiveReassembledIntegratedCentral
    (T : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∫ t : ℝ, ∫ u in -(T / 8)..T / 8,
        (hughesYoungHeightWeight T t : ℂ) *
          hughesYoungActiveReassembledSignedCentralAtHeight
            T t (hughesYoungSmallContour T) u h k
              (hughesYoungReducedLeft h k)
              (hughesYoungReducedRight h k) R K

/-- The active complete central family is exactly its single reassembled
equation-(85) source. -/
theorem hughesYoungActiveIntegratedCompleteCentral_eq_reassembledSource
    {T : ℝ} (hT : Real.exp 1 ≤ T) (R K : ℕ) :
    hughesYoungActiveIntegratedCompleteCentral T R K =
      hughesYoungActiveReassembledIntegratedCentral T R K := by
  exact hughesYoungActiveIntegratedCompleteCentral_eq_activeSource hT R K

/-- The error terms left after DFI is applied on the large active boxes and
the complementary active boxes are restored.  No inactive rectangular
central family occurs. -/
noncomputable def hughesYoungActiveNativeOffDiagonalCorrection
    (T P : ℝ) (R K : ℕ) : ℂ :=
  hughesYoungActiveNonLargeDFIOffDiagonal T P R K -
    hughesYoungActiveNonLargeDFIIntegratedCompleteCentral T P R K -
    hughesYoungActiveLargeDFIIntegratedCentralTail T P R K +
    hughesYoungActiveLargeDFIPointwiseDiscrepancy T P R K +
    hughesYoungActiveLargeDFIFarOffDiagonal T P R K

/-- Exact source-order native off-diagonal assembly on the actual active
dyadic family.  This theorem consumes the active equation-(85) source
directly and introduces no artificial rectangular complement. -/
theorem hughesYoungActiveFiniteOffDiagonal_eq_activeSource_add_correction
    {T P : ℝ} (hT : Real.exp 1 ≤ T) (hT16 : 16 ≤ T)
    (hP : 1 ≤ P) (hPT : P ≤ T) (R K : ℕ) :
    hughesYoungActiveFiniteOffDiagonal T (T / 8) R K =
      hughesYoungActiveReassembledIntegratedCentral T R K +
        hughesYoungActiveNativeOffDiagonalCorrection T P R K := by
  rw [hughesYoungActiveFiniteOffDiagonal_eq_largeDFI_add_nonLargeDFI]
  rw [hughesYoungActiveLargeDFIOffDiagonal_eq_pointwiseCentral_add_discrepancy_add_far]
  rw [hughesYoungActiveLargeDFIPointwiseSignedCentral_eq_complete_sub_tail
    hT hT16 hP hPT]
  rw [hughesYoungActiveLargeDFIIntegratedCompleteCentral_eq_full_sub_nonLarge]
  rw [hughesYoungActiveIntegratedCompleteCentral_eq_reassembledSource hT]
  unfold hughesYoungActiveNativeOffDiagonalCorrection
  ring

end RiemannZeta.GuthMaynard
