import RiemannZeta.GuthMaynard.HughesYoungActiveTransfer
import RiemannZeta.GuthMaynard.HughesYoungCanonicalBox

open Complex Finset Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Active dyadic moment at fixed mollifier indices

This module performs the exact finite algebra after the legal contour
transfer.  The active family is summed at the source `h,k` indices and each
box is split into its literal diagonal and its literal nonzero-shift DFI
part.  There is no asymptotic estimate in this decomposition.
-/

/-- The `hughesYoungActiveDyadicMoment` definition used by the source-facing construction in `HughesYoungActiveMoment`. -/
noncomputable def hughesYoungActiveDyadicMoment
    (T c H : ℝ) (h k R K : ℕ) : ℂ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
    hughesYoungFullDyadicIntegratedBox T c H h k ij.1 ij.2

/-- The `hughesYoungActiveDyadicDiagonal` definition used by the source-facing construction in `HughesYoungActiveMoment`. -/
noncomputable def hughesYoungActiveDyadicDiagonal
    (T c H : ℝ) (h k R K : ℕ) : ℂ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
    hughesYoungFullDyadicDiagonalBox T c H h k ij.1 ij.2

/-- The `hughesYoungActiveDyadicOffDiagonal` definition used by the source-facing construction in `HughesYoungActiveMoment`. -/
noncomputable def hughesYoungActiveDyadicOffDiagonal
    (T c H : ℝ) (h k R K : ℕ) : ℂ :=
  ∑ ij ∈ hughesYoungActiveDyadicBoxes
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
    hughesYoungLocalizedOffDiagonalBox T c H
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2) h k
      (hughesYoungFullDyadicBound ij.1)
      (hughesYoungFullDyadicBound ij.2)

/-- Exact diagonal/off-diagonal decomposition of every active box. -/
theorem hughesYoungActiveDyadicMoment_eq_diagonal_add_offDiagonal
    (T c H : ℝ) {h k R K : ℕ} (hh : 0 < h) (hk : 0 < k) :
    hughesYoungActiveDyadicMoment T c H h k R K =
      hughesYoungActiveDyadicDiagonal T c H h k R K +
        hughesYoungActiveDyadicOffDiagonal T c H h k R K := by
  unfold hughesYoungActiveDyadicMoment hughesYoungActiveDyadicDiagonal
    hughesYoungActiveDyadicOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij hij
  exact hughesYoungFullDyadicIntegratedBox_eq_diagonal_add_offDiagonal
    T c H hh hk

/-- The active moment is literally a finite sum of the finite dyadic pair
rectangles.  This statement records the finite support needed by every later
DFI summation. -/
theorem hughesYoungActiveDyadicMoment_eq_finitePairSum
    (T c H : ℝ) {h k R K : ℕ} (hh : 0 < h) (hk : 0 < k) :
    hughesYoungActiveDyadicMoment T c H h k R K =
      ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        ∑ m ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.1),
          ∑ n ∈ Finset.Icc 1 (hughesYoungFullDyadicBound ij.2),
            hughesYoungFullDyadicIntegratedTerm
              T c H h k ij.1 ij.2 (m, n) := by
  unfold hughesYoungActiveDyadicMoment
  apply Finset.sum_congr rfl
  intro ij hij
  exact hughesYoungFullDyadicIntegratedBox_eq_finiteSum T c H hh hk

theorem norm_hughesYoungActiveDyadicOffDiagonal_le_sum_norm
    (T c H : ℝ) (h k R K : ℕ) :
    ‖hughesYoungActiveDyadicOffDiagonal T c H h k R K‖ ≤
      ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        ‖hughesYoungLocalizedOffDiagonalBox T c H
          (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)‖ := by
  unfold hughesYoungActiveDyadicOffDiagonal
  exact norm_sum_le _ _

end RiemannZeta.GuthMaynard
