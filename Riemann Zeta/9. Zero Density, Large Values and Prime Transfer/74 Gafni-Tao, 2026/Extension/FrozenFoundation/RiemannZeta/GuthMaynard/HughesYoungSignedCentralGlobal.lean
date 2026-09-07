import RiemannZeta.GuthMaynard.HughesYoungActiveDFIConsumer
import RiemannZeta.GuthMaynard.HughesYoungSignedCentralAssembly

open Complex Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Global cancellation-preserving Hughes--Young/DFI assembly

The DFI equation-(27) contribution must remain signed while the dyadic,
shift, and mollifier sums are reassembled.  These definitions expose the
three exact global pieces of the finite active off-diagonal term.  In
particular, the central series is not folded into a termwise norm majorant.
-/

/-- The complete signed DFI equation-(27) contribution in the finite active
Hughes--Young expansion. -/
noncomputable def hughesYoungActiveFiniteSignedCentral
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungNearSignedCentralBox T (hughesYoungSmallContour T)
          (T / 8) P (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The complete sum of literal DFI Theorem-1 discrepancies in the finite
active Hughes--Young expansion. -/
noncomputable def hughesYoungActiveFiniteDFIDiscrepancy
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungNearDFIDiscrepancyBox T (hughesYoungSmallContour T)
          (T / 8) P (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- The complete complementary (equation-(65)) far-shift contribution in
the finite active Hughes--Young expansion. -/
noncomputable def hughesYoungActiveFiniteFarOffDiagonal
    (T P : ℝ) (R K : ℕ) : ℂ :=
  ∑ h ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
    ∑ k ∈ Finset.Icc 1 ((detectorCutoff T) ^ 2),
      ∑ ij ∈ hughesYoungActiveDyadicBoxes
          (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) R K,
        hughesYoungFarOffDiagonalBox T (hughesYoungSmallContour T)
          (T / 8) P (hughesYoungFullDyadicScale ij.1)
          (hughesYoungFullDyadicScale ij.2) h k
          (hughesYoungFullDyadicBound ij.1)
          (hughesYoungFullDyadicBound ij.2)

/-- Exact global version of the cancellation-preserving local DFI split.
This is the source entry for Hughes--Young equations (79)--(95): only the
second and third summands are errors; the first is the signed main term. -/
theorem hughesYoungActiveFiniteOffDiagonal_eq_signedCentral_add_discrepancy_add_far
    (T P : ℝ) (R K : ℕ) :
    hughesYoungActiveFiniteOffDiagonal T (T / 8) R K =
      hughesYoungActiveFiniteSignedCentral T P R K +
        hughesYoungActiveFiniteDFIDiscrepancy T P R K +
          hughesYoungActiveFiniteFarOffDiagonal T P R K := by
  classical
  unfold hughesYoungActiveFiniteOffDiagonal
    hughesYoungActiveFiniteSignedCentral
    hughesYoungActiveFiniteDFIDiscrepancy
    hughesYoungActiveFiniteFarOffDiagonal
    hughesYoungActiveDyadicOffDiagonal
  simp only [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro h hh
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro ij _hij
  exact hughesYoungLocalizedOffDiagonalBox_eq_signedCentral_add_discrepancy_add_far
    T (hughesYoungSmallContour T) (T / 8) P
      (hughesYoungFullDyadicScale ij.1)
      (hughesYoungFullDyadicScale ij.2)
      (hh := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hh).1)

end RiemannZeta.GuthMaynard
