import RiemannZeta.GuthMaynard.HughesYoungBoxConsumer

open Complex Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Cancellation-preserving Hughes--Young/DFI assembly

DFI equation (27) is the main term, not part of the error.  This file keeps
the signed Ramanujan central series intact and isolates only the literal DFI
discrepancy.  It is the exact local algebraic entry to Hughes--Young equations
(83)--(95).
-/

/-- The signed DFI equation-(27) contribution over the exact near-shift
family of one localized Hughes--Young box. -/
noncomputable def hughesYoungNearSignedCentralBox
    (T c H P X Y : ℝ) (h k M N : ℕ) : ℂ :=
  ∑ r ∈ hughesYoungNearShifts T P X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
    dfiSignedCentralSeries
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
      (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)

/-- The sum of the exact DFI discrepancies over the same near-shift family.
No triangle inequality has been applied. -/
noncomputable def hughesYoungNearDFIDiscrepancyBox
    (T c H P X Y : ℝ) (h k M N : ℕ) : ℂ :=
  ∑ r ∈ hughesYoungNearShifts T P X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
    (dfiDyadicShiftedDivisorSum
        (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N r -
      dfiSignedCentralSeries
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
        (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k))

/-- The exact equation-(65) complementary shift contribution. -/
noncomputable def hughesYoungFarOffDiagonalBox
    (T c H P X Y : ℝ) (h k M N : ℕ) : ℂ :=
  ∑ r ∈ hughesYoungFarShifts T P X Y
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
    dfiDyadicShiftedDivisorSum
      (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
      (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N r

theorem hughesYoungNearShiftSum_eq_signedCentral_add_discrepancy
    (T c H P X Y : ℝ) (h k M N : ℕ) :
    (∑ r ∈ hughesYoungNearShifts T P X Y
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N,
      dfiDyadicShiftedDivisorSum
        (hughesYoungGCDReducedIntegratedBoxWeight T c H X Y h k)
        (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) M N r) =
      hughesYoungNearSignedCentralBox T c H P X Y h k M N +
        hughesYoungNearDFIDiscrepancyBox T c H P X Y h k M N := by
  classical
  unfold hughesYoungNearSignedCentralBox hughesYoungNearDFIDiscrepancyBox
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r _hr
  ring

/-- Exact cancellation-preserving decomposition of one localized box into
the DFI central main term, the DFI theorem-1 discrepancy, and the
equation-(65) far family. -/
theorem hughesYoungLocalizedOffDiagonalBox_eq_signedCentral_add_discrepancy_add_far
    (T c H P X Y : ℝ) {h k M N : ℕ} (hh : 0 < h) :
    hughesYoungLocalizedOffDiagonalBox T c H X Y h k M N =
      hughesYoungNearSignedCentralBox T c H P X Y h k M N +
        hughesYoungNearDFIDiscrepancyBox T c H P X Y h k M N +
          hughesYoungFarOffDiagonalBox T c H P X Y h k M N := by
  rw [hughesYoungLocalizedOffDiagonalBox_eq_near_add_far
    T c H P X Y hh]
  rw [hughesYoungNearShiftSum_eq_signedCentral_add_discrepancy]
  rfl

end RiemannZeta.GuthMaynard
