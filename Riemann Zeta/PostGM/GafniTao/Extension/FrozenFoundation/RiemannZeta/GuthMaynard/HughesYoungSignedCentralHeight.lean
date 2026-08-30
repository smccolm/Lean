import RiemannZeta.GuthMaynard.HughesYoungCentralSeriesFubiniNegative
import RiemannZeta.GuthMaynard.HughesYoungIntegratedDiscrepancy

open Complex Filter MeasureTheory Set
open scoped BigOperators ENNReal Interval

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Source-order height expansion of the signed Hughes--Young central term

DFI is applied pointwise in the compact Mellin ordinate.  The resulting
signed equation-(27) series is then expanded through the physical-height
average, without taking a norm across either sign of the shift.
-/

/-- The actual pointwise signed central object used by the DFI consumer is
exactly the compact Mellin integral of the finite signed shift family of
height integrals. -/
theorem hughesYoungIntegratedPointwiseSignedCentral_eq_heightIntegrals
    {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c)
    (H : ℝ) {X Y : ℝ} (hX : 1 ≤ X) (hY : 1 ≤ Y)
    {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (s : Finset ℤ)
    (hs : ∀ r ∈ s, r ≠ 0) :
    hughesYoungIntegratedPointwiseSignedCentral T c H X Y h k s =
      ∫ u in -H..H,
        ∑ r ∈ s, ∫ t : ℝ,
          (hughesYoungHeightWeight T t : ℂ) *
            dfiSignedCentralSeries
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
              (hughesYoungReducedLocalizedMellinWeight
                T t c u X Y h k) := by
  have ha : 0 < hughesYoungReducedLeft h k :=
    hughesYoungReducedLeft_pos hh
  have hb : 0 < hughesYoungReducedRight h k :=
    hughesYoungReducedRight_pos hh hk
  unfold hughesYoungIntegratedPointwiseSignedCentral
  apply intervalIntegral.integral_congr
  intro u _hu
  change
    (T : ℂ) *
          ∑ r ∈ s,
            dfiSignedCentralSeries
              (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
              (hughesYoungReducedCleanedShiftWeight T c u X Y h k r) =
      ∑ r ∈ s, ∫ t : ℝ,
        (hughesYoungHeightWeight T t : ℂ) *
          dfiSignedCentralSeries
            (hughesYoungReducedLeft h k) (hughesYoungReducedRight h k) r
            (hughesYoungReducedLocalizedMellinWeight T t c u X Y h k)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [dfiSignedCentralSeries_reducedCleaned_eq_heightIntegral
    hT hc u hX hY hh hk ha hb (hs r hr)]
  field_simp [hT.ne']

end RiemannZeta.GuthMaynard
