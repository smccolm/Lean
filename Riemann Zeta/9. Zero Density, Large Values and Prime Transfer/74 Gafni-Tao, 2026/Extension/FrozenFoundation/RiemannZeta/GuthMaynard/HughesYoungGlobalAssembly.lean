import RiemannZeta.GuthMaynard.HughesYoungBoundaryBound
import RiemannZeta.GuthMaynard.HughesYoungBoxScaleSplit

open Complex Finset MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# Global finite Hughes--Young box assembly
-/

/-- Exact reconstruction of the finite off-diagonal rectangle using only
ordinary localized boxes.  The double initial box is diagonal and vanishes;
the two mixed boundary families are the ordinary scale-`1 / sqrt 2` boxes. -/
theorem hughesYoungFiniteOffDiagonalBox_eq_initial_add_regular_boxes
    (T c H : ℝ) {h k M N K₁ K₂ : ℕ}
    (hh : 0 < h) (hk : 0 < k)
    (hM : (((hughesYoungReducedLeft h k) * M : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K₁ + 1))
    (hN : (((hughesYoungReducedRight h k) * N : ℕ) : ℝ) ≤
      hughesYoungDyadicRatio ^ (K₂ + 1)) :
    hughesYoungFiniteOffDiagonalBox T c H h k M N =
      (∑ j ∈ Finset.range (K₂ + 1),
        hughesYoungLocalizedOffDiagonalBox T c H
          (1 / hughesYoungDyadicRatio) (hughesYoungDyadicScale j)
          h k M N) +
      (∑ i ∈ Finset.range (K₁ + 1),
        hughesYoungLocalizedOffDiagonalBox T c H
          (hughesYoungDyadicScale i) (1 / hughesYoungDyadicRatio)
          h k M N) +
      (∑ i ∈ Finset.range (K₁ + 1),
        ∑ j ∈ Finset.range (K₂ + 1),
          hughesYoungLocalizedOffDiagonalBox T c H
            (hughesYoungDyadicScale i) (hughesYoungDyadicScale j)
            h k M N) := by
  rw [hughesYoungFiniteOffDiagonalBox_eq_boundary_add_dyadic
    T c H hh hk hM hN]
  rw [finiteQuadraticDivisorOffDiagonalPiece_boundary_boundary_eq_zero
    hh hk (hughesYoungIntegratedSourceWeight T c H h k)]
  simp_rw [finiteQuadraticDivisorOffDiagonalPiece_boundary_left_eq_initialBox
    T c H _ hh]
  simp_rw [finiteQuadraticDivisorOffDiagonalPiece_boundary_right_eq_initialBox
    T c H _ hh hk]
  ring

end RiemannZeta.GuthMaynard
