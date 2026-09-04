import GafniTao.HeathBrownCellPairCount

/-!
# Source-normalized first and second moments of `nu`

These are the two displayed coefficient-torus estimates in Heath-Brown's
Lemma 1, with the finite source interval retained exactly.
-/

open Finset Set MeasureTheory
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

theorem integral_heathBrownNu_exact
    (N k H : ℕ) (hH : 2 ≤ H) (f : ℝ → ℝ) :
    ∫ α, heathBrownNu N k H f α ∂(heathBrownCoefficientMeasure k) =
      ((N - H : ℕ) : ℝ) *
        ((2 : ℝ) ^ (k - 1) *
          (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹)) := by
  rw [integral_heathBrownNu N k H hH f]
  unfold heathBrownCoefficientMeasure
  rw [measureReal_heathBrownCoefficientCell_exact hH]

theorem integral_heathBrownNu_sq_source_bound
    (N k H : ℕ) (hH : 2 ≤ H) (f : ℝ → ℝ) :
    ∫ α, (heathBrownNu N k H f α) ^ 2
        ∂(heathBrownCoefficientMeasure k) ≤
      ((heathBrownPairCount N k H f).card : ℝ) *
        ((2 : ℝ) ^ (k - 1) *
          (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹)) := by
  have h := integral_heathBrownNu_sq_le_pairCount N k H hH f
  unfold heathBrownCoefficientMeasure at h ⊢
  rw [measureReal_heathBrownCoefficientCell_exact hH] at h
  exact h

#print axioms integral_heathBrownNu_exact
#print axioms integral_heathBrownNu_sq_source_bound

end

end GafniTao
