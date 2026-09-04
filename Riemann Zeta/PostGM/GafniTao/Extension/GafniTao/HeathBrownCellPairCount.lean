import GafniTao.HeathBrownMultiplicitySecondMoment
import GafniTao.HeathBrownRefinedCountFinal

/-!
# From coefficient-cell intersections to Heath-Brown's `mathcal N`

This is the semantic bridge behind the source inequality for `integral nu^2`:
two source indices whose coefficient cells meet satisfy every simultaneous
distance-to-an-integer condition in the concrete finite count `mathcal N`.
-/

open Finset Set MeasureTheory Metric
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

theorem unitAddCircle_dist_real_coe
    (a b : ℝ) :
    dist (a : UnitAddCircle) (b : UnitAddCircle) =
      heathBrownDistanceToInteger (a - b) := by
  rw [dist_eq_norm]
  rw [← QuotientAddGroup.mk_sub]
  rw [UnitAddCircle.norm_eq]
  rfl

theorem heathBrown_center_coordinate_dist
    {k : ℕ} (f : ℝ → ℝ) (m n : ℝ) (j : Fin (k - 1)) :
    dist (heathBrownCoefficientCenter k f m j)
        (heathBrownCoefficientCenter k f n j) =
      heathBrownDistanceToInteger
        (heathBrownDerivativeCoordinate f ((j : ℕ) + 1) m -
          heathBrownDerivativeCoordinate f ((j : ℕ) + 1) n) := by
  unfold heathBrownCoefficientCenter heathBrownDerivativeCoordinate
  rw [unitAddCircle_dist_real_coe]

theorem heathBrown_cell_intersection_coordinate_bound
    {k H : ℕ} {f : ℝ → ℝ} {m n : ℕ}
    (hover : (heathBrownCoefficientCell k H f m ∩
      heathBrownCoefficientCell k H f n).Nonempty)
    (j : Fin (k - 1)) :
    heathBrownDistanceToInteger
        (heathBrownDerivativeCoordinate f ((j : ℕ) + 1) m -
          heathBrownDerivativeCoordinate f ((j : ℕ) + 1) n) ≤
      2 * (((H : ℝ) ^ ((j : ℕ) + 1))⁻¹) := by
  obtain ⟨α, hm, hn⟩ := hover
  have hmj : dist (α j)
      (heathBrownCoefficientCenter k f m j) ≤
        heathBrownCellRadius H j := by
    exact hm j (Set.mem_univ j)
  have hnj : dist (α j)
      (heathBrownCoefficientCenter k f n j) ≤
        heathBrownCellRadius H j := by
    exact hn j (Set.mem_univ j)
  rw [← heathBrown_center_coordinate_dist f m n j]
  calc
    dist (heathBrownCoefficientCenter k f m j)
        (heathBrownCoefficientCenter k f n j) ≤
      dist (heathBrownCoefficientCenter k f m j) (α j) +
        dist (α j) (heathBrownCoefficientCenter k f n j) := dist_triangle _ _ _
    _ ≤ heathBrownCellRadius H j + heathBrownCellRadius H j := by
      gcongr
      simpa only [dist_comm] using hmj
    _ = 2 * (((H : ℝ) ^ ((j : ℕ) + 1))⁻¹) := by
      simp [heathBrownCellRadius, two_mul]

theorem heathBrown_cell_intersection_derivative_bound
    {k H : ℕ} {f : ℝ → ℝ} {m n j : ℕ}
    (hj : j ∈ Finset.Icc 1 (k - 1))
    (hover : (heathBrownCoefficientCell k H f m ∩
      heathBrownCoefficientCell k H f n).Nonempty) :
    heathBrownDistanceToInteger
        (heathBrownDerivativeCoordinate f j m -
          heathBrownDerivativeCoordinate f j n) ≤
      2 * (((H : ℝ) ^ j)⁻¹) := by
  have hjBounds := Finset.mem_Icc.mp hj
  let q : Fin (k - 1) := ⟨j - 1, by omega⟩
  have hq : (q : ℕ) + 1 = j := by
    dsimp [q]
    omega
  simpa only [hq] using
    heathBrown_cell_intersection_coordinate_bound hover q

theorem heathBrownOverlappingCellPairs_subset_pairCount
    {N k H : ℕ} (f : ℝ → ℝ) :
    heathBrownOverlappingCellPairs N k H f ⊆
      heathBrownPairCount N k H f := by
  classical
  intro p hp
  simp only [heathBrownOverlappingCellPairs, Finset.mem_filter] at hp
  rw [mem_heathBrownPairCount]
  have hpRange := Finset.mem_product.mp hp.1
  have hmRange := Finset.mem_Icc.mp hpRange.1
  have hnRange := Finset.mem_Icc.mp hpRange.2
  refine ⟨hmRange.1, le_trans hmRange.2 (Nat.sub_le N H),
    hnRange.1, le_trans hnRange.2 (Nat.sub_le N H), ?_⟩
  intro j hj
  exact heathBrown_cell_intersection_derivative_bound hj hp.2

theorem card_heathBrownOverlappingCellPairs_le_pairCount
    {N k H : ℕ} (f : ℝ → ℝ) :
    (heathBrownOverlappingCellPairs N k H f).card ≤
      (heathBrownPairCount N k H f).card :=
  Finset.card_le_card (heathBrownOverlappingCellPairs_subset_pairCount f)

theorem integral_heathBrownNu_sq_le_pairCount
    (N k H : ℕ) (hH : 2 ≤ H) (f : ℝ → ℝ) :
    ∫ α, (heathBrownNu N k H f α) ^ 2
        ∂(heathBrownCoefficientMeasure k) ≤
      ((heathBrownPairCount N k H f).card : ℝ) *
        (heathBrownCoefficientMeasure k).real
          (heathBrownCoefficientCell k H f 1) := by
  have hover := integral_heathBrownNu_sq_le_overlap_count N k H hH f
  refine hover.trans ?_
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast card_heathBrownOverlappingCellPairs_le_pairCount f
  · exact measureReal_nonneg

#print axioms unitAddCircle_dist_real_coe
#print axioms heathBrown_cell_intersection_coordinate_bound
#print axioms heathBrownOverlappingCellPairs_subset_pairCount
#print axioms integral_heathBrownNu_sq_le_pairCount

end

end GafniTao
