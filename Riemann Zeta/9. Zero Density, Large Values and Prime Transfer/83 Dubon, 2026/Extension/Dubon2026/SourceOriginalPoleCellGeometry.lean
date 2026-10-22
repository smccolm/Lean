import Dubon2026.SourceOriginalInverseJCells
import Dubon2026.SourceCellReciprocalGeometry

/-! DUB-17/18 -> original Abel-Jacobi -> exterior original-place cells.
The reciprocal of a sufficiently large window lies inside the actual inverse-j
chart scale. Original valuation orders identify its preimage with all poles
and the regular j values outside the window interior.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Metric
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem reciprocal_region_small {W R : RadialRegion} {ε : ℝ} (hε : 0 < ε)
    (hmem : ∀ w : ℂ, w ≠ 0 → (w ∈ R.K ↔ w⁻¹ ∉ W.Kint))
    (hlarge : closedBall 0 ε⁻¹ ⊆ W.Kint) : R.K ⊆ ball 0 ε := by
  intro w hw
  rw [mem_ball, dist_zero_right]
  by_cases hw0 : w = 0
  · simpa only [hw0, norm_zero] using hε
  · by_contra hn
    have hinv : w⁻¹ ∈ closedBall 0 ε⁻¹ := by
      rw [mem_closedBall, dist_zero_right, norm_inv]
      exact (inv_le_inv₀ (norm_pos_iff.mpr hw0) hε).mpr (le_of_not_gt hn)
    exact ((hmem w hw0).mp hw) (hlarge hinv)

theorem original_inverse_j_mem_reciprocal_iff (W R : RadialRegion)
    (hW : W.q = 0) (hR : R.q = 0)
    (hmem : ∀ w : ℂ, w ≠ 0 → (w ∈ R.K ↔ w⁻¹ ∉ W.Kint)) (P : Place ℂ F) :
    ((jOver N ℂ)⁻¹ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ ∈ R.K) ↔
    (jOver N ℂ ∉ P.toValuationSubring ∨
      (jOver N ℂ ∈ P.toValuationSubring ∧ originalPlaceEval N ℂ P (jOver N ℂ) ∉ W.Kint)) := by
  have hj : jOver N ℂ ≠ 0 := fun hz => transcendental_jOver N ℂ (hz ▸ isAlgebraic_zero)
  have hW0 : (0 : ℂ) ∈ W.Kint := by
    change ‖(0 : ℂ) - W.q‖ < W.r (Complex.arg (0 - W.q))
    simpa only [hW, sub_zero, norm_zero] using W.hpos (Complex.arg (0 : ℂ))
  have hR0 : (0 : ℂ) ∈ R.K := by
    change ‖(0 : ℂ) - R.q‖ ≤ R.r (Complex.arg (0 - R.q))
    simpa only [hR, sub_zero, norm_zero] using (R.hpos (Complex.arg (0 : ℂ))).le
  constructor
  · rintro ⟨hi, hval⟩
    by_cases hr : jOver N ℂ ∈ P.toValuationSubring
    · have ho : P.ord (jOver N ℂ) = 0 := by
        have h1 := P.ord_nonneg_of_mem hr
        have h2 := P.ord_nonneg_of_mem hi
        rw [Place.ord_inv] at h2
        omega
      have hne : originalPlaceEval N ℂ P (jOver N ℂ) ≠ 0 := by
        intro hz
        have hp := (originalPlaceEval_eq_zero_iff_ord_pos N ℂ P hr hj).mp hz
        rw [ho] at hp
        exact lt_irrefl _ hp
      refine Or.inr ⟨hr, ?_⟩
      rw [originalPlaceEval_inv] at hval
      simpa only [inv_inv] using (hmem _ (inv_ne_zero hne)).mp hval
    · exact Or.inl hr
  · rintro (hp | ⟨hr, hout⟩)
    · have ho : P.ord (jOver N ℂ) < 0 := by
        by_contra hn
        exact hp (P.mem_of_ord_nonneg (le_of_not_gt hn))
      have hi : (jOver N ℂ)⁻¹ ∈ P.toValuationSubring :=
        P.mem_of_ord_nonneg (by rw [Place.ord_inv]; omega)
      have hz : originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ = 0 :=
        (originalPlaceEval_eq_zero_iff_ord_pos N ℂ P hi (inv_ne_zero hj)).mpr
          (by rw [Place.ord_inv]; omega)
      exact ⟨hi, hz.symm ▸ hR0⟩
    · have hne : originalPlaceEval N ℂ P (jOver N ℂ) ≠ 0 := fun hz => hout (hz.symm ▸ hW0)
      have ho : P.ord (jOver N ℂ) = 0 := by
        have h1 := P.ord_nonneg_of_mem hr
        have h2 : ¬ 0 < P.ord (jOver N ℂ) := fun hp => hne
          ((originalPlaceEval_eq_zero_iff_ord_pos N ℂ P hr hj).mpr hp)
        omega
      refine ⟨P.mem_of_ord_nonneg (by rw [Place.ord_inv, ho, neg_zero]), ?_⟩
      rw [originalPlaceEval_inv, hmem _ (inv_ne_zero hne), inv_inv]
      exact hout

end
end Dubon2026.SourceFunctionField.CellGeometry
