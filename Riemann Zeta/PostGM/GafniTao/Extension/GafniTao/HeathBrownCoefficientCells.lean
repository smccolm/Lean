import GafniTao.HeathBrownAbelTransfer
import GafniTao.FordVinogradovIntegral
import Mathlib.MeasureTheory.Group.AddCircle

/-!
# Coefficient cells in Heath-Brown Lemma 1

The source integrates over the coefficient torus.  For each source index
`n`, its cell consists of coefficient vectors within `H^{-(j+1)}` of
`f^(j+1)(n)/(j+1)!` modulo one.
-/

open Finset Set MeasureTheory Metric
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

abbrev HeathBrownCoefficientTorus (k : ℕ) := UnitAddTorus (Fin (k - 1))

noncomputable def heathBrownCoefficientCenter
    (k : ℕ) (f : ℝ → ℝ) (n : ℝ) : HeathBrownCoefficientTorus k :=
  fun j => ((iteratedDeriv ((j : ℕ) + 1) f n /
    (((j : ℕ) + 1).factorial : ℝ) : ℝ) : UnitAddCircle)

noncomputable def heathBrownCellRadius (H : ℕ) (j : ℕ) : ℝ :=
  ((H : ℝ) ^ (j + 1))⁻¹

def heathBrownCoefficientCell
    (k H : ℕ) (f : ℝ → ℝ) (n : ℝ) : Set (HeathBrownCoefficientTorus k) :=
  Set.univ.pi fun j => Metric.closedBall (heathBrownCoefficientCenter k f n j)
    (heathBrownCellRadius H j)

theorem measurableSet_heathBrownCoefficientCell
    (k H : ℕ) (f : ℝ → ℝ) (n : ℝ) :
    MeasurableSet (heathBrownCoefficientCell k H f n) := by
  unfold heathBrownCoefficientCell
  exact MeasurableSet.pi countable_univ fun j hj => measurableSet_closedBall

theorem heathBrownCellRadius_pos
    {H : ℕ} (hH : 1 ≤ H) (j : ℕ) :
    0 < heathBrownCellRadius H j := by
  unfold heathBrownCellRadius
  positivity

theorem two_mul_heathBrownCellRadius_le_one
    {H : ℕ} (hH : 2 ≤ H) (j : ℕ) :
    2 * heathBrownCellRadius H j ≤ 1 := by
  unfold heathBrownCellRadius
  have hpow : (2 : ℝ) ≤ (H : ℝ) ^ (j + 1) := by
    calc
      (2 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
      _ ≤ (H : ℝ) ^ (j + 1) := by
        have hHreal : (1 : ℝ) ≤ H := by exact_mod_cast (by omega : 1 ≤ H)
        simpa only [pow_one] using
          (pow_le_pow_right₀ hHreal (by omega : 1 ≤ j + 1))
  have hpowPos : 0 < (H : ℝ) ^ (j + 1) := by positivity
  rw [mul_inv_le_iff₀ hpowPos]
  simpa [mul_comm] using hpow

theorem measure_heathBrownCoefficientCell
    {k H : ℕ} (hH : 2 ≤ H) (f : ℝ → ℝ) (n : ℝ) :
    Measure.pi (fun _ : Fin (k - 1) => AddCircle.haarAddCircle)
        (heathBrownCoefficientCell k H f n) =
      ∏ j : Fin (k - 1), ENNReal.ofReal (2 * heathBrownCellRadius H j) := by
  unfold heathBrownCoefficientCell
  rw [Measure.pi_pi]
  apply Finset.prod_congr rfl
  intro j hj
  have hhaar : (@AddCircle.haarAddCircle 1 inferInstance) = volume := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    simp
  rw [hhaar]
  rw [AddCircle.volume_closedBall]
  rw [min_eq_right (two_mul_heathBrownCellRadius_le_one hH j)]

#print axioms measurableSet_heathBrownCoefficientCell
#print axioms measure_heathBrownCoefficientCell

end

end GafniTao
