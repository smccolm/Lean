import GafniTao.HeathBrownCellVolume

/-!
# Heath-Brown's coefficient-cell multiplicity

The function `heathBrownNu` is the literal finite multiplicity `nu(alpha)`
from the proof of Lemma 1: it counts the source indices `1 <= n <= N-H`
whose derivative-coefficient cell contains `alpha`.
-/

open Finset Set MeasureTheory
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

noncomputable def heathBrownCoefficientMeasure (k : ℕ) :
    Measure (HeathBrownCoefficientTorus k) :=
  Measure.pi (fun _ : Fin (k - 1) => AddCircle.haarAddCircle)

def heathBrownInteriorIndices (N H : ℕ) : Finset ℕ :=
  Finset.Icc 1 (N - H)

theorem card_heathBrownInteriorIndices (N H : ℕ) :
    (heathBrownInteriorIndices N H).card = N - H := by
  simp [heathBrownInteriorIndices]

noncomputable def heathBrownCellIndicator
    (k H : ℕ) (f : ℝ → ℝ) (n : ℕ) :
    HeathBrownCoefficientTorus k → ℝ :=
  (heathBrownCoefficientCell k H f n).indicator (fun _ => 1)

noncomputable def heathBrownNu
    (N k H : ℕ) (f : ℝ → ℝ) (α : HeathBrownCoefficientTorus k) : ℝ :=
  ∑ n ∈ heathBrownInteriorIndices N H,
    heathBrownCellIndicator k H f n α

theorem heathBrownCellIndicator_eq_one_iff
    {k H n : ℕ} {f : ℝ → ℝ} {α : HeathBrownCoefficientTorus k} :
    heathBrownCellIndicator k H f n α = 1 ↔
      α ∈ heathBrownCoefficientCell k H f n := by
  simp [heathBrownCellIndicator]

theorem heathBrownCellIndicator_nonneg
    (k H n : ℕ) (f : ℝ → ℝ) (α : HeathBrownCoefficientTorus k) :
    0 ≤ heathBrownCellIndicator k H f n α := by
  by_cases hα : α ∈ heathBrownCoefficientCell k H f n
  · simp [heathBrownCellIndicator, hα]
  · simp [heathBrownCellIndicator, hα]

theorem heathBrownNu_nonneg
    (N k H : ℕ) (f : ℝ → ℝ) (α : HeathBrownCoefficientTorus k) :
    0 ≤ heathBrownNu N k H f α := by
  unfold heathBrownNu
  exact Finset.sum_nonneg fun n hn => heathBrownCellIndicator_nonneg k H n f α

theorem integrable_heathBrownCellIndicator
    (k H n : ℕ) (f : ℝ → ℝ) :
    Integrable (heathBrownCellIndicator k H f n)
      (heathBrownCoefficientMeasure k) := by
  unfold heathBrownCellIndicator heathBrownCoefficientMeasure
  exact (integrable_const (1 : ℝ)).indicator
    (measurableSet_heathBrownCoefficientCell k H f n)

theorem integrable_heathBrownNu
    (N k H : ℕ) (f : ℝ → ℝ) :
    Integrable (heathBrownNu N k H f)
      (heathBrownCoefficientMeasure k) := by
  unfold heathBrownNu
  exact integrable_finsetSum _ fun n hn =>
    integrable_heathBrownCellIndicator k H n f

theorem integral_heathBrownCellIndicator
    (k H n : ℕ) (f : ℝ → ℝ) :
    ∫ α, heathBrownCellIndicator k H f n α
        ∂(heathBrownCoefficientMeasure k) =
      (heathBrownCoefficientMeasure k).real
        (heathBrownCoefficientCell k H f n) := by
  unfold heathBrownCellIndicator
  exact integral_indicator_one
    (measurableSet_heathBrownCoefficientCell k H f n)

theorem integral_heathBrownNu
    (N k H : ℕ) (hH : 2 ≤ H) (f : ℝ → ℝ) :
    ∫ α, heathBrownNu N k H f α ∂(heathBrownCoefficientMeasure k) =
      ((N - H : ℕ) : ℝ) *
        (heathBrownCoefficientMeasure k).real
          (heathBrownCoefficientCell k H f 1) := by
  unfold heathBrownNu
  rw [integral_finsetSum _ fun n hn =>
    integrable_heathBrownCellIndicator k H n f]
  simp_rw [integral_heathBrownCellIndicator]
  have hmeasure (n : ℕ) :
      (heathBrownCoefficientMeasure k).real
          (heathBrownCoefficientCell k H f n) =
        (heathBrownCoefficientMeasure k).real
          (heathBrownCoefficientCell k H f 1) := by
    unfold heathBrownCoefficientMeasure
    have hn := measure_heathBrownCoefficientCell (k := k) (H := H) hH f (n : ℝ)
    have h1 := measure_heathBrownCoefficientCell (k := k) (H := H) hH f (1 : ℝ)
    simpa only [Measure.real] using congrArg ENNReal.toReal (hn.trans h1.symm)
  simp_rw [hmeasure]
  rw [Finset.sum_const, card_heathBrownInteriorIndices]
  simp [nsmul_eq_mul]

#print axioms card_heathBrownInteriorIndices
#print axioms heathBrownCellIndicator_eq_one_iff
#print axioms heathBrownNu_nonneg
#print axioms integral_heathBrownNu

end

end GafniTao
