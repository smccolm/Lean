import GafniTao.HeathBrownMultiplicity

/-!
# The exact second moment of Heath-Brown's multiplicity

Squaring `nu(alpha)` produces the literal pairwise intersections of source
coefficient cells.  This file proves that identity and bounds the integral by
one cell volume times the number of nonempty intersections.  The subsequent
module identifies those intersections with Heath-Brown's `mathcal N`.
-/

open Finset Set MeasureTheory
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

noncomputable def heathBrownOverlappingCellPairs
    (N k H : ℕ) (f : ℝ → ℝ) : Finset (ℕ × ℕ) := by
  classical
  exact
    ((heathBrownInteriorIndices N H).product (heathBrownInteriorIndices N H)).filter
      fun p =>
        (heathBrownCoefficientCell k H f p.1 ∩
          heathBrownCoefficientCell k H f p.2).Nonempty

noncomputable def heathBrownCellIntersectionIndicator
    (k H : ℕ) (f : ℝ → ℝ) (p : ℕ × ℕ) :
    HeathBrownCoefficientTorus k → ℝ :=
  (heathBrownCoefficientCell k H f p.1 ∩
      heathBrownCoefficientCell k H f p.2).indicator (fun _ => 1)

theorem heathBrownCellIndicator_mul_cellIndicator
    (k H : ℕ) (f : ℝ → ℝ) (m n : ℕ)
    (α : HeathBrownCoefficientTorus k) :
    heathBrownCellIndicator k H f m α *
        heathBrownCellIndicator k H f n α =
      heathBrownCellIntersectionIndicator k H f (m, n) α := by
  by_cases hm : α ∈ heathBrownCoefficientCell k H f m <;>
    by_cases hn : α ∈ heathBrownCoefficientCell k H f n <;>
      simp [heathBrownCellIndicator, heathBrownCellIntersectionIndicator, hm, hn]

theorem heathBrownNu_sq_eq_pair_sum
    (N k H : ℕ) (f : ℝ → ℝ) (α : HeathBrownCoefficientTorus k) :
    (heathBrownNu N k H f α) ^ 2 =
      ∑ p ∈ (heathBrownInteriorIndices N H).product
          (heathBrownInteriorIndices N H),
        heathBrownCellIntersectionIndicator k H f p α := by
  unfold heathBrownNu
  rw [pow_two, Finset.sum_mul_sum]
  calc
    (∑ m ∈ heathBrownInteriorIndices N H,
        ∑ n ∈ heathBrownInteriorIndices N H,
          heathBrownCellIndicator k H f m α *
            heathBrownCellIndicator k H f n α) =
        ∑ m ∈ heathBrownInteriorIndices N H,
          ∑ n ∈ heathBrownInteriorIndices N H,
            heathBrownCellIntersectionIndicator k H f (m, n) α := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      exact heathBrownCellIndicator_mul_cellIndicator k H f m n α
    _ = _ := by
      simpa only using
        (Finset.sum_product
          (heathBrownInteriorIndices N H)
          (heathBrownInteriorIndices N H)
          (fun p => heathBrownCellIntersectionIndicator k H f p α)).symm

theorem integrable_heathBrownCellIntersectionIndicator
    (k H : ℕ) (f : ℝ → ℝ) (p : ℕ × ℕ) :
    Integrable (heathBrownCellIntersectionIndicator k H f p)
      (heathBrownCoefficientMeasure k) := by
  letI : IsFiniteMeasure (heathBrownCoefficientMeasure k) := by
    unfold heathBrownCoefficientMeasure
    infer_instance
  unfold heathBrownCellIntersectionIndicator
  exact (integrable_const (1 : ℝ)).indicator
    ((measurableSet_heathBrownCoefficientCell k H f p.1).inter
      (measurableSet_heathBrownCoefficientCell k H f p.2))

theorem integral_heathBrownCellIntersectionIndicator
    (k H : ℕ) (f : ℝ → ℝ) (p : ℕ × ℕ) :
    ∫ α, heathBrownCellIntersectionIndicator k H f p α
        ∂(heathBrownCoefficientMeasure k) =
      (heathBrownCoefficientMeasure k).real
        (heathBrownCoefficientCell k H f p.1 ∩
          heathBrownCoefficientCell k H f p.2) := by
  unfold heathBrownCellIntersectionIndicator
  exact integral_indicator_one
    ((measurableSet_heathBrownCoefficientCell k H f p.1).inter
      (measurableSet_heathBrownCoefficientCell k H f p.2))

theorem integral_heathBrownNu_sq_eq_intersections
    (N k H : ℕ) (f : ℝ → ℝ) :
    ∫ α, (heathBrownNu N k H f α) ^ 2
        ∂(heathBrownCoefficientMeasure k) =
      ∑ p ∈ (heathBrownInteriorIndices N H).product
          (heathBrownInteriorIndices N H),
        (heathBrownCoefficientMeasure k).real
          (heathBrownCoefficientCell k H f p.1 ∩
            heathBrownCoefficientCell k H f p.2) := by
  simp_rw [heathBrownNu_sq_eq_pair_sum]
  rw [integral_finsetSum _ fun p hp =>
    integrable_heathBrownCellIntersectionIndicator k H f p]
  simp_rw [integral_heathBrownCellIntersectionIndicator]

theorem integral_heathBrownNu_sq_le_overlap_count
    (N k H : ℕ) (hH : 2 ≤ H) (f : ℝ → ℝ) :
    ∫ α, (heathBrownNu N k H f α) ^ 2
        ∂(heathBrownCoefficientMeasure k) ≤
      ((heathBrownOverlappingCellPairs N k H f).card : ℝ) *
        (heathBrownCoefficientMeasure k).real
          (heathBrownCoefficientCell k H f 1) := by
  classical
  letI : IsFiniteMeasure (heathBrownCoefficientMeasure k) := by
    unfold heathBrownCoefficientMeasure
    infer_instance
  rw [integral_heathBrownNu_sq_eq_intersections]
  let S := (heathBrownInteriorIndices N H).product (heathBrownInteriorIndices N H)
  let P := heathBrownOverlappingCellPairs N k H f
  let μ := heathBrownCoefficientMeasure k
  let V := μ.real (heathBrownCoefficientCell k H f 1)
  have hmeasure (n : ℕ) :
      μ.real (heathBrownCoefficientCell k H f n) = V := by
    unfold V μ heathBrownCoefficientMeasure
    have hn := measure_heathBrownCoefficientCell (k := k) (H := H) hH f (n : ℝ)
    have h1 := measure_heathBrownCoefficientCell (k := k) (H := H) hH f (1 : ℝ)
    simpa only [Measure.real] using congrArg ENNReal.toReal (hn.trans h1.symm)
  have hterm (p : ℕ × ℕ) (hp : p ∈ S) :
      μ.real (heathBrownCoefficientCell k H f p.1 ∩
          heathBrownCoefficientCell k H f p.2) ≤
        (if p ∈ P then V else 0) := by
    by_cases hover :
        (heathBrownCoefficientCell k H f p.1 ∩
          heathBrownCoefficientCell k H f p.2).Nonempty
    · have hpP : p ∈ P := by
        simp only [P, heathBrownOverlappingCellPairs, Finset.mem_filter]
        exact ⟨hp, hover⟩
      rw [if_pos hpP]
      calc
        μ.real (heathBrownCoefficientCell k H f p.1 ∩
            heathBrownCoefficientCell k H f p.2) ≤
            μ.real (heathBrownCoefficientCell k H f p.1) :=
          measureReal_mono Set.inter_subset_left
        _ = V := hmeasure p.1
    · have hpP : p ∉ P := by
        simp only [P, heathBrownOverlappingCellPairs, Finset.mem_filter]
        exact fun h => hover h.2
      rw [if_neg hpP]
      have hempty : heathBrownCoefficientCell k H f p.1 ∩
          heathBrownCoefficientCell k H f p.2 = ∅ := not_nonempty_iff_eq_empty.mp hover
      simp [hempty]
  calc
    ∑ p ∈ S,
        μ.real (heathBrownCoefficientCell k H f p.1 ∩
          heathBrownCoefficientCell k H f p.2) ≤
        ∑ p ∈ S, (if p ∈ P then V else 0) :=
      Finset.sum_le_sum fun p hp => hterm p hp
    _ = (P.card : ℝ) * V := by
      have hPS : P ⊆ S := by
        intro p hp
        simp only [P, heathBrownOverlappingCellPairs, Finset.mem_filter] at hp
        exact hp.1
      rw [← Finset.sum_filter]
      rw [Finset.filter_mem_eq_inter]
      rw [Finset.inter_eq_right.mpr hPS]
      simp [nsmul_eq_mul]

#print axioms heathBrownNu_sq_eq_pair_sum
#print axioms integral_heathBrownNu_sq_eq_intersections
#print axioms integral_heathBrownNu_sq_le_overlap_count

end

end GafniTao
