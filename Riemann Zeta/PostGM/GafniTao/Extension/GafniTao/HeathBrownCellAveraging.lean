import GafniTao.HeathBrownCoefficientAbel
import GafniTao.HeathBrownIntegratedHolder

/-!
# Averaging Heath-Brown's coefficient-cell Abel estimate

This file performs the literal sum over source cells which follows the second
Abel summation in Heath-Brown's proof.  The overlap multiplicity is the
previously defined function `heathBrownNu`; no uniform-overlap surrogate is
introduced.
-/

open Complex Finset Set MeasureTheory
open scoped BigOperators ENNReal

namespace GafniTao

noncomputable section

noncomputable def heathBrownIntegratedWeyl
    (N k H Q : ℕ) (f : ℝ → ℝ) : ENNReal :=
  ∫⁻ α : HeathBrownCoefficientTorus k,
    ENNReal.ofReal ‖heathBrownWeylSum k Q α‖ *
      ENNReal.ofReal (heathBrownNu N k H f α)
      ∂(heathBrownCoefficientMeasure k)

theorem measurable_heathBrownCellIndicator
    (k H n : ℕ) (f : ℝ → ℝ) :
    Measurable (heathBrownCellIndicator k H f n) := by
  unfold heathBrownCellIndicator
  exact measurable_const.indicator
    (measurableSet_heathBrownCoefficientCell k H f n)

theorem measurable_heathBrownNu
    (N k H : ℕ) (f : ℝ → ℝ) :
    Measurable (heathBrownNu N k H f) := by
  unfold heathBrownNu
  exact Finset.measurable_sum (heathBrownInteriorIndices N H) fun n hn =>
    measurable_heathBrownCellIndicator k H n f

theorem heathBrown_cellwise_center_le
    {N k H Q : ℕ} (hH : 2 ≤ H) (hQ : 1 ≤ Q) (hQH : Q ≤ H)
    (f : ℝ → ℝ) (α : HeathBrownCoefficientTorus k) :
    ∑ n ∈ heathBrownInteriorIndices N H,
        heathBrownCellIndicator k H f n α *
          ‖heathBrownWeylSum k Q
            (heathBrownCoefficientCenter k f n)‖ ≤
      ‖heathBrownWeylSum k Q α‖ * heathBrownNu N k H f α +
        (2 * Real.pi * ((k : ℝ) ^ 2 / H)) *
          ∑ j ∈ Finset.Ico 1 Q,
            ‖heathBrownWeylSum k j α‖ * heathBrownNu N k H f α := by
  unfold heathBrownNu
  calc
    ∑ n ∈ heathBrownInteriorIndices N H,
        heathBrownCellIndicator k H f n α *
          ‖heathBrownWeylSum k Q
            (heathBrownCoefficientCenter k f n)‖ ≤
      ∑ n ∈ heathBrownInteriorIndices N H,
        heathBrownCellIndicator k H f n α *
          (‖heathBrownWeylSum k Q α‖ +
            (2 * Real.pi * ((k : ℝ) ^ 2 / H)) *
              ∑ j ∈ Finset.Ico 1 Q, ‖heathBrownWeylSum k j α‖) := by
      apply Finset.sum_le_sum
      intro n hn
      by_cases hα : α ∈ heathBrownCoefficientCell k H f n
      · rw [show heathBrownCellIndicator k H f n α = 1 by
          simp [heathBrownCellIndicator, hα]]
        simpa only [one_mul] using
          norm_heathBrown_centerWeyl_le hH hQ hQH hα
      · rw [show heathBrownCellIndicator k H f n α = 0 by
          simp [heathBrownCellIndicator, hα]]
        simp
    _ = _ := by
      rw [← Finset.sum_mul]
      have hsum :
          (∑ j ∈ Finset.Ico 1 Q,
              ‖heathBrownWeylSum k j α‖ *
                ∑ n ∈ heathBrownInteriorIndices N H,
                  heathBrownCellIndicator k H f n α) =
            (∑ n ∈ heathBrownInteriorIndices N H,
                heathBrownCellIndicator k H f n α) *
              ∑ j ∈ Finset.Ico 1 Q,
                ‖heathBrownWeylSum k j α‖ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [mul_comm]
      rw [hsum]
      ring

theorem lintegral_heathBrownCellIndicator_mul_const
    {k H n : ℕ} (f : ℝ → ℝ) (C : ℝ) :
    ∫⁻ α : HeathBrownCoefficientTorus k,
        ENNReal.ofReal (heathBrownCellIndicator k H f n α) *
          ENNReal.ofReal C ∂(heathBrownCoefficientMeasure k) =
      (heathBrownCoefficientMeasure k)
          (heathBrownCoefficientCell k H f n) * ENNReal.ofReal C := by
  calc
    (∫⁻ α : HeathBrownCoefficientTorus k,
        ENNReal.ofReal (heathBrownCellIndicator k H f n α) *
          ENNReal.ofReal C ∂(heathBrownCoefficientMeasure k)) =
      ∫⁻ α in heathBrownCoefficientCell k H f n,
        ENNReal.ofReal C ∂(heathBrownCoefficientMeasure k) := by
        rw [← lintegral_indicator
          (measurableSet_heathBrownCoefficientCell k H f n)]
        apply lintegral_congr
        intro α
        by_cases hα : α ∈ heathBrownCoefficientCell k H f n
        · simp [Set.indicator, heathBrownCellIndicator, hα]
        · simp [Set.indicator, heathBrownCellIndicator, hα]
    _ = _ := by simp [mul_comm]

theorem heathBrown_cellwise_center_lintegral_le
    {N k H Q : ℕ} (hH : 2 ≤ H) (hQ : 1 ≤ Q) (hQH : Q ≤ H)
    (f : ℝ → ℝ) :
    ENNReal.ofReal
        ((2 : ℝ) ^ (k - 1) *
          (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹)) *
        ∑ n ∈ heathBrownInteriorIndices N H,
          ENNReal.ofReal ‖heathBrownWeylSum k Q
            (heathBrownCoefficientCenter k f n)‖ ≤
      heathBrownIntegratedWeyl N k H Q f +
        ENNReal.ofReal (2 * Real.pi * ((k : ℝ) ^ 2 / H)) *
          ∑ j ∈ Finset.Ico 1 Q,
            heathBrownIntegratedWeyl N k H j f := by
  let μ := heathBrownCoefficientMeasure k
  let c : ℝ := 2 * Real.pi * ((k : ℝ) ^ 2 / H)
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint (α : HeathBrownCoefficientTorus k) :
      ∑ n ∈ heathBrownInteriorIndices N H,
          ENNReal.ofReal (heathBrownCellIndicator k H f n α) *
            ENNReal.ofReal ‖heathBrownWeylSum k Q
              (heathBrownCoefficientCenter k f n)‖ ≤
        ENNReal.ofReal ‖heathBrownWeylSum k Q α‖ *
            ENNReal.ofReal (heathBrownNu N k H f α) +
          ENNReal.ofReal c *
            ∑ j ∈ Finset.Ico 1 Q,
              ENNReal.ofReal ‖heathBrownWeylSum k j α‖ *
                ENNReal.ofReal (heathBrownNu N k H f α) := by
    have h := ENNReal.ofReal_le_ofReal
      (heathBrown_cellwise_center_le (N := N) hH hQ hQH f α)
    rw [ENNReal.ofReal_sum_of_nonneg] at h
    · simp_rw [ENNReal.ofReal_mul
          (heathBrownCellIndicator_nonneg k H _ f α)] at h
      have htail :
          0 ≤ c * ∑ j ∈ Finset.Ico 1 Q,
            ‖heathBrownWeylSum k j α‖ * heathBrownNu N k H f α :=
        mul_nonneg hc (Finset.sum_nonneg fun j hj =>
          mul_nonneg (norm_nonneg _)
            (heathBrownNu_nonneg N k H f α))
      rw [ENNReal.ofReal_add
        (mul_nonneg (norm_nonneg _)
          (heathBrownNu_nonneg N k H f α)) htail] at h
      rw [ENNReal.ofReal_mul (norm_nonneg _),
        ENNReal.ofReal_mul hc] at h
      rw [ENNReal.ofReal_sum_of_nonneg] at h
      · simp_rw [ENNReal.ofReal_mul (norm_nonneg _)] at h
        simpa only [c] using h
      · intro j hj
        exact mul_nonneg (norm_nonneg _)
          (heathBrownNu_nonneg N k H f α)
    · intro n hn
      exact mul_nonneg (heathBrownCellIndicator_nonneg k H n f α)
        (norm_nonneg _)
  have hmono := lintegral_mono (μ := μ) hpoint
  have hleft :
      (∫⁻ α : HeathBrownCoefficientTorus k,
          ∑ n ∈ heathBrownInteriorIndices N H,
            ENNReal.ofReal (heathBrownCellIndicator k H f n α) *
              ENNReal.ofReal ‖heathBrownWeylSum k Q
                (heathBrownCoefficientCenter k f n)‖ ∂μ) =
        ENNReal.ofReal
            ((2 : ℝ) ^ (k - 1) *
              (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹)) *
          ∑ n ∈ heathBrownInteriorIndices N H,
            ENNReal.ofReal ‖heathBrownWeylSum k Q
              (heathBrownCoefficientCenter k f n)‖ := by
    rw [lintegral_finsetSum]
    · simp_rw [μ, lintegral_heathBrownCellIndicator_mul_const f _]
      have hcell (n : ℕ) :
          (heathBrownCoefficientMeasure k)
              (heathBrownCoefficientCell k H f n) =
            ENNReal.ofReal
              ((2 : ℝ) ^ (k - 1) *
                (((H : ℝ) ^ heathBrownCriticalMoment k)⁻¹)) := by
        exact measure_heathBrownCoefficientCell_exact hH f (n : ℝ)
      simp_rw [hcell]
      rw [Finset.mul_sum]
    · intro n hn
      exact (measurable_heathBrownCellIndicator k H n f).ennreal_ofReal.mul
        measurable_const
  rw [hleft] at hmono
  -- The right side is exactly `I(Q) + c * sum_{j<Q} I(j)` after Tonelli.
  have hnu : Measurable (fun α : HeathBrownCoefficientTorus k =>
      ENNReal.ofReal (heathBrownNu N k H f α)) :=
    (measurable_heathBrownNu N k H f).ennreal_ofReal
  have hweyl (j : ℕ) : Measurable (fun α : HeathBrownCoefficientTorus k =>
      ENNReal.ofReal ‖heathBrownWeylSum k j α‖) :=
    (ENNReal.continuous_ofReal.comp
      (continuous_fordVinogradovWeylSum (k - 1) j).norm).measurable
  have hterm (j : ℕ) : Measurable (fun α : HeathBrownCoefficientTorus k =>
      ENNReal.ofReal ‖heathBrownWeylSum k j α‖ *
        ENNReal.ofReal (heathBrownNu N k H f α)) :=
    (hweyl j).mul hnu
  have hsum : Measurable (fun α : HeathBrownCoefficientTorus k =>
      ∑ j ∈ Finset.Ico 1 Q,
        ENNReal.ofReal ‖heathBrownWeylSum k j α‖ *
          ENNReal.ofReal (heathBrownNu N k H f α)) :=
    Finset.measurable_sum (Finset.Ico 1 Q) fun j hj => hterm j
  have hright :
      (∫⁻ α : HeathBrownCoefficientTorus k,
          ENNReal.ofReal ‖heathBrownWeylSum k Q α‖ *
              ENNReal.ofReal (heathBrownNu N k H f α) +
            ENNReal.ofReal c *
              ∑ j ∈ Finset.Ico 1 Q,
                ENNReal.ofReal ‖heathBrownWeylSum k j α‖ *
                  ENNReal.ofReal (heathBrownNu N k H f α) ∂μ) =
        heathBrownIntegratedWeyl N k H Q f +
          ENNReal.ofReal c *
            ∑ j ∈ Finset.Ico 1 Q,
              heathBrownIntegratedWeyl N k H j f := by
    rw [lintegral_add_left (hterm Q)]
    rw [lintegral_const_mul _ hsum]
    rw [lintegral_finsetSum (Finset.Ico 1 Q) fun j hj => hterm j]
    rfl
  rw [hright] at hmono
  simpa only [c] using hmono

#print axioms heathBrown_cellwise_center_le
#print axioms measurable_heathBrownCellIndicator
#print axioms measurable_heathBrownNu
#print axioms lintegral_heathBrownCellIndicator_mul_const
#print axioms heathBrown_cellwise_center_lintegral_le

end

end GafniTao
