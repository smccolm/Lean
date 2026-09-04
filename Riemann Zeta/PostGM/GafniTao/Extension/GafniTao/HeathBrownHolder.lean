import GafniTao.HeathBrownCenterWeyl
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# The three-factor Hölder step in Heath-Brown Lemma 1

This is the exact measure-theoretic inequality used for
`I(x) = ∫ |S(x; α)| ν(α) dα`.  The three factors are the `2s`-moment
of the Weyl sum, the second moment of `ν`, and the first moment of `ν`.
The statement is in `ENNReal`, so no hidden finiteness or division
hypothesis is needed.
-/

open MeasureTheory

namespace GafniTao

noncomputable section

private def heathBrownHolderFunction
    {X : Type*} (B : X → ENNReal) : Bool → X → ENNReal
  | false => fun x => B x ^ 2
  | true => B

private def heathBrownHolderExponent (s : ℕ) : Bool → ℝ
  | false => 1 / (2 * (s : ℝ))
  | true => 1 - 1 / (s : ℝ)

private theorem heathBrownHolderExponent_sum
    {s : ℕ} (hs : 1 ≤ s) :
    1 / (2 * (s : ℝ)) + ∑ i : Bool, heathBrownHolderExponent s i = 1 := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  rw [Fintype.sum_bool]
  simp [heathBrownHolderExponent]
  field_simp
  ring

private theorem heathBrownHolderExponent_nonneg
    {s : ℕ} (hs : 1 ≤ s) (i : Bool) :
    0 ≤ heathBrownHolderExponent s i := by
  cases i
  · simp only [heathBrownHolderExponent]
    positivity
  · simp only [heathBrownHolderExponent]
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    exact sub_nonneg.mpr (by
      simpa using one_div_le_one_div_of_le zero_lt_one hsR)

private theorem prod_heathBrownHolderFunction
    {X : Type*} (A B : X → ENNReal) {s : ℕ} (hs : 1 ≤ s) (x : X) :
    (A x ^ (2 * s)) ^ (1 / (2 * (s : ℝ))) *
        ∏ i : Bool,
          (heathBrownHolderFunction B i x) ^
            (heathBrownHolderExponent s i) =
      A x * B x := by
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  have htwoS : (2 * (s : ℝ)) ≠ 0 := by positivity
  have hq : 0 ≤ 1 / (2 * (s : ℝ)) := by positivity
  have hr : 0 ≤ 1 - 1 / (s : ℝ) := by
    have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
    exact sub_nonneg.mpr (by
      simpa using one_div_le_one_div_of_le zero_lt_one hsR)
  rw [Fintype.prod_bool]
  simp only [heathBrownHolderFunction, heathBrownHolderExponent]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [show ((2 * s : ℕ) : ℝ) * (1 / (2 * (s : ℝ))) = 1 by
    push_cast
    field_simp]
  rw [ENNReal.rpow_one]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  rw [show ((2 : ℕ) : ℝ) * (1 / (2 * (s : ℝ))) = 1 / (s : ℝ) by
    norm_num
    field_simp]
  rw [← ENNReal.rpow_add_of_nonneg _ _ hr (by positivity)]
  rw [show (1 - 1 / (s : ℝ)) + 1 / (s : ℝ) = 1 by ring]
  rw [ENNReal.rpow_one]

/-- Heath-Brown's three-factor Hölder inequality, in the exact root form
used in Lemma 1. -/
theorem heathBrown_lintegral_mul_le_three_moments
    {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {A B : X → ENNReal} (hA : AEMeasurable A μ) (hB : AEMeasurable B μ)
    {s : ℕ} (hs : 1 ≤ s) :
    ∫⁻ x, A x * B x ∂μ ≤
      (∫⁻ x, A x ^ (2 * s) ∂μ) ^ (1 / (2 * (s : ℝ))) *
        (∫⁻ x, B x ^ 2 ∂μ) ^ (1 / (2 * (s : ℝ))) *
        (∫⁻ x, B x ∂μ) ^ (1 - 1 / (s : ℝ)) := by
  have hholder := ENNReal.lintegral_mul_prod_norm_pow_le
    (Finset.univ : Finset Bool)
    (μ := μ)
    (g := fun x => A x ^ (2 * s))
    (f := heathBrownHolderFunction B)
    (q := 1 / (2 * (s : ℝ)))
    (hA.pow_const (2 * s))
    (fun i hi => by
      cases i
      · exact hB.pow_const 2
      · exact hB)
    (p := heathBrownHolderExponent s)
    (by simpa using heathBrownHolderExponent_sum hs)
    (by positivity)
    (fun i hi => heathBrownHolderExponent_nonneg hs i)
  rw [show (∫⁻ x, A x * B x ∂μ) =
      ∫⁻ x, (A x ^ (2 * s)) ^ (1 / (2 * (s : ℝ))) *
        ∏ i : Bool,
          (heathBrownHolderFunction B i x) ^
            (heathBrownHolderExponent s i) ∂μ by
    apply lintegral_congr
    intro x
    exact (prod_heathBrownHolderFunction A B hs x).symm]
  refine hholder.trans_eq ?_
  rw [Fintype.prod_bool]
  simp only [heathBrownHolderFunction, heathBrownHolderExponent]
  ring

#print axioms heathBrown_lintegral_mul_le_three_moments

end

end GafniTao
