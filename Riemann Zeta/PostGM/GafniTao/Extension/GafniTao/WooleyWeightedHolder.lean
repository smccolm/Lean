import Mathlib

/-!
# The weighted Hölder inequality used in Wooley (3.9)

Mathlib supplies the one-over-`p` form.  The source repeatedly uses its
`p`-th-power consequence.  We isolate that consequence with all positivity
hypotheses visible.
-/

open Finset
open scoped BigOperators

namespace GafniTao

noncomputable section

theorem wooley_weighted_rpow_sum_le
    {ι : Type*} (t : Finset ι) (w f : ι → ℝ) {p : ℝ}
    (hp : 1 ≤ p) (hw : ∀ i, 0 ≤ w i) (hf : ∀ i, 0 ≤ f i) :
    (∑ i ∈ t, w i * f i) ^ p ≤
      (∑ i ∈ t, w i) ^ (p - 1) *
        ∑ i ∈ t, w i * f i ^ p := by
  let A : ℝ := ∑ i ∈ t, w i * f i
  let W : ℝ := ∑ i ∈ t, w i
  let D : ℝ := ∑ i ∈ t, w i * f i ^ p
  have hA : 0 ≤ A := by
    dsimp [A]
    exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i) (hf i)
  have hW : 0 ≤ W := by
    dsimp [W]
    exact Finset.sum_nonneg fun i hi => hw i
  have hD : 0 ≤ D := by
    dsimp [D]
    exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hw i) (Real.rpow_nonneg (hf i) p)
  have hpPos : 0 < p := zero_lt_one.trans_le hp
  have hHolder : A ≤ W ^ (1 - p⁻¹) * D ^ p⁻¹ := by
    simpa only [A, W, D] using
      Real.inner_le_weight_mul_Lp_of_nonneg t hp w f hw hf
  have hRaised := Real.rpow_le_rpow hA hHolder hpPos.le
  calc
    A ^ p ≤ (W ^ (1 - p⁻¹) * D ^ p⁻¹) ^ p := hRaised
    _ = (W ^ (p - 1)) * D := by
      rw [Real.mul_rpow (Real.rpow_nonneg hW _) (Real.rpow_nonneg hD _),
        ← Real.rpow_mul hW, ← Real.rpow_mul hD]
      have hpNe : p ≠ 0 := ne_of_gt hpPos
      rw [inv_mul_cancel₀ hpNe, Real.rpow_one]
      congr 1
      field_simp
    _ = (∑ i ∈ t, w i) ^ (p - 1) *
        ∑ i ∈ t, w i * f i ^ p := by rfl

#print axioms wooley_weighted_rpow_sum_le

end

end GafniTao
