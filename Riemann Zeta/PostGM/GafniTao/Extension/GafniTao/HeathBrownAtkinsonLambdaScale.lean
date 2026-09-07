import GafniTao.HeathBrownAtkinsonLargeValues
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Elementary size bounds for the Atkinson B-process parameters

Ivić's equation (7.19) uses that the curvature of the two-height phase has
size `|t-u| T⁻¹ᐟ² K⁻³ᐟ²`.  The lemmas here prove explicit one-sided versions
directly from the literal radical definitions.  No asymptotic notation is
introduced.
-/

namespace GafniTao

noncomputable section

theorem heathBrownAtkinsonSlopeUpper_le_seven_sqrt
    {u A : Real} (hu : 0 < u) (hA : 0 < A) :
    heathBrownAtkinsonSlopeUpper u A ≤ 7 * Real.sqrt (u / A) := by
  have hr : 0 ≤ u / A := (div_pos hu hA).le
  have hcoeff :
      (2 * Real.pi + Real.pi ^ (2 : Nat)) * 2 ≤ 49 := by
    nlinarith [Real.pi_pos, Real.pi_le_four, sq_nonneg (Real.pi - 4)]
  have hins :
      (2 * Real.pi + Real.pi ^ (2 : Nat)) * (2 * u) / A ≤
        49 * (u / A) := by
    have hm := mul_le_mul_of_nonneg_right hcoeff hr
    convert hm using 1
    field_simp [hA.ne']
  unfold heathBrownAtkinsonSlopeUpper
  calc
    Real.sqrt ((2 * Real.pi + Real.pi ^ (2 : Nat)) * (2 * u) / A) ≤
        Real.sqrt (49 * (u / A)) := Real.sqrt_le_sqrt hins
    _ = 7 * Real.sqrt (u / A) := by
      rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 49)]
      norm_num

theorem sqrt_le_heathBrownAtkinsonSlopeLower_two_mul
    {u A : Real} (hu : 0 < u) (hA : 0 < A) :
    Real.sqrt (u / A) ≤ heathBrownAtkinsonSlopeLower u (2 * A) := by
  unfold heathBrownAtkinsonSlopeLower
  apply Real.sqrt_le_sqrt
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hr : 0 ≤ u / A := (div_pos hu hA).le
  have hm := mul_le_mul_of_nonneg_right hpi hr
  convert hm using 1 <;> field_simp [hA.ne']

/-- The lower box curvature has the required `u⁻¹ᐟ² A⁻³ᐟ²` scale, with an
explicit harmless constant. -/
theorem one_div_twenty_scale_le_heathBrownAtkinsonBoxCurvatureLower
    {u A : Real} (hu : 0 < u) (hA : 0 < A) :
    1 / (20 * A ^ (2 : Nat) * Real.sqrt (u / A)) ≤
      heathBrownAtkinsonBoxCurvatureLower u A (2 * A) := by
  have hr : 0 < u / A := div_pos hu hA
  have hs : 0 < Real.sqrt (u / A) := Real.sqrt_pos.2 hr
  have hQ : 0 < A ^ (2 : Nat) * Real.sqrt (u / A) :=
    mul_pos (sq_pos_of_pos hA) hs
  have hslope := heathBrownAtkinsonSlopeUpper_le_seven_sqrt hu hA
  have hden :
      2 * (2 * A) ^ (2 : Nat) * heathBrownAtkinsonSlopeUpper u A ≤
        56 * (A ^ (2 : Nat) * Real.sqrt (u / A)) := by
    have hnonneg : 0 ≤ 2 * (2 * A) ^ (2 : Nat) := by positivity
    have hm := mul_le_mul_of_nonneg_left hslope hnonneg
    nlinarith
  have hdenPos :
      0 < 2 * (2 * A) ^ (2 : Nat) *
        heathBrownAtkinsonSlopeUpper u A := by
    exact mul_pos (mul_pos (by norm_num) (sq_pos_of_pos (by linarith)))
      (heathBrownAtkinsonSlopeUpper_pos hu hA)
  unfold heathBrownAtkinsonBoxCurvatureLower
  have hfirst :
      Real.pi /
          (56 * (A ^ (2 : Nat) * Real.sqrt (u / A))) ≤
        Real.pi /
          (2 * (2 * A) ^ (2 : Nat) *
            heathBrownAtkinsonSlopeUpper u A) :=
    div_le_div_of_nonneg_left Real.pi_nonneg hdenPos hden
  calc
    1 / (20 * A ^ (2 : Nat) * Real.sqrt (u / A)) ≤
        Real.pi / (56 * (A ^ (2 : Nat) * Real.sqrt (u / A))) := by
      rw [div_le_div_iff₀ (by positivity :
          0 < 20 * A ^ (2 : Nat) * Real.sqrt (u / A))
        (by positivity :
          0 < 56 * (A ^ (2 : Nat) * Real.sqrt (u / A)))]
      nlinarith [Real.pi_gt_three, hQ]
    _ ≤ _ := hfirst

/-- Matching explicit upper curvature scale. -/
theorem heathBrownAtkinsonBoxCurvatureUpper_le_four_div_scale
    {u A : Real} (hu : 0 < u) (hA : 0 < A) :
    heathBrownAtkinsonBoxCurvatureUpper u A (2 * A) ≤
      4 / (A ^ (2 : Nat) * Real.sqrt (u / A)) := by
  have hr : 0 < u / A := div_pos hu hA
  have hs : 0 < Real.sqrt (u / A) := Real.sqrt_pos.2 hr
  have hslow := sqrt_le_heathBrownAtkinsonSlopeLower_two_mul hu hA
  have hden :
      A ^ (2 : Nat) * Real.sqrt (u / A) ≤
        A ^ (2 : Nat) * heathBrownAtkinsonSlopeLower u (2 * A) :=
    mul_le_mul_of_nonneg_left hslow (sq_nonneg A)
  have hdenPos :
      0 < A ^ (2 : Nat) * heathBrownAtkinsonSlopeLower u (2 * A) := by
    exact mul_pos (sq_pos_of_pos hA)
      (heathBrownAtkinsonSlopeLower_pos hu (by linarith))
  unfold heathBrownAtkinsonBoxCurvatureUpper
  calc
    Real.pi /
        (A ^ (2 : Nat) * heathBrownAtkinsonSlopeLower u (2 * A)) ≤
        Real.pi / (A ^ (2 : Nat) * Real.sqrt (u / A)) :=
      div_le_div_of_nonneg_left Real.pi_nonneg
        (mul_pos (sq_pos_of_pos hA) hs) hden
    _ ≤ 4 / (A ^ (2 : Nat) * Real.sqrt (u / A)) := by
      exact div_le_div_of_nonneg_right Real.pi_le_four
        (mul_nonneg (sq_nonneg A) hs.le)

/-- Explicit lower scale for the lambda used by the terminal Gram block. -/
theorem heathBrownAtkinsonBProcessLambda_terminal_lower
    {t u : Real} {K : Nat} (hu : 0 < u) (htu : u < t)
    (hKpos : 0 < K) :
    (t - u) /
        (20 * ((K + 1 : Nat) : Real) ^ (2 : Nat) *
          Real.sqrt (u / ((K + 1 : Nat) : Real))) ≤
      heathBrownAtkinsonBProcessLambda t u (K + 1) (K - 1) := by
  have hK : 0 < ((K + 1 : Nat) : Real) := by positivity
  have hNat : (K + 1) + (K - 1) + 2 = 2 * (K + 1) := by omega
  have hB :
      ((K + 1 : Nat) : Real) + ((K - 1 : Nat) : Real) + 2 =
        2 * ((K + 1 : Nat) : Real) := by
    exact_mod_cast hNat
  unfold heathBrownAtkinsonBProcessLambda
  rw [hB]
  have hcurv :=
    one_div_twenty_scale_le_heathBrownAtkinsonBoxCurvatureLower hu hK
  have hgap : 0 ≤ t - u := sub_nonneg.mpr htu.le
  have hm := mul_le_mul_of_nonneg_right hcurv hgap
  convert hm using 1
  field_simp

/-- The upper curvature parameter is positive on every positively oriented
height pair. -/
theorem heathBrownAtkinsonBProcessLambdaUpper_pos
    {t u : Real} {K N : Nat} (hu : 0 < u) (htu : u < t)
    (hK : 0 < K) :
    0 < heathBrownAtkinsonBProcessLambdaUpper t u K N := by
  unfold heathBrownAtkinsonBProcessLambdaUpper
    heathBrownAtkinsonBoxCurvatureUpper
  exact mul_pos
    (div_pos Real.pi_pos
      (mul_pos (sq_pos_of_pos (by exact_mod_cast hK))
        (heathBrownAtkinsonSlopeLower_pos hu (by
          exact_mod_cast (show 0 < K + N + 2 by omega)))))
    (sub_pos.mpr htu)

/-- Explicit upper scale for the matching terminal lambda. -/
theorem heathBrownAtkinsonBProcessLambdaUpper_terminal_upper
    {t u : Real} {K : Nat} (hu : 0 < u) (htu : u < t)
    (hKpos : 0 < K) :
    heathBrownAtkinsonBProcessLambdaUpper t u (K + 1) (K - 1) ≤
      4 * (t - u) /
        (((K + 1 : Nat) : Real) ^ (2 : Nat) *
          Real.sqrt (u / ((K + 1 : Nat) : Real))) := by
  have hK : 0 < ((K + 1 : Nat) : Real) := by positivity
  have hNat : (K + 1) + (K - 1) + 2 = 2 * (K + 1) := by omega
  have hB :
      ((K + 1 : Nat) : Real) + ((K - 1 : Nat) : Real) + 2 =
        2 * ((K + 1 : Nat) : Real) := by
    exact_mod_cast hNat
  unfold heathBrownAtkinsonBProcessLambdaUpper
  rw [hB]
  have hcurv :=
    heathBrownAtkinsonBoxCurvatureUpper_le_four_div_scale hu hK
  have hgap : 0 ≤ t - u := sub_nonneg.mpr htu.le
  have hm := mul_le_mul_of_nonneg_right hcurv hgap
  convert hm using 1
  field_simp


end

end GafniTao
