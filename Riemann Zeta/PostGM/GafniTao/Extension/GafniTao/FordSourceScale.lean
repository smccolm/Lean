import GafniTao.FordNormalizedIntegral

/-!
# Ford's printed scale

The analytic development used the reciprocal cube root of the literal cubic
coefficient.  This file proves that it is exactly Ford's printed factor
`D^(1/3) * log(t)^(2/3) / log(2)`.
-/

namespace GafniTao

noncomputable section

def fordSourceScaleCore (D t : ℝ) : ℝ :=
  (D * Real.log t ^ 2) ^ ((3 : ℝ)⁻¹) / Real.log 2

def fordSourceScale (D t : ℝ) : ℝ :=
  D ^ ((3 : ℝ)⁻¹) * Real.log t ^ ((2 : ℝ) / 3) / Real.log 2

/-- The normalized parameter printed in Ford's proof of Lemma 7.3. -/
def fordSourceY (D sigma t : ℝ) : ℝ :=
  Real.sqrt ((1 - sigma) / 3) *
    D ^ ((1 : ℝ) / 6) * Real.log t ^ ((1 : ℝ) / 3)

theorem fordSourceScaleCore_pos
    {D t : ℝ} (hD : 0 < D) (ht : 1 < t) :
    0 < fordSourceScaleCore D t := by
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold fordSourceScaleCore
  exact div_pos (Real.rpow_pos_of_pos (mul_pos hD (sq_pos_of_pos hlogt)) _)
    hlogTwo

theorem fordCubicB_mul_sourceScaleCore_cubed
    {D t : ℝ} (hD : 0 < D) (ht : 1 < t) :
    fordCubicB D t * fordSourceScaleCore D t ^ 3 = 1 := by
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hbase : 0 ≤ D * Real.log t ^ 2 :=
    (mul_pos hD (sq_pos_of_pos hlogt)).le
  have hroot :
      ((D * Real.log t ^ 2) ^ ((3 : ℝ)⁻¹)) ^ 3 =
        D * Real.log t ^ 2 := by
    exact Real.rpow_inv_natCast_pow hbase (by norm_num)
  unfold fordCubicB fordSourceScaleCore
  rw [div_pow, hroot]
  field_simp [hD.ne', hlogt.ne', hlogTwo.ne']

theorem fordCubicScale_eq_sourceScaleCore
    {D t : ℝ} (hD : 0 < D) (ht : 1 < t) :
    fordCubicScale D t = fordSourceScaleCore D t := by
  have hB : 0 < fordCubicB D t := fordCubicB_pos hD ht
  have hleft := fordCubicB_mul_scale_cubed hD ht
  have hright := fordCubicB_mul_sourceScaleCore_cubed hD ht
  have hcubes : fordCubicScale D t ^ 3 = fordSourceScaleCore D t ^ 3 := by
    apply (mul_left_cancel₀ hB.ne')
    exact hleft.trans hright.symm
  exact (by norm_num : Odd 3).pow_injective hcubes

theorem fordSourceScaleCore_eq_sourceScale
    {D t : ℝ} (hD : 0 < D) (ht : 1 < t) :
    fordSourceScaleCore D t = fordSourceScale D t := by
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have hprod :
      (D * Real.log t ^ 2) ^ ((3 : ℝ)⁻¹) =
        D ^ ((3 : ℝ)⁻¹) * (Real.log t ^ 2) ^ ((3 : ℝ)⁻¹) := by
    exact Real.mul_rpow hD.le (sq_nonneg (Real.log t))
  have hlogpow :
      (Real.log t ^ 2) ^ ((3 : ℝ)⁻¹) =
        Real.log t ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hlogt.le]
    congr 1
  unfold fordSourceScaleCore fordSourceScale
  rw [hprod, hlogpow]

theorem fordCubicScale_eq_sourceScale
    {D t : ℝ} (hD : 0 < D) (ht : 1 < t) :
    fordCubicScale D t = fordSourceScale D t := by
  rw [fordCubicScale_eq_sourceScaleCore hD ht,
    fordSourceScaleCore_eq_sourceScale hD ht]

theorem fordCubicY_eq_sourceY
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    fordCubicY D sigma t = fordSourceY D sigma t := by
  have hlogt : 0 < Real.log t := Real.log_pos ht
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : 0 ≤ (1 - sigma) / 3 := by positivity
  have hDpow :
      (D ^ ((1 : ℝ) / 6)) ^ 2 = D ^ ((1 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hD.le]
    congr 1
    norm_num
  have hlogpow :
      (Real.log t ^ ((1 : ℝ) / 3)) ^ 2 =
        Real.log t ^ ((2 : ℝ) / 3) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlogt.le]
    congr 1
    norm_num
  have hsourceSq :
      fordSourceY D sigma t ^ 2 =
        (1 - sigma) / 3 * D ^ ((1 : ℝ) / 3) *
          Real.log t ^ ((2 : ℝ) / 3) := by
    unfold fordSourceY
    rw [mul_pow, mul_pow, Real.sq_sqrt ha, hDpow, hlogpow]
  have hySq :
      fordCubicY D sigma t ^ 2 =
        (1 - sigma) / 3 * D ^ ((1 : ℝ) / 3) *
          Real.log t ^ ((2 : ℝ) / 3) := by
    have hinside :
        0 ≤ fordCubicA sigma * fordCubicScale D t / 3 := by
      exact div_nonneg
        (mul_nonneg (fordCubicA_nonneg hsigma)
          (fordCubicScale_pos hD ht).le) (by norm_num)
    unfold fordCubicY
    rw [Real.sq_sqrt hinside, fordCubicScale_eq_sourceScale hD ht]
    unfold fordCubicA fordSourceScale
    field_simp [hlogTwo.ne']
  have hy0 : 0 ≤ fordCubicY D sigma t := by
    unfold fordCubicY
    positivity
  have hsource0 : 0 ≤ fordSourceY D sigma t := by
    unfold fordSourceY
    positivity
  nlinarith

#print axioms fordCubicB_mul_sourceScaleCore_cubed
#print axioms fordCubicScale_eq_sourceScale
#print axioms fordCubicY_eq_sourceY

end

end GafniTao
