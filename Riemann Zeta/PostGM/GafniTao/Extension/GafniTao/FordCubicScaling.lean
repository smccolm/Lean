import GafniTao.FordCubicIntegral

/-!
# Scaling Ford's cubic integral

This is the exact change of variables in Ford's Lemma 7.3.  The scale is
defined from the literal cubic coefficient, and the normalized parameter is
chosen so that the transformed exponent is exactly `3*y^2*u-u^3`.
-/

open Set MeasureTheory

namespace GafniTao

noncomputable section

def fordCubicScale (D t : ℝ) : ℝ :=
  (fordCubicB D t ^ ((3 : ℝ)⁻¹))⁻¹

def fordCubicY (D sigma t : ℝ) : ℝ :=
  Real.sqrt (fordCubicA sigma * fordCubicScale D t / 3)

def fordNormalizedCubicExp (y u : ℝ) : ℝ :=
  Real.exp (3 * y ^ 2 * u - u ^ 3)

theorem fordCubicScale_pos
    {D t : ℝ} (hD : 0 < D) (ht : 1 < t) :
    0 < fordCubicScale D t := by
  unfold fordCubicScale
  exact inv_pos.mpr (Real.rpow_pos_of_pos (fordCubicB_pos hD ht) _)

theorem fordCubicB_mul_scale_cubed
    {D t : ℝ} (hD : 0 < D) (ht : 1 < t) :
    fordCubicB D t * fordCubicScale D t ^ 3 = 1 := by
  have hB : 0 < fordCubicB D t := fordCubicB_pos hD ht
  let q := fordCubicB D t ^ ((3 : ℝ)⁻¹)
  have hq : 0 < q := Real.rpow_pos_of_pos hB _
  have hcube : q ^ 3 = fordCubicB D t := by
    dsimp [q]
    exact Real.rpow_inv_natCast_pow hB.le (by norm_num)
  unfold fordCubicScale
  change fordCubicB D t * q⁻¹ ^ 3 = 1
  rw [inv_pow, hcube]
  exact mul_inv_cancel₀ hB.ne'

theorem three_mul_fordCubicY_sq
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    3 * fordCubicY D sigma t ^ 2 =
      fordCubicA sigma * fordCubicScale D t := by
  have hnonneg :
      0 ≤ fordCubicA sigma * fordCubicScale D t / 3 := by
    exact div_nonneg
      (mul_nonneg (fordCubicA_nonneg hsigma)
        (fordCubicScale_pos hD ht).le) (by norm_num)
  unfold fordCubicY
  rw [Real.sq_sqrt hnonneg]
  ring

theorem fordCubicExponent_scale
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) (u : ℝ) :
    fordCubicExponent D sigma t (fordCubicScale D t * u) =
      3 * fordCubicY D sigma t ^ 2 * u - u ^ 3 := by
  have hscale := fordCubicB_mul_scale_cubed hD ht
  have hy := three_mul_fordCubicY_sq hsigma hD ht
  unfold fordCubicExponent
  calc
    fordCubicA sigma * (fordCubicScale D t * u) -
        fordCubicB D t * (fordCubicScale D t * u) ^ 3 =
      (fordCubicA sigma * fordCubicScale D t) * u -
        (fordCubicB D t * fordCubicScale D t ^ 3) * u ^ 3 := by ring
    _ = 3 * fordCubicY D sigma t ^ 2 * u - u ^ 3 := by
      rw [← hy, hscale]
      ring

theorem fordCubicExp_scale
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) (u : ℝ) :
    Real.exp (fordCubicExponent D sigma t (fordCubicScale D t * u)) =
      fordNormalizedCubicExp (fordCubicY D sigma t) u := by
  unfold fordNormalizedCubicExp
  rw [fordCubicExponent_scale hsigma hD ht]

theorem integral_fordCubicExp_Ioi_eq_scaled
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    (∫ x in Set.Ioi (0 : ℝ),
        Real.exp (fordCubicExponent D sigma t x)) =
      fordCubicScale D t *
        ∫ u in Set.Ioi (0 : ℝ),
          fordNormalizedCubicExp (fordCubicY D sigma t) u := by
  let L := fordCubicScale D t
  have hL : 0 < L := fordCubicScale_pos hD ht
  have hchange := integral_comp_mul_left_Ioi
    (fun x : ℝ => Real.exp (fordCubicExponent D sigma t x)) 0 hL
  have hnormalized :
      (∫ u in Set.Ioi (0 : ℝ),
          Real.exp (fordCubicExponent D sigma t (L * u))) =
        ∫ u in Set.Ioi (0 : ℝ),
          fordNormalizedCubicExp (fordCubicY D sigma t) u := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    exact fordCubicExp_scale hsigma hD ht u
  dsimp only at hchange
  rw [mul_zero, hnormalized] at hchange
  change (∫ x in Set.Ioi (0 : ℝ),
      Real.exp (fordCubicExponent D sigma t x)) =
    L * ∫ u in Set.Ioi (0 : ℝ),
      fordNormalizedCubicExp (fordCubicY D sigma t) u
  rw [hchange]
  simp [smul_eq_mul, hL.ne']

#print axioms fordCubicB_mul_scale_cubed
#print axioms fordCubicExponent_scale
#print axioms integral_fordCubicExp_Ioi_eq_scaled

end

end GafniTao
