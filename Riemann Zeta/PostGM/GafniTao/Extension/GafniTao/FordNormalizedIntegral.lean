import GafniTao.FordCubicScaling

/-!
# Ford's normalized cubic integral

We identify the critical point and maximum after scaling, prove integrability
of the exact normalized integrand, and assemble the pre-numerical form of
Ford's Lemma 7.3.
-/

open Set MeasureTheory

namespace GafniTao

noncomputable section

theorem fordCubicScale_mul_y_eq_turningPoint
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    fordCubicScale D t * fordCubicY D sigma t =
      fordCubicTurningPoint D sigma t := by
  let L := fordCubicScale D t
  let y := fordCubicY D sigma t
  have hL : 0 < L := fordCubicScale_pos hD ht
  have hy0 : 0 ≤ y := by
    dsimp [y, fordCubicY]
    positivity
  have hturn0 := fordCubicTurningPoint_nonneg D sigma t
  have hB : 0 < fordCubicB D t := fordCubicB_pos hD ht
  have hy := three_mul_fordCubicY_sq hsigma hD ht
  have hscale := fordCubicB_mul_scale_cubed hD ht
  change L * y = fordCubicTurningPoint D sigma t
  have hcross :
      3 * fordCubicB D t * (L * y) ^ 2 = fordCubicA sigma := by
    calc
      3 * fordCubicB D t * (L * y) ^ 2 =
          (3 * y ^ 2) * (fordCubicB D t * L ^ 2) := by ring
      _ = (fordCubicA sigma * L) *
          (fordCubicB D t * L ^ 2) := by
            change (3 * fordCubicY D sigma t ^ 2) *
                (fordCubicB D t * fordCubicScale D t ^ 2) = _
            rw [hy]
      _ = fordCubicA sigma *
          (fordCubicB D t * L ^ 3) := by ring
      _ = fordCubicA sigma := by
        change fordCubicA sigma *
            (fordCubicB D t * fordCubicScale D t ^ 3) = _
        rw [hscale]
        ring
  have hprodSq :
      (L * y) ^ 2 = fordCubicA sigma / (3 * fordCubicB D t) := by
    apply (eq_div_iff (by positivity : 3 * fordCubicB D t ≠ 0)).2
    nlinarith
  have hturnSq := fordCubicTurningPoint_sq hsigma hD ht
  have hprod0 : 0 ≤ L * y := mul_nonneg hL.le hy0
  nlinarith

theorem fordCubicPeak_eq_two_mul_y_cubed
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    fordCubicExponent D sigma t
        (fordCubicTurningPoint D sigma t) =
      2 * fordCubicY D sigma t ^ 3 := by
  rw [← fordCubicScale_mul_y_eq_turningPoint hsigma hD ht,
    fordCubicExponent_scale hsigma hD ht]
  ring

theorem integrableOn_fordNormalizedCubicExp_Ioi
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    IntegrableOn (fordNormalizedCubicExp (fordCubicY D sigma t))
      (Set.Ioi 0) := by
  have hL := fordCubicScale_pos hD ht
  have hcomp : IntegrableOn
      (fun u => Real.exp (fordCubicExponent D sigma t
        (fordCubicScale D t * u))) (Set.Ioi 0) := by
    exact (integrableOn_Ioi_comp_mul_left_iff
      (fun x : ℝ => Real.exp (fordCubicExponent D sigma t x)) 0 hL).2
        (by
          simpa using
            (integrableOn_fordCubicExp_Ioi (sigma := sigma) hD ht))
  apply hcomp.congr
  filter_upwards with u
  exact fordCubicExp_scale hsigma hD ht u

theorem fordCubicExpSum_le_normalized
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) (r : ℕ) :
    (∑ j ∈ Finset.range r,
        Real.exp (fordDyadicExponent D sigma t j)) ≤
      Real.exp (2 * fordCubicY D sigma t ^ 3) +
        fordCubicScale D t *
          ∫ u in Set.Ioi (0 : ℝ),
            fordNormalizedCubicExp (fordCubicY D sigma t) u := by
  have hsum := fordCubicExpSum_le_peak_add_integral hsigma hD ht r
  have hfinite := intervalIntegral_fordCubicExp_le_Ioi
    (sigma := sigma) hD ht r
  have hscale := integral_fordCubicExp_Ioi_eq_scaled hsigma hD ht
  rw [fordCubicPeak_eq_two_mul_y_cubed hsigma hD ht] at hsum
  rw [hscale] at hfinite
  linarith

#print axioms fordCubicScale_mul_y_eq_turningPoint
#print axioms fordCubicPeak_eq_two_mul_y_cubed
#print axioms integrableOn_fordNormalizedCubicExp_Ioi
#print axioms fordCubicExpSum_le_normalized

end

end GafniTao
