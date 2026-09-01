import GafniTao.FordIntegralBound

/-!
# Ford's source peak exponent

The normalized cubic maximum is rewritten here as Ford's printed
Vinogradov--Korobov exponent.  The proof compares exact squares and keeps all
fractional powers in Lean's real-power convention.
-/

namespace GafniTao

noncomputable section

def fordSourceB (D : ℝ) : ℝ :=
  (2 / 9 : ℝ) * Real.sqrt (3 * D)

theorem two_mul_fordCubicY_cubed_sq
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    (2 * fordCubicY D sigma t ^ 3) ^ 2 =
      (4 / 27 : ℝ) * D * (1 - sigma) ^ 3 * Real.log t ^ 2 := by
  have hy := three_mul_fordCubicY_sq hsigma hD ht
  have hscale := fordCubicB_mul_scale_cubed hD ht
  have hlogTwo : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlogt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  unfold fordCubicA at hy
  unfold fordCubicB at hscale
  field_simp [hD.ne', hlogTwo, hlogt] at hscale ⊢
  have hycube := congrArg (fun x : ℝ => x ^ 3) hy
  have hycube' :
      27 * fordCubicY D sigma t ^ 6 =
        (1 - sigma) ^ 3 * Real.log 2 ^ 3 *
          fordCubicScale D t ^ 3 := by
    calc
      27 * fordCubicY D sigma t ^ 6 =
          (3 * fordCubicY D sigma t ^ 2) ^ 3 := by ring
      _ = ((1 - sigma) * Real.log 2 * fordCubicScale D t) ^ 3 := hycube
      _ = _ := by ring
  calc
    2 ^ 2 * fordCubicY D sigma t ^ 6 * 27 =
        4 * (27 * fordCubicY D sigma t ^ 6) := by ring
    _ = 4 * ((1 - sigma) ^ 3 * Real.log 2 ^ 3 *
          fordCubicScale D t ^ 3) := by rw [hycube']
    _ = 4 * (1 - sigma) ^ 3 *
          (Real.log 2 ^ 3 * fordCubicScale D t ^ 3) := by ring
    _ = D * Real.log t ^ 2 * 4 * (1 - sigma) ^ 3 := by rw [hscale]; ring

theorem fordSourcePeak_sq
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) :
    (fordSourceB D * (1 - sigma) ^ (3 / 2 : ℝ) * Real.log t) ^ 2 =
      (4 / 27 : ℝ) * D * (1 - sigma) ^ 3 * Real.log t ^ 2 := by
  have hp : 0 ≤ 1 - sigma := sub_nonneg.mpr hsigma
  have hsqrt : Real.sqrt (3 * D) ^ 2 = 3 * D := by
    rw [Real.sq_sqrt]
    positivity
  have hrpow : ((1 - sigma) ^ (3 / 2 : ℝ)) ^ 2 = (1 - sigma) ^ 3 := by
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul hp]
    norm_num
  unfold fordSourceB
  calc
    (2 / 9 * Real.sqrt (3 * D) *
        (1 - sigma) ^ (3 / 2 : ℝ) * Real.log t) ^ 2 =
        (4 / 81 : ℝ) * Real.sqrt (3 * D) ^ 2 *
          ((1 - sigma) ^ (3 / 2 : ℝ)) ^ 2 * Real.log t ^ 2 := by ring
    _ = _ := by rw [hsqrt, hrpow]; ring

theorem two_mul_fordCubicY_cubed_eq_sourcePeak
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    2 * fordCubicY D sigma t ^ 3 =
      fordSourceB D * (1 - sigma) ^ (3 / 2 : ℝ) * Real.log t := by
  have hl := two_mul_fordCubicY_cubed_sq hsigma hD ht
  have hr := fordSourcePeak_sq (t := t) hsigma hD
  have hleft : 0 ≤ 2 * fordCubicY D sigma t ^ 3 := by
    have : 0 ≤ fordCubicY D sigma t := by unfold fordCubicY; positivity
    positivity
  have hright : 0 ≤
      fordSourceB D * (1 - sigma) ^ (3 / 2 : ℝ) * Real.log t := by
    unfold fordSourceB
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
        (Real.rpow_nonneg (sub_nonneg.mpr hsigma) _))
      (Real.log_pos ht).le
  nlinarith

theorem exp_two_mul_fordCubicY_cubed_eq_sourcePower
    {D sigma t : ℝ} (hsigma : sigma ≤ 1)
    (hD : 0 < D) (ht : 1 < t) :
    Real.exp (2 * fordCubicY D sigma t ^ 3) =
      t ^ (fordSourceB D * (1 - sigma) ^ (3 / 2 : ℝ)) := by
  rw [two_mul_fordCubicY_cubed_eq_sourcePeak hsigma hD ht]
  rw [Real.rpow_def_of_pos (zero_lt_one.trans ht)]
  ring_nf

#print axioms two_mul_fordCubicY_cubed_eq_sourcePeak
#print axioms exp_two_mul_fordCubicY_cubed_eq_sourcePower

end

end GafniTao
