import GafniTao.ClassicalA2BLogCurvature

/-!
# Reciprocal-power bounds for the classical `A³B` process

After a third Weyl shift, the curvature of the logarithmic phase is
controlled by a finite difference of a reciprocal-cube gap.  This file
keeps that gap, both shift lengths, and the fifth power of the physical
block scale explicit.
-/

open Set

namespace GafniTao

noncomputable section

def reciprocalCubeGap (r x : ℝ) : ℝ :=
  1 / x ^ 3 - 1 / (x + r) ^ 3

theorem hasDerivAt_reciprocalCubeGap
    {r x : ℝ} (hx : x ≠ 0) (hxr : x + r ≠ 0) :
    HasDerivAt (reciprocalCubeGap r)
      (-3 / x ^ 4 + 3 / (x + r) ^ 4) x := by
  unfold reciprocalCubeGap
  have hleft : HasDerivAt (fun y : ℝ => 1 / y ^ 3) (-3 / x ^ 4) x := by
    convert (hasDerivAt_inv hx).pow 3 using 1
    · ext y
      simp [div_eq_mul_inv]
    · norm_num
      field_simp [hx]
  have hrightAt : HasDerivAt (fun y : ℝ => 1 / y ^ 3)
      (-3 / (x + r) ^ 4) (x + r) := by
    convert (hasDerivAt_inv hxr).pow 3 using 1
    · ext y
      simp [div_eq_mul_inv]
    · norm_num
      field_simp [hxr]
  have hright : HasDerivAt (fun y : ℝ => 1 / (y + r) ^ 3)
      (-3 / (x + r) ^ 4) x := by
    simpa using hrightAt.comp x ((hasDerivAt_id x).add_const r)
  convert hleft.sub hright using 1
  all_goals field_simp [hx, hxr]
  all_goals ring

theorem reciprocal_fourth_gap_formula
    {u v r : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (hvu : v - u = r) :
    1 / u ^ 4 - 1 / v ^ 4 =
      r * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) /
        (u ^ 4 * v ^ 4) := by
  rw [← hvu]
  field_simp [hu, hv]
  ring

theorem reciprocal_fourth_gap_bounds
    {A u v r : ℝ} (hA : 0 < A) (hr : 0 < r)
    (huLow : A ≤ u) (huv : u ≤ v) (hvHigh : v ≤ 2 * A)
    (hvu : v - u = r) :
    r / (64 * A ^ 5) ≤ 1 / u ^ 4 - 1 / v ^ 4 ∧
      1 / u ^ 4 - 1 / v ^ 4 ≤ 32 * r / A ^ 5 := by
  have hu : 0 < u := hA.trans_le huLow
  have hv : 0 < v := hu.trans_le huv
  have huHigh : u ≤ 2 * A := huv.trans hvHigh
  have hu2Low : A ^ 2 ≤ u ^ 2 := by nlinarith
  have hv2Low : A ^ 2 ≤ v ^ 2 := by nlinarith
  have hu2High : u ^ 2 ≤ 4 * A ^ 2 := by nlinarith
  have hv2High : v ^ 2 ≤ 4 * A ^ 2 := by nlinarith
  have hu3Low : A ^ 3 ≤ u ^ 3 := by nlinarith
  have hv3Low : A ^ 3 ≤ v ^ 3 := by nlinarith
  have hu3High : u ^ 3 ≤ 8 * A ^ 3 := by nlinarith
  have hv3High : v ^ 3 ≤ 8 * A ^ 3 := by nlinarith
  have hu2vLow : A ^ 3 ≤ u ^ 2 * v := by nlinarith
  have huv2Low : A ^ 3 ≤ u * v ^ 2 := by nlinarith
  have hu2vHigh : u ^ 2 * v ≤ 8 * A ^ 3 := by nlinarith
  have huv2High : u * v ^ 2 ≤ 8 * A ^ 3 := by nlinarith
  have hnumLow : 4 * A ^ 3 ≤
      u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3 := by linarith
  have hnumHigh : u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3 ≤
      32 * A ^ 3 := by linarith
  have hu4Low : A ^ 4 ≤ u ^ 4 := by nlinarith
  have hv4Low : A ^ 4 ≤ v ^ 4 := by nlinarith
  have hu4High : u ^ 4 ≤ 16 * A ^ 4 := by nlinarith
  have hv4High : v ^ 4 ≤ 16 * A ^ 4 := by nlinarith
  have hdenLow : A ^ 8 ≤ u ^ 4 * v ^ 4 := by
    calc
      A ^ 8 = A ^ 4 * A ^ 4 := by ring
      _ ≤ u ^ 4 * v ^ 4 :=
        mul_le_mul hu4Low hv4Low (by positivity) (by positivity)
  have hdenHigh : u ^ 4 * v ^ 4 ≤ 256 * A ^ 8 := by
    calc
      u ^ 4 * v ^ 4 ≤ (16 * A ^ 4) * (16 * A ^ 4) :=
        mul_le_mul hu4High hv4High (by positivity) (by positivity)
      _ = 256 * A ^ 8 := by ring
  rw [reciprocal_fourth_gap_formula hu.ne' hv.ne' hvu]
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 64 * A ^ 5)
      (by positivity : 0 < u ^ 4 * v ^ 4)]
    have hcore : u ^ 4 * v ^ 4 ≤
        64 * A ^ 5 * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) := by
      calc
        u ^ 4 * v ^ 4 ≤ 256 * A ^ 8 := hdenHigh
        _ = 64 * A ^ 5 * (4 * A ^ 3) := by ring
        _ ≤ 64 * A ^ 5 *
            (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) := by gcongr
    nlinarith [mul_nonneg hr.le
      (mul_nonneg (pow_nonneg hu.le 4) (pow_nonneg hv.le 4))]
  · rw [div_le_div_iff₀ (by positivity : 0 < u ^ 4 * v ^ 4)
      (by positivity : 0 < A ^ 5)]
    have hcore : A ^ 5 *
        (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) ≤
        32 * (u ^ 4 * v ^ 4) := by
      calc
        A ^ 5 * (u ^ 3 + u ^ 2 * v + u * v ^ 2 + v ^ 3) ≤
            A ^ 5 * (32 * A ^ 3) :=
          mul_le_mul_of_nonneg_left hnumHigh (pow_nonneg hA.le 5)
        _ = 32 * A ^ 8 := by ring
        _ ≤ 32 * (u ^ 4 * v ^ 4) := by linarith
    nlinarith [mul_nonneg hr.le
      (mul_nonneg (pow_nonneg hu.le 4) (pow_nonneg hv.le 4))]

theorem reciprocalCubeGap_neg_deriv_bounds
    {A x r : ℝ} (hA : 0 < A) (hr : 0 < r)
    (hxLow : A ≤ x) (hxrHigh : x + r ≤ 2 * A) :
    r / (32 * A ^ 5) ≤
        -(-3 / x ^ 4 + 3 / (x + r) ^ 4) ∧
      -(-3 / x ^ 4 + 3 / (x + r) ^ 4) ≤
        96 * r / A ^ 5 := by
  have hx : 0 < x := hA.trans_le hxLow
  have hgap := reciprocal_fourth_gap_bounds hA hr hxLow
    (by linarith : x ≤ x + r) hxrHigh (by ring)
  have heq : -(-3 / x ^ 4 + 3 / (x + r) ^ 4) =
      3 * (1 / x ^ 4 - 1 / (x + r) ^ 4) := by ring
  rw [heq]
  constructor
  · calc
      r / (32 * A ^ 5) = 2 * (r / (64 * A ^ 5)) := by
        field_simp [hA.ne']
        ring
      _ ≤ 3 * (r / (64 * A ^ 5)) := by
        have hfrac : 0 ≤ r / (64 * A ^ 5) := by positivity
        linarith
      _ ≤ 3 * (1 / x ^ 4 - 1 / (x + r) ^ 4) :=
        mul_le_mul_of_nonneg_left hgap.1 (by norm_num)
  · have := mul_le_mul_of_nonneg_left hgap.2 (by norm_num : (0 : ℝ) ≤ 3)
    convert this using 1
    · ring

/-- A positive finite difference of the reciprocal-cube gap has fifth-order
size in the block scale. -/
theorem reciprocalCubeGap_difference_bounds
    {A u r s : ℝ} (hA : 0 < A) (hr : 0 < r) (hs : 0 < s)
    (huLow : A ≤ u) (hursHigh : u + r + s ≤ 2 * A) :
    r * s / (32 * A ^ 5) ≤
        reciprocalCubeGap r u - reciprocalCubeGap r (u + s) ∧
      reciprocalCubeGap r u - reciprocalCubeGap r (u + s) ≤
        96 * r * s / A ^ 5 := by
  have hu : 0 < u := hA.trans_le huLow
  have hus : 0 < u + s := by linarith
  have hcont : ContinuousOn (reciprocalCubeGap r) (Icc u (u + s)) := by
    intro x hx
    exact (hasDerivAt_reciprocalCubeGap
      (ne_of_gt (hu.trans_le hx.1))
      (ne_of_gt (by linarith [hx.1]))).continuousAt.continuousWithinAt
  have hderiv : ∀ x ∈ Ioo u (u + s),
      HasDerivAt (reciprocalCubeGap r)
        (-3 / x ^ 4 + 3 / (x + r) ^ 4) x := by
    intro x hx
    exact hasDerivAt_reciprocalCubeGap
      (ne_of_gt (hu.trans hx.1)) (ne_of_gt (by linarith [hx.1]))
  obtain ⟨c, hc, hslope⟩ := exists_hasDerivAt_eq_slope
    (reciprocalCubeGap r)
    (fun x : ℝ => -3 / x ^ 4 + 3 / (x + r) ^ 4)
    (by linarith) hcont hderiv
  have hcLow : A ≤ c := huLow.trans hc.1.le
  have hcrHigh : c + r ≤ 2 * A := by linarith [hc.2, hursHigh]
  have hderivBounds := reciprocalCubeGap_neg_deriv_bounds hA hr hcLow hcrHigh
  have hlength : u + s - u = s := by ring
  rw [hlength] at hslope
  have heq : reciprocalCubeGap r u - reciprocalCubeGap r (u + s) =
      -(-3 / c ^ 4 + 3 / (c + r) ^ 4) * s := by
    rw [hslope]
    field_simp [hs.ne']
    ring
  rw [heq]
  constructor
  · have hmul := mul_le_mul_of_nonneg_right hderivBounds.1 hs.le
    convert hmul using 1
    · ring
  · have hmul := mul_le_mul_of_nonneg_right hderivBounds.2 hs.le
    convert hmul using 1
    · ring

#print axioms reciprocal_fourth_gap_bounds
#print axioms reciprocalCubeGap_difference_bounds

end

end GafniTao
