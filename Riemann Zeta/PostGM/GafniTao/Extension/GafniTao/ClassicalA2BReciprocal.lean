import GafniTao.ClassicalExponentPairAveraging

/-!
# Reciprocal-power bounds for the classical `A²B` process

Two finite differences of the logarithmic phase have positive curvature.
The elementary bounds here keep both shift distances and the fourth power
of the physical block scale explicit.
-/

namespace GafniTao

noncomputable section

def reciprocalSquareGap (r x : ℝ) : ℝ :=
  1 / x ^ 2 - 1 / (x + r) ^ 2

theorem hasDerivAt_reciprocalSquareGap
    {r x : ℝ} (hx : x ≠ 0) (hxr : x + r ≠ 0) :
    HasDerivAt (reciprocalSquareGap r)
      (-2 / x ^ 3 + 2 / (x + r) ^ 3) x := by
  unfold reciprocalSquareGap
  have hleft : HasDerivAt (fun y : ℝ => 1 / y ^ 2) (-2 / x ^ 3) x := by
    convert (hasDerivAt_inv hx).pow 2 using 1
    · ext y
      simp [div_eq_mul_inv]
    · norm_num
      field_simp [hx]
  have hrightAt : HasDerivAt (fun y : ℝ => 1 / y ^ 2)
      (-2 / (x + r) ^ 3) (x + r) := by
    convert (hasDerivAt_inv hxr).pow 2 using 1
    · ext y
      simp [div_eq_mul_inv]
    · norm_num
      field_simp [hxr]
  have hright : HasDerivAt (fun y : ℝ => 1 / (y + r) ^ 2)
      (-2 / (x + r) ^ 3) x := by
    simpa using hrightAt.comp x ((hasDerivAt_id x).add_const r)
  convert hleft.sub hright using 1
  all_goals field_simp [hx, hxr]
  all_goals ring

theorem reciprocal_cube_gap_formula
    {u v r : ℝ} (hu : u ≠ 0) (hv : v ≠ 0) (hvu : v - u = r) :
    1 / u ^ 3 - 1 / v ^ 3 =
      r * (u ^ 2 + u * v + v ^ 2) / (u ^ 3 * v ^ 3) := by
  rw [← hvu]
  field_simp [hu, hv]
  ring

theorem reciprocal_cube_gap_bounds
    {A u v r : ℝ} (hA : 0 < A) (hr : 0 < r)
    (huLow : A ≤ u) (huv : u ≤ v) (hvHigh : v ≤ 2 * A)
    (hvu : v - u = r) :
    r / (32 * A ^ 4) ≤ 1 / u ^ 3 - 1 / v ^ 3 ∧
      1 / u ^ 3 - 1 / v ^ 3 ≤ 16 * r / A ^ 4 := by
  have hu : 0 < u := hA.trans_le huLow
  have hv : 0 < v := hu.trans_le huv
  have huHigh : u ≤ 2 * A := huv.trans hvHigh
  have huSqLow : A ^ 2 ≤ u ^ 2 := by nlinarith
  have hvSqLow : A ^ 2 ≤ v ^ 2 := by nlinarith
  have huSqHigh : u ^ 2 ≤ 4 * A ^ 2 := by nlinarith
  have hvSqHigh : v ^ 2 ≤ 4 * A ^ 2 := by nlinarith
  have huvLow : A ^ 2 ≤ u * v := by nlinarith
  have huvHigh : u * v ≤ 4 * A ^ 2 := by nlinarith
  have hnumLow : 3 * A ^ 2 ≤ u ^ 2 + u * v + v ^ 2 := by linarith
  have hnumHigh : u ^ 2 + u * v + v ^ 2 ≤ 12 * A ^ 2 := by linarith
  have huCubeLow : A ^ 3 ≤ u ^ 3 := by nlinarith
  have hvCubeLow : A ^ 3 ≤ v ^ 3 := by nlinarith
  have huCubeHigh : u ^ 3 ≤ 8 * A ^ 3 := by nlinarith
  have hvCubeHigh : v ^ 3 ≤ 8 * A ^ 3 := by nlinarith
  have hdenLow : A ^ 6 ≤ u ^ 3 * v ^ 3 := by
    calc
      A ^ 6 = A ^ 3 * A ^ 3 := by ring
      _ ≤ u ^ 3 * v ^ 3 :=
        mul_le_mul huCubeLow hvCubeLow (by positivity) (by positivity)
  have hdenHigh : u ^ 3 * v ^ 3 ≤ 64 * A ^ 6 := by
    calc
      u ^ 3 * v ^ 3 ≤ (8 * A ^ 3) * (8 * A ^ 3) :=
        mul_le_mul huCubeHigh hvCubeHigh (by positivity) (by positivity)
      _ = 64 * A ^ 6 := by ring
  rw [reciprocal_cube_gap_formula hu.ne' hv.ne' hvu]
  constructor
  · rw [div_le_div_iff₀ (by positivity : 0 < 32 * A ^ 4)
      (by positivity : 0 < u ^ 3 * v ^ 3)]
    have hcore : u ^ 3 * v ^ 3 ≤
        32 * A ^ 4 * (u ^ 2 + u * v + v ^ 2) := by
      calc
        u ^ 3 * v ^ 3 ≤ 64 * A ^ 6 := hdenHigh
        _ ≤ 32 * A ^ 4 * (u ^ 2 + u * v + v ^ 2) := by
          nlinarith [mul_nonneg (sq_nonneg A) (sq_nonneg (A ^ 2))]
    nlinarith [mul_nonneg hr.le
      (mul_nonneg (pow_nonneg hu.le 3) (pow_nonneg hv.le 3))]
  · rw [div_le_div_iff₀ (by positivity : 0 < u ^ 3 * v ^ 3)
      (by positivity : 0 < A ^ 4)]
    have hcore : A ^ 4 * (u ^ 2 + u * v + v ^ 2) ≤
        16 * (u ^ 3 * v ^ 3) := by
      calc
        A ^ 4 * (u ^ 2 + u * v + v ^ 2) ≤
            A ^ 4 * (12 * A ^ 2) :=
          mul_le_mul_of_nonneg_left hnumHigh (pow_nonneg hA.le 4)
        _ ≤ 16 * (A ^ 6) := by
          nlinarith [pow_nonneg hA.le 6]
        _ ≤ 16 * (u ^ 3 * v ^ 3) := by linarith
    nlinarith [mul_nonneg hr.le
      (mul_nonneg (pow_nonneg hu.le 3) (pow_nonneg hv.le 3))]

/-- The negative derivative of a reciprocal-square gap has fourth-order
size in the block scale. -/
theorem reciprocalSquareGap_neg_deriv_bounds
    {A x r : ℝ} (hA : 0 < A) (hr : 0 < r)
    (hxLow : A ≤ x) (hxrHigh : x + r ≤ 2 * A) :
    r / (16 * A ^ 4) ≤
        -(-2 / x ^ 3 + 2 / (x + r) ^ 3) ∧
      -(-2 / x ^ 3 + 2 / (x + r) ^ 3) ≤
        32 * r / A ^ 4 := by
  have hx : 0 < x := hA.trans_le hxLow
  have hgap := reciprocal_cube_gap_bounds hA hr hxLow
    (by linarith : x ≤ x + r) hxrHigh (by ring)
  have heq : -(-2 / x ^ 3 + 2 / (x + r) ^ 3) =
      2 * (1 / x ^ 3 - 1 / (x + r) ^ 3) := by ring
  rw [heq]
  constructor
  · have := mul_le_mul_of_nonneg_left hgap.1 (by norm_num : (0 : ℝ) ≤ 2)
    convert this using 1
    all_goals ring
  · have := mul_le_mul_of_nonneg_left hgap.2 (by norm_num : (0 : ℝ) ≤ 2)
    convert this using 1
    all_goals ring

#print axioms hasDerivAt_reciprocalSquareGap
#print axioms reciprocal_cube_gap_bounds
#print axioms reciprocalSquareGap_neg_deriv_bounds

end

end GafniTao
