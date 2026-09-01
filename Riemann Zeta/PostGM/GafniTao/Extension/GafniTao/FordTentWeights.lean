import GafniTao.FordSpacingCount
import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc

/-!
# Ford's tent and sinc-square weights

These are the literal weights between equations (5.3) and (5.4).  The tent
uses the norm on `UnitAddCircle`, which is exactly distance to the nearest
integer.  No unspecified cutoff is introduced.
-/

open Real

namespace GafniTao

noncomputable section

/-- Ford's periodic tent `ℓ(x;w)`. -/
def fordTent (x w : ℝ) : ℝ :=
  max 0 (1 - ‖(x : UnitAddCircle)‖ / w)

theorem fordTent_nonneg (x w : ℝ) : 0 ≤ fordTent x w := by
  exact le_max_left _ _

theorem fordTent_le_one {x w : ℝ} (hw : 0 < w) : fordTent x w ≤ 1 := by
  unfold fordTent
  apply max_le
  · norm_num
  · have hnorm : 0 ≤ ‖(x : UnitAddCircle)‖ / w := by positivity
    linarith

theorem fordTent_eq_zero_of_le_norm {x w : ℝ} (hw : 0 < w)
    (h : w ≤ ‖(x : UnitAddCircle)‖) : fordTent x w = 0 := by
  unfold fordTent
  rw [max_eq_left]
  have h' : 1 * w ≤ ‖(x : UnitAddCircle)‖ := by simpa using h
  exact sub_nonpos.mpr ((le_div_iff₀ hw).2 h')

theorem fordTent_eq_one_sub_of_norm_lt {x w : ℝ} (hw : 0 < w)
    (h : ‖(x : UnitAddCircle)‖ < w) :
    fordTent x w = 1 - ‖(x : UnitAddCircle)‖ / w := by
  unfold fordTent
  rw [max_eq_right]
  exact sub_nonneg.mpr ((div_le_one hw).2 h.le)

/-- Ford's non-periodic sinc-square weight `f_j`. -/
def fordSincSquareWeight (r M j : ℕ) (x : ℝ) : ℝ :=
  (Real.pi / 2 *
      Real.sinc (Real.pi * x / (2 * ((r * M ^ j : ℕ) : ℝ)))) ^ 2

@[simp]
theorem fordSincSquareWeight_zero (r M j : ℕ) :
    fordSincSquareWeight r M j 0 = (Real.pi / 2) ^ 2 := by
  simp [fordSincSquareWeight]

theorem fordSincSquareWeight_eq_source
    {r M j : ℕ} (hr : 0 < r) (hM : 0 < M) {x : ℝ} (hx : x ≠ 0) :
    fordSincSquareWeight r M j x =
      (((r * M ^ j : ℕ) : ℝ) *
        Real.sin (Real.pi * x / (2 * ((r * M ^ j : ℕ) : ℝ))) / x) ^ 2 := by
  let A : ℝ := ((r * M ^ j : ℕ) : ℝ)
  have hA : A ≠ 0 := by
    dsimp [A]
    positivity
  have harg : Real.pi * x / (2 * A) ≠ 0 := by
    positivity
  unfold fordSincSquareWeight
  rw [Real.sinc_of_ne_zero harg]
  change (Real.pi / 2 *
      (Real.sin (Real.pi * x / (2 * A)) /
        (Real.pi * x / (2 * A)))) ^ 2 =
    (A * Real.sin (Real.pi * x / (2 * A)) / x) ^ 2
  congr 1
  field_simp [Real.pi_ne_zero, hA, hx]

theorem fordSincSquareWeight_nonneg (r M j : ℕ) (x : ℝ) :
    0 ≤ fordSincSquareWeight r M j x := by
  exact sq_nonneg _

/-- The source observation `f_j(x) ≥ 1` on `1 ≤ x ≤ rM^j`. -/
theorem one_le_fordSincSquareWeight
    {r M j : ℕ} (hr : 0 < r) (hM : 0 < M) {x : ℝ}
    (hxOne : 1 ≤ x) (hxTop : x ≤ ((r * M ^ j : ℕ) : ℝ)) :
    1 ≤ fordSincSquareWeight r M j x := by
  let A : ℝ := ((r * M ^ j : ℕ) : ℝ)
  have hAp : 0 < A := by
    dsimp [A]
    positivity
  have hxp : 0 < x := lt_of_lt_of_le (by norm_num) hxOne
  let y : ℝ := Real.pi * x / (2 * A)
  have hy0 : 0 ≤ y := by
    dsimp [y]
    positivity
  have hyTop : y ≤ Real.pi / 2 := by
    dsimp [y]
    apply (div_le_iff₀ (by positivity : 0 < 2 * A)).2
    nlinarith [Real.pi_pos, hxTop]
  have hsin := Real.mul_le_sin hy0 hyTop
  have hlinear : x / A ≤ Real.sin y := by
    calc
      x / A = 2 / Real.pi * y := by
        dsimp [y]
        field_simp [Real.pi_ne_zero, hAp.ne']
      _ ≤ Real.sin y := hsin
  have hratio : 1 ≤ A * Real.sin y / x := by
    apply (le_div_iff₀ hxp).2
    apply (div_le_iff₀ hAp).1 at hlinear
    nlinarith
  rw [fordSincSquareWeight_eq_source hr hM hxp.ne']
  change 1 ≤ (A * Real.sin y / x) ^ 2
  nlinarith [sq_nonneg (A * Real.sin y / x - 1)]

#print axioms fordTent_eq_zero_of_le_norm
#print axioms fordSincSquareWeight_eq_source
#print axioms one_le_fordSincSquareWeight

end

end GafniTao
