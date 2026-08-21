import RiemannZeta.GuthMaynard.HughesYoungDyadicAssembly

open Complex Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff FourierTransform Interval Topology

noncomputable section

namespace RiemannZeta.GuthMaynard

/-!
# The optimized DFI scale on a Hughes--Young box

For a box of physical reduced scales `X,Y` and derivative parameter `P`,
Hughes--Young use

`Q² = U = P⁻¹ (X+Y)⁻¹ X Y`.

The lemmas below construct these parameters and prove every scale condition
required by the native DFI theorem.  The condition `64 ≤ U` is exactly the
large-box branch `8 ≤ Q`; its complement is the finite small-box branch.
-/

noncomputable def hughesYoungDFIOptimalU (P X Y : ℝ) : ℝ :=
  P⁻¹ * (X + Y)⁻¹ * (X * Y)

noncomputable def hughesYoungDFIOptimalQ (P X Y : ℝ) : ℝ :=
  Real.sqrt (hughesYoungDFIOptimalU P X Y)

theorem hughesYoungDFIOptimalU_nonneg
    {P X Y : ℝ} (hP : 0 < P) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    0 ≤ hughesYoungDFIOptimalU P X Y := by
  unfold hughesYoungDFIOptimalU
  positivity

theorem hughesYoungDFIOptimalQ_sq
    {P X Y : ℝ} (hP : 0 < P) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    hughesYoungDFIOptimalQ P X Y ^ 2 =
      P⁻¹ * (X + Y)⁻¹ * (X * Y) := by
  unfold hughesYoungDFIOptimalQ hughesYoungDFIOptimalU
  rw [Real.sq_sqrt (by positivity)]

theorem hughesYoungDFIOptimalU_eq_Q_sq
    {P X Y : ℝ} (hP : 0 < P) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    hughesYoungDFIOptimalU P X Y =
      hughesYoungDFIOptimalQ P X Y ^ 2 := by
  exact (hughesYoungDFIOptimalQ_sq hP hX hY).symm

theorem hughesYoungDFIOptimalU_le_inv_mul_min
    {P X Y : ℝ} (hP : 0 < P) (hX : 0 < X) (hY : 0 < Y) :
    hughesYoungDFIOptimalU P X Y ≤ P⁻¹ * min X Y := by
  unfold hughesYoungDFIOptimalU
  have hsum : 0 < X + Y := add_pos hX hY
  have hfracX : (X + Y)⁻¹ * (X * Y) ≤ X := by
    rw [inv_mul_eq_div, div_le_iff₀ hsum]
    nlinarith
  have hfracY : (X + Y)⁻¹ * (X * Y) ≤ Y := by
    rw [inv_mul_eq_div, div_le_iff₀ hsum]
    nlinarith
  have hPinv : 0 ≤ P⁻¹ := inv_nonneg.mpr hP.le
  rw [mul_assoc]
  rcases le_total X Y with hXY | hYX
  · rw [min_eq_left hXY]
    exact mul_le_mul_of_nonneg_left hfracX hPinv
  · rw [min_eq_right hYX]
    exact mul_le_mul_of_nonneg_left hfracY hPinv

theorem eight_le_hughesYoungDFIOptimalQ
    {P X Y : ℝ} (hlarge : 64 ≤ hughesYoungDFIOptimalU P X Y) :
    8 ≤ hughesYoungDFIOptimalQ P X Y := by
  unfold hughesYoungDFIOptimalQ
  rw [show (8 : ℝ) = Real.sqrt 64 by norm_num]
  exact Real.sqrt_le_sqrt hlarge

/-- Complete package of optimized scale identities consumed by a large
Hughes--Young dyadic box. -/
theorem hughesYoungDFIOptimalScale_spec
    {P X Y : ℝ} (hP : 0 < P) (hX : 0 < X) (hY : 0 < Y)
    (hlarge : 64 ≤ hughesYoungDFIOptimalU P X Y) :
    hughesYoungDFIOptimalU P X Y ≤ P⁻¹ * min X Y ∧
      8 ≤ hughesYoungDFIOptimalQ P X Y ∧
      hughesYoungDFIOptimalU P X Y =
        hughesYoungDFIOptimalQ P X Y ^ 2 ∧
      hughesYoungDFIOptimalQ P X Y ^ 2 =
        P⁻¹ * (X + Y)⁻¹ * (X * Y) := by
  exact ⟨hughesYoungDFIOptimalU_le_inv_mul_min hP hX hY,
    eight_le_hughesYoungDFIOptimalQ hlarge,
    hughesYoungDFIOptimalU_eq_Q_sq hP hX.le hY.le,
    hughesYoungDFIOptimalQ_sq hP hX.le hY.le⟩

/-- Failure of the DFI `Q ≥ 8` condition is exactly the explicit small-box
inequality. -/
theorem hughesYoungDFIOptimalU_lt_sixtyFour_of_not_large
    {P X Y : ℝ} (h : ¬ 64 ≤ hughesYoungDFIOptimalU P X Y) :
    hughesYoungDFIOptimalU P X Y < 64 :=
  lt_of_not_ge h

/-- On the factor-four comparable range, failure of the optimized DFI
scale forces the second physical scale into the equation-(65) range.  This
is the quantitative harmonic-mean calculation used in the small-box branch
of Hughes--Young: `XY/(P(X+Y)) < 64` and `Y ≤ 4X` imply `Y < 320P`. -/
theorem hughesYoung_secondScale_lt_threeHundredTwenty_mul_of_optimalU_lt
    {P X Y : ℝ} (hP : 0 < P) (hX : 0 < X) (hY : 0 < Y)
    (hYX : Y ≤ 4 * X)
    (hsmall : hughesYoungDFIOptimalU P X Y < 64) :
    Y < 320 * P := by
  have hsum : 0 < X + Y := add_pos hX hY
  have hidentity :
      hughesYoungDFIOptimalU P X Y * (P * (X + Y)) = X * Y := by
    unfold hughesYoungDFIOptimalU
    field_simp
  have hsumBound : X + Y ≤ 5 * X := by linarith
  have hUP : hughesYoungDFIOptimalU P X Y * P < 64 * P :=
    mul_lt_mul_of_pos_right hsmall hP
  by_contra hYP
  have hYP' : 320 * P ≤ Y := le_of_not_gt hYP
  have hU0 : 0 ≤ hughesYoungDFIOptimalU P X Y :=
    hughesYoungDFIOptimalU_nonneg hP hX.le hY.le
  have hleft :
      hughesYoungDFIOptimalU P X Y * (P * (X + Y)) <
        64 * P * (5 * X) := by
    calc
      hughesYoungDFIOptimalU P X Y * (P * (X + Y)) =
          (hughesYoungDFIOptimalU P X Y * P) * (X + Y) := by ring
      _ < (64 * P) * (X + Y) :=
        mul_lt_mul_of_pos_right hUP hsum
      _ ≤ (64 * P) * (5 * X) := by gcongr
  rw [hidentity] at hleft
  nlinarith

/-- Symmetric first-coordinate form of the comparable small-scale bound. -/
theorem hughesYoung_firstScale_lt_threeHundredTwenty_mul_of_optimalU_lt
    {P X Y : ℝ} (hP : 0 < P) (hX : 0 < X) (hY : 0 < Y)
    (hXY : X ≤ 4 * Y)
    (hsmall : hughesYoungDFIOptimalU P X Y < 64) :
    X < 320 * P := by
  have hsymm : hughesYoungDFIOptimalU P X Y =
      hughesYoungDFIOptimalU P Y X := by
    unfold hughesYoungDFIOptimalU
    ring
  rw [hsymm] at hsmall
  exact hughesYoung_secondScale_lt_threeHundredTwenty_mul_of_optimalU_lt
    hP hY hX hXY hsmall

end RiemannZeta.GuthMaynard
