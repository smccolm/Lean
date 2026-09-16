import Tao2026.TypeIConvolutionBridge
import Tao2026.WeylDifferencing
import Tao2026.TypeIIArithmetic

/-!
# Quadratic Weyl bridge for Type I fibers

This module removes the endpoint bookkeeping from the quadratic specialization
of the four-step reciprocal-phase estimate.  If an interval and four copies of
its optimized differencing range fit inside one local dyadic window, the full
analytic theorem applies.  The stronger elementary condition used here is that
five copies of the interval length fit in that window.
-/

open ArithmeticFunction Complex Finset
open scoped BigOperators zeta

namespace Tao2026

noncomputable section

/-- A nonzero higher reciprocal parameter makes the phase scale positive on
every positive real scale. -/
theorem reciprocalPhaseScale_pos_of_right_ne_zero
    (N M : ℝ) (j : ℕ) {X : ℝ} (hX : 0 < X) (hM : M ≠ 0) :
    0 < reciprocalPhaseScale N M j X := by
  unfold reciprocalPhaseScale
  have hterm : 0 < |M| / X ^ j :=
    div_pos (abs_pos.mpr hM) (pow_pos hX j)
  positivity

/-- On a quadratic dyadic window, the phase scale can decrease by at most a
factor four. -/
theorem reciprocalPhaseScale_quadratic_le_four_mul_of_le_two_mul
    (N M : ℝ) {X Y : ℝ} (hX : 0 < X) (hY : 0 < Y)
    (hXY : Y ≤ 2 * X) :
    reciprocalPhaseScale N M 2 X ≤
      4 * reciprocalPhaseScale N M 2 Y := by
  have hlinear : |N| / X ≤ 2 * (|N| / Y) := by
    rw [← mul_div_assoc]
    rw [le_div_iff₀ hY]
    have hmul := mul_le_mul_of_nonneg_left hXY
      (div_nonneg (abs_nonneg N) hX.le)
    calc
      |N| / X * Y ≤ |N| / X * (2 * X) := hmul
      _ = 2 * |N| := by field_simp
  have hquadratic : |M| / X ^ 2 ≤ 4 * (|M| / Y ^ 2) := by
    rw [← mul_div_assoc]
    rw [le_div_iff₀ (pow_pos hY 2)]
    have hpow : Y ^ 2 ≤ (2 * X) ^ 2 :=
      pow_le_pow_left₀ hY.le hXY 2
    have hmul := mul_le_mul_of_nonneg_left hpow
      (div_nonneg (abs_nonneg M) (pow_pos hX 2).le)
    calc
      |M| / X ^ 2 * Y ^ 2 ≤ |M| / X ^ 2 * (2 * X) ^ 2 := hmul
      _ = 4 * |M| := by field_simp; ring
  unfold reciprocalPhaseScale
  nlinarith [div_nonneg (abs_nonneg N) hY.le,
    div_nonneg (abs_nonneg M) (pow_pos hY 2).le]

/-- A source error budget at the left endpoint controls the complete
four-step effective error at every quadratic scale in the same dyadic window.
The factor four is the exact worst loss in the inverse phase scale. -/
theorem reciprocalPhaseFourStepEffectiveErrorScale_quadratic_le_one_of_dyadic
    (N M : ℝ) {L : ℕ} {X Y : ℝ}
    (hX : 0 < X) (hY : 0 < Y) (hXY : X ≤ Y) (hYtop : Y ≤ 2 * X)
    (hM : M ≠ 0) (hLength : 1 ≤ L)
    (hbudget :
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N M 2 X / X ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N M 2 X ≤ 1) :
    reciprocalPhaseFourStepEffectiveErrorScale N M 2 Y L ≤ 1 := by
  have hFX : 0 < reciprocalPhaseScale N M 2 X :=
    reciprocalPhaseScale_pos_of_right_ne_zero N M 2 hX hM
  have hFY : 0 < reciprocalPhaseScale N M 2 Y :=
    reciprocalPhaseScale_pos_of_right_ne_zero N M 2 hY hM
  have hscaleUpper : reciprocalPhaseScale N M 2 Y ≤
      reciprocalPhaseScale N M 2 X :=
    reciprocalPhaseScale_anti N M 2 hX hXY
  have hpow : X ^ 5 ≤ Y ^ 5 := pow_le_pow_left₀ hX.le hXY 5
  have hupper : reciprocalPhaseScale N M 2 Y / Y ^ 5 ≤
      reciprocalPhaseScale N M 2 X / X ^ 5 := by
    calc
      reciprocalPhaseScale N M 2 Y / Y ^ 5 ≤
          reciprocalPhaseScale N M 2 X / Y ^ 5 :=
        div_le_div_of_nonneg_right hscaleUpper (pow_pos hY 5).le
      _ ≤ reciprocalPhaseScale N M 2 X / X ^ 5 :=
        div_le_div_of_nonneg_left hFX.le (pow_pos hX 5) hpow
  have hscaleLower : reciprocalPhaseScale N M 2 X ≤
      4 * reciprocalPhaseScale N M 2 Y :=
    reciprocalPhaseScale_quadratic_le_four_mul_of_le_two_mul N M hX hY hYtop
  have hinv : 1 / reciprocalPhaseScale N M 2 Y ≤
      4 / reciprocalPhaseScale N M 2 X := by
    rw [div_le_div_iff₀ hFY hFX]
    simpa only [one_mul] using hscaleLower
  have hraw := reciprocalPhaseFourStepEffectiveErrorScale_le_of_scale_bounds
    N M Y (reciprocalPhaseScale N M 2 X / X ^ 5)
      (4 / reciprocalPhaseScale N M 2 X) 2 L hupper hinv hLength
  exact hraw.trans hbudget

/-- Under the effective-error bound, the optimized four-step differencing
range is no longer than the interval itself. -/
theorem reciprocalPhaseFourStepOptimizedRange_le_length
    (N M : ℝ) {j L : ℕ} {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M j X)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M j X L ≤ 1) :
    reciprocalPhaseFourStepOptimizedRange N M j X L ≤ L := by
  have hwidth := reciprocalPhaseFourStepCriticalWidth_le_one
    N M hX hF herrorSmall
  have hrange := reciprocalPhaseFourStepOptimizedRange_cast_le
    N M hX hF (j := j) (L := L)
  have hrange' :
      (reciprocalPhaseFourStepOptimizedRange N M j X L : ℝ) ≤ (L : ℝ) := by
    calc
      (reciprocalPhaseFourStepOptimizedRange N M j X L : ℝ) ≤
          (L : ℝ) * reciprocalPhaseFourStepCriticalWidth N M j X L := hrange
      _ ≤ (L : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left hwidth (Nat.cast_nonneg L)
      _ = (L : ℝ) := by ring
  exact_mod_cast hrange'

/-- Quadratic source wrapper for the four-step Weyl theorem.  The condition
`a + 5(b-a) ≤ 2X` is an elementary sufficient margin: the interval consumes
one copy of its length and the four differencing rounds consume at most four
more. -/
theorem norm_reciprocalPhaseSum_le_fourStepWeyl_twoTerm_quadratic_of_five_fit
    (N M : ℝ) (orders : Finset ℕ) (a b : ℕ) {X : ℝ}
    (hX : 0 < X) (hF : 0 < reciprocalPhaseScale N M 2 X)
    (hFlow : reciprocalPhaseScale N M 2 X ≤ X ^ 4)
    (herrorSmall :
      reciprocalPhaseFourStepEffectiveErrorScale N M 2 X (b - a) ≤ 1)
    (hM : M ≠ 0) (hLength : 1 ≤ b - a)
    (ha : X ≤ (a : ℝ))
    (hfit : (a : ℝ) + 5 * (b - a : ℕ) ≤ 2 * X)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    let p := reciprocalPhaseFourStepTwoTermWidth N M 2 X
    ‖reciprocalPhaseSum N M 2 a b‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((b - a : ℕ) : ℝ)) * X * p) := by
  have hrangeNat :
      reciprocalPhaseFourStepOptimizedRange N M 2 X (b - a) ≤ b - a :=
    reciprocalPhaseFourStepOptimizedRange_le_length N M hX hF herrorSmall
  have hrange :
      (4 * reciprocalPhaseFourStepOptimizedRange N M 2 X (b - a) : ℕ) ≤
        4 * (b - a) := Nat.mul_le_mul_left 4 hrangeNat
  have hrangeReal :
      ((4 * reciprocalPhaseFourStepOptimizedRange N M 2 X (b - a) : ℕ) : ℝ) ≤
        4 * (b - a : ℕ) := by exact_mod_cast hrange
  have haTop : (a : ℝ) ≤ 2 * X := by
    have hlengthNonneg : (0 : ℝ) ≤ 5 * (b - a : ℕ) := by positivity
    linarith
  have haIcc : (a : ℝ) ∈ Set.Icc X (2 * X) := ⟨ha, haTop⟩
  have heval : (a : ℝ) + (b - a : ℕ) +
      (4 * reciprocalPhaseFourStepOptimizedRange N M 2 X (b - a) : ℕ) ≤
        2 * X := by
    have hcombine : (a : ℝ) + (b - a : ℕ) + 4 * (b - a : ℕ) =
        (a : ℝ) + 5 * (b - a : ℕ) := by ring
    calc
      (a : ℝ) + (b - a : ℕ) +
          (4 * reciprocalPhaseFourStepOptimizedRange N M 2 X (b - a) : ℕ) ≤
        (a : ℝ) + (b - a : ℕ) + 4 * (b - a : ℕ) := by linarith
      _ = (a : ℝ) + 5 * (b - a : ℕ) := hcombine
      _ ≤ 2 * X := hfit
  have hpow : ∀ t ∈ Set.Icc X (2 * X),
      t ^ (2 - 1) ≤ 2 * X ^ (2 - 1) := by
    intro t ht
    simpa using ht.2
  exact norm_reciprocalPhaseSum_le_fourStepWeyl_twoTerm
    N M orders a b hX hF hFlow herrorSmall hM (by norm_num) hLength
      haIcc heval heval hpow hrFive hrSix

/-! ## Canonical ten-block quadratic subdivision -/

/-- A ten-block subdivision leaves enough room for four differencing rounds
after ceiling rounding. -/
theorem five_mul_dyadicShortIntervalLength_ten_le
    {D : ℕ} (hD : 10 ≤ D) :
    5 * dyadicShortIntervalLength D 10 ≤ D := by
  have hq := dyadicShortIntervalLength_le_div_add_one D
    (by norm_num : 0 < (10 : ℕ))
  omega

/-- Left endpoint of a canonical Type I quadratic Weyl block. -/
def typeIQuadraticWeylBlockLower (D k : ℕ) : ℕ :=
  D + k * dyadicShortIntervalLength D 10

/-- Right endpoint of a canonical Type I quadratic Weyl block. -/
def typeIQuadraticWeylBlockUpper (D k : ℕ) : ℕ :=
  min (2 * D) (D + (k + 1) * dyadicShortIntervalLength D 10)

theorem shortIntervalBlock_ten_eq_typeIQuadraticWeylBlock
    {D k : ℕ} (hD : 0 < D) :
    shortIntervalBlock D (2 * D) (dyadicShortIntervalLength D 10) k =
      Finset.Ico (typeIQuadraticWeylBlockLower D k)
        (typeIQuadraticWeylBlockUpper D k) := by
  rw [shortIntervalBlock_eq_Ico
    (dyadicShortIntervalLength_pos hD (by norm_num : 0 < (10 : ℕ)))]
  rfl

/-- Exact reconstruction of the quadratic reciprocal-phase sum on `[D,2D)`
from its canonical ten-block subdivision. -/
theorem reciprocalPhaseSum_eq_sum_typeIQuadraticWeylBlocks
    (N M : ℝ) {D : ℕ} (hD : 0 < D) :
    reciprocalPhaseSum N M 2 D (2 * D) =
      ∑ k ∈ Finset.range
          (shortIntervalBlockCount D (2 * D)
            (dyadicShortIntervalLength D 10)),
        reciprocalPhaseSum N M 2
          (typeIQuadraticWeylBlockLower D k)
          (typeIQuadraticWeylBlockUpper D k) := by
  unfold reciprocalPhaseSum
  rw [sum_shortIntervalBlocks _
    (dyadicShortIntervalLength_pos hD (by norm_num : 0 < (10 : ℕ)))]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [shortIntervalBlock_ten_eq_typeIQuadraticWeylBlock hD]

/-- Triangle-inequality form of the exact ten-block reconstruction. -/
theorem norm_reciprocalPhaseSum_le_sum_typeIQuadraticWeylBlocks
    (N M : ℝ) {D : ℕ} (hD : 0 < D) :
    ‖reciprocalPhaseSum N M 2 D (2 * D)‖ ≤
      ∑ k ∈ Finset.range
          (shortIntervalBlockCount D (2 * D)
            (dyadicShortIntervalLength D 10)),
        ‖reciprocalPhaseSum N M 2
          (typeIQuadraticWeylBlockLower D k)
          (typeIQuadraticWeylBlockUpper D k)‖ := by
  rw [reciprocalPhaseSum_eq_sum_typeIQuadraticWeylBlocks N M hD]
  exact norm_sum_le _ _

/-- Every nonempty canonical ten-block lies in the local dyadic window based
at its own left endpoint and satisfies the five-length fit condition. -/
theorem typeIQuadraticWeylBlock_geometry
    {D k : ℕ} (hD : 10 ≤ D)
    (hLength : 1 ≤ typeIQuadraticWeylBlockUpper D k -
      typeIQuadraticWeylBlockLower D k) :
    let lo := typeIQuadraticWeylBlockLower D k
    let hi := typeIQuadraticWeylBlockUpper D k
    D ≤ lo ∧ lo ≤ 2 * D ∧ hi - lo ≤ dyadicShortIntervalLength D 10 ∧
      lo + 5 * (hi - lo) ≤ 2 * lo := by
  dsimp only
  let q := dyadicShortIntervalLength D 10
  let lo := typeIQuadraticWeylBlockLower D k
  let hi := typeIQuadraticWeylBlockUpper D k
  change D ≤ lo ∧ lo ≤ 2 * D ∧ hi - lo ≤ q ∧
    lo + 5 * (hi - lo) ≤ 2 * lo
  change 1 ≤ hi - lo at hLength
  have hqfit : 5 * q ≤ D := by
    simpa only [q] using five_mul_dyadicShortIntervalLength_ten_le hD
  have hlo : D ≤ lo := by
    unfold lo typeIQuadraticWeylBlockLower
    omega
  have hhiTop : hi ≤ 2 * D := by
    unfold hi typeIQuadraticWeylBlockUpper
    exact min_le_left _ _
  have hlohi : lo < hi := by omega
  have hloTop : lo ≤ 2 * D := hlohi.le.trans hhiTop
  have hhiWidth : hi ≤ lo + q := by
    unfold hi lo typeIQuadraticWeylBlockUpper typeIQuadraticWeylBlockLower
    calc
      min (2 * D) (D + (k + 1) * q) ≤ D + (k + 1) * q := min_le_right _ _
      _ = D + k * q + q := by rw [Nat.add_mul]; omega
  have hlength : hi - lo ≤ q := by omega
  have hfive : 5 * (hi - lo) ≤ lo :=
    (Nat.mul_le_mul_left 5 hlength).trans (hqfit.trans hlo)
  exact ⟨hlo, hloTop, hlength, by omega⟩

/-- The quadratic four-step estimate on one nonempty canonical ten-block,
with every local analytic premise discharged from source-scale bounds at `D`.
-/
theorem norm_reciprocalPhaseSum_typeIQuadraticWeylBlock_le
    (N M : ℝ) (orders : Finset ℕ) {D k : ℕ}
    (hD : 10 ≤ D) (hM : M ≠ 0)
    (hFlow : reciprocalPhaseScale N M 2 D ≤ (D : ℝ) ^ 4)
    (hbudget :
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N M 2 D / (D : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N M 2 D ≤ 1)
    (hLength : 1 ≤ typeIQuadraticWeylBlockUpper D k -
      typeIQuadraticWeylBlockLower D k)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    let lo := typeIQuadraticWeylBlockLower D k
    let hi := typeIQuadraticWeylBlockUpper D k
    let p := reciprocalPhaseFourStepTwoTermWidth N M 2 lo
    ‖reciprocalPhaseSum N M 2 lo hi‖ ≤
      ((370 * orders.card + 173 : ℕ) : ℝ) *
        (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
          (1 + Real.log ((hi - lo : ℕ) : ℝ)) * lo * p) := by
  dsimp only
  let lo := typeIQuadraticWeylBlockLower D k
  let hi := typeIQuadraticWeylBlockUpper D k
  have hgeom := typeIQuadraticWeylBlock_geometry hD hLength
  dsimp only at hgeom
  rcases hgeom with ⟨hDloNat, hloTopNat, _hlength, hfitNat⟩
  have hDposNat : 0 < D := by omega
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hDposNat
  have hloposNat : 0 < lo := hDposNat.trans_le hDloNat
  have hlopos : (0 : ℝ) < lo := by exact_mod_cast hloposNat
  have hDlo : (D : ℝ) ≤ lo := by exact_mod_cast hDloNat
  have hloTop : (lo : ℝ) ≤ 2 * D := by exact_mod_cast hloTopNat
  have hF : 0 < reciprocalPhaseScale N M 2 lo :=
    reciprocalPhaseScale_pos_of_right_ne_zero N M 2 hlopos hM
  have hscaleUpper : reciprocalPhaseScale N M 2 lo ≤
      reciprocalPhaseScale N M 2 D :=
    reciprocalPhaseScale_anti N M 2 hDpos hDlo
  have hpow : (D : ℝ) ^ 4 ≤ (lo : ℝ) ^ 4 :=
    pow_le_pow_left₀ hDpos.le hDlo 4
  have hFlowLocal : reciprocalPhaseScale N M 2 lo ≤ (lo : ℝ) ^ 4 :=
    hscaleUpper.trans (hFlow.trans hpow)
  have herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale
      N M 2 lo (hi - lo) ≤ 1 :=
    reciprocalPhaseFourStepEffectiveErrorScale_quadratic_le_one_of_dyadic
      N M hDpos hlopos hDlo hloTop hM hLength hbudget
  have hfit : (lo : ℝ) + 5 * (hi - lo : ℕ) ≤ 2 * (lo : ℝ) := by
    exact_mod_cast hfitNat
  exact norm_reciprocalPhaseSum_le_fourStepWeyl_twoTerm_quadratic_of_five_fit
    N M orders lo hi hlopos hF hFlowLocal herrorSmall hM hLength
      le_rfl hfit hrFive hrSix

/-! ## Uniform source width and complete dyadic sum -/

/-- One source-scale width that dominates every local two-term width in the
quadratic dyadic subdivision. -/
noncomputable def typeIQuadraticWeylSourceWidth
    (N M : ℝ) (D : ℕ) : ℝ :=
  (reciprocalPhaseScale N M 2 D / (D : ℝ) ^ 5 +
    4 / reciprocalPhaseScale N M 2 D) ^ (1 / 1024 : ℝ)

theorem typeIQuadraticWeylSourceWidth_nonneg
    (N M : ℝ) (D : ℕ) :
    0 ≤ typeIQuadraticWeylSourceWidth N M D := by
  unfold typeIQuadraticWeylSourceWidth
  have hscale : 0 ≤ reciprocalPhaseScale N M 2 D := by
    unfold reciprocalPhaseScale
    positivity
  have hinside : 0 ≤ reciprocalPhaseScale N M 2 D / (D : ℝ) ^ 5 +
      4 / reciprocalPhaseScale N M 2 D :=
    add_nonneg (div_nonneg hscale (pow_nonneg (Nat.cast_nonneg D) 5))
      (div_nonneg (by norm_num) hscale)
  exact Real.rpow_nonneg hinside _

/-- The factor-four dyadic phase comparison uniformizes both terms in the
local two-term Weyl width. -/
theorem reciprocalPhaseFourStepTwoTermWidth_quadratic_le_sourceWidth_of_dyadic
    (N M : ℝ) {D Y : ℝ} (hD : 0 < D) (hY : 0 < Y)
    (hDY : D ≤ Y) (hYtop : Y ≤ 2 * D) (hM : M ≠ 0) :
    reciprocalPhaseFourStepTwoTermWidth N M 2 Y ≤
      (reciprocalPhaseScale N M 2 D / D ^ 5 +
        4 / reciprocalPhaseScale N M 2 D) ^ (1 / 1024 : ℝ) := by
  have hFD : 0 < reciprocalPhaseScale N M 2 D :=
    reciprocalPhaseScale_pos_of_right_ne_zero N M 2 hD hM
  have hFY : 0 < reciprocalPhaseScale N M 2 Y :=
    reciprocalPhaseScale_pos_of_right_ne_zero N M 2 hY hM
  have hscaleUpper : reciprocalPhaseScale N M 2 Y ≤
      reciprocalPhaseScale N M 2 D :=
    reciprocalPhaseScale_anti N M 2 hD hDY
  have hpow : D ^ 5 ≤ Y ^ 5 := pow_le_pow_left₀ hD.le hDY 5
  have hupper : reciprocalPhaseScale N M 2 Y / Y ^ 5 ≤
      reciprocalPhaseScale N M 2 D / D ^ 5 := by
    calc
      reciprocalPhaseScale N M 2 Y / Y ^ 5 ≤
          reciprocalPhaseScale N M 2 D / Y ^ 5 :=
        div_le_div_of_nonneg_right hscaleUpper (pow_pos hY 5).le
      _ ≤ reciprocalPhaseScale N M 2 D / D ^ 5 :=
        div_le_div_of_nonneg_left hFD.le (pow_pos hD 5) hpow
  have hscaleLower : reciprocalPhaseScale N M 2 D ≤
      4 * reciprocalPhaseScale N M 2 Y :=
    reciprocalPhaseScale_quadratic_le_four_mul_of_le_two_mul
      N M hD hY hYtop
  have hinv : 1 / reciprocalPhaseScale N M 2 Y ≤
      4 / reciprocalPhaseScale N M 2 D := by
    rw [div_le_div_iff₀ hFY hFD]
    simpa only [one_mul] using hscaleLower
  unfold reciprocalPhaseFourStepTwoTermWidth reciprocalPhaseFourStepTwoTermError
  apply Real.rpow_le_rpow
  · positivity
  · exact add_le_add hupper hinv
  · norm_num

/-- Uniform majorant for one canonical quadratic Weyl block. -/
noncomputable def typeIQuadraticWeylUniformBlockMajorant
    (N M : ℝ) (orders : Finset ℕ) (D : ℕ) : ℝ :=
  ((370 * orders.card + 173 : ℕ) : ℝ) *
    (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1) *
        (1 + Real.log (D : ℝ)) * (2 * D : ℕ) *
          typeIQuadraticWeylSourceWidth N M D)

theorem typeIQuadraticWeylUniformBlockMajorant_nonneg
    (N M : ℝ) (orders : Finset ℕ) {D : ℕ} (hD : 1 ≤ D) :
    0 ≤ typeIQuadraticWeylUniformBlockMajorant N M orders D := by
  unfold typeIQuadraticWeylUniformBlockMajorant
  have hlog : 0 ≤ Real.log (D : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hD)
  have hsource := typeIQuadraticWeylSourceWidth_nonneg N M D
  positivity

/-- Every block, including an empty terminal block, is controlled by the same
source-scale majorant. -/
theorem norm_reciprocalPhaseSum_typeIQuadraticWeylBlock_le_uniform
    (N M : ℝ) (orders : Finset ℕ) {D k : ℕ}
    (hD : 10 ≤ D) (hM : M ≠ 0)
    (hFlow : reciprocalPhaseScale N M 2 D ≤ (D : ℝ) ^ 4)
    (hbudget :
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N M 2 D / (D : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N M 2 D ≤ 1)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M 2
        (typeIQuadraticWeylBlockLower D k)
        (typeIQuadraticWeylBlockUpper D k)‖ ≤
      typeIQuadraticWeylUniformBlockMajorant N M orders D := by
  let lo := typeIQuadraticWeylBlockLower D k
  let hi := typeIQuadraticWeylBlockUpper D k
  by_cases hLength : 1 ≤ hi - lo
  · have hbase := norm_reciprocalPhaseSum_typeIQuadraticWeylBlock_le
      N M orders hD hM hFlow hbudget hLength hrFive hrSix
    have hgeom := typeIQuadraticWeylBlock_geometry hD hLength
    dsimp only at hbase hgeom
    rcases hgeom with ⟨hDloNat, hloTopNat, hlength, _hfit⟩
    have hDposNat : 0 < D := by omega
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hDposNat
    have hloposNat : 0 < lo := hDposNat.trans_le hDloNat
    have hlopos : (0 : ℝ) < lo := by exact_mod_cast hloposNat
    have hDlo : (D : ℝ) ≤ lo := by exact_mod_cast hDloNat
    have hloTop : (lo : ℝ) ≤ 2 * D := by exact_mod_cast hloTopNat
    have hqD : dyadicShortIntervalLength D 10 ≤ D := by
      unfold dyadicShortIntervalLength
      exact ceilDiv_le_self_of_pos D 10 (by norm_num)
    have hlengthD : hi - lo ≤ D := hlength.trans hqD
    have hlog : Real.log ((hi - lo : ℕ) : ℝ) ≤ Real.log (D : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < hi - lo))
        (by exact_mod_cast hlengthD)
    have hwidth : reciprocalPhaseFourStepTwoTermWidth N M 2 lo ≤
        typeIQuadraticWeylSourceWidth N M D := by
      unfold typeIQuadraticWeylSourceWidth
      exact reciprocalPhaseFourStepTwoTermWidth_quadratic_le_sourceWidth_of_dyadic
        N M hDpos hlopos hDlo hloTop hM
    refine hbase.trans ?_
    unfold typeIQuadraticWeylUniformBlockMajorant
    have hlogNonneg : 0 ≤ 1 + Real.log ((hi - lo : ℕ) : ℝ) := by
      have hone : (1 : ℝ) ≤ (hi - lo : ℕ) := by exact_mod_cast hLength
      have := Real.log_nonneg hone
      linarith
    have hsourceNonneg := typeIQuadraticWeylSourceWidth_nonneg N M D
    have hlocalScalePos : 0 < reciprocalPhaseScale N M 2 lo :=
      reciprocalPhaseScale_pos_of_right_ne_zero N M 2 hlopos hM
    have hwidthNonneg : 0 ≤ reciprocalPhaseFourStepTwoTermWidth N M 2 lo :=
      (reciprocalPhaseFourStepTwoTermWidth_pos N M hlopos hlocalScalePos).le
    gcongr
  · have hle : hi ≤ lo := by omega
    have hzero : reciprocalPhaseSum N M 2 lo hi = 0 := by
      have hIco : Finset.Ico lo hi = ∅ :=
        Finset.Ico_eq_empty (Nat.not_lt.mpr hle)
      simp [reciprocalPhaseSum, hIco]
    change ‖reciprocalPhaseSum N M 2 lo hi‖ ≤ _
    rw [hzero, norm_zero]
    exact typeIQuadraticWeylUniformBlockMajorant_nonneg N M orders (by omega)

/-- Complete source-scale bound for the quadratic reciprocal-phase sum on a
dyadic interval.  The factor ten is the exact subdivision budget. -/
theorem norm_reciprocalPhaseSum_dyadic_le_typeIQuadraticWeylSource
    (N M : ℝ) (orders : Finset ℕ) {D : ℕ}
    (hD : 10 ≤ D) (hM : M ≠ 0)
    (hFlow : reciprocalPhaseScale N M 2 D ≤ (D : ℝ) ^ 4)
    (hbudget :
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N M 2 D / (D : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N M 2 D ≤ 1)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M 2 D (2 * D)‖ ≤
      10 * typeIQuadraticWeylUniformBlockMajorant N M orders D := by
  have hDpos : 0 < D := by omega
  let count := shortIntervalBlockCount D (2 * D)
    (dyadicShortIntervalLength D 10)
  have hcount : count ≤ 10 := by
    unfold count
    exact shortIntervalBlockCount_dyadic_le hDpos (by norm_num)
  calc
    ‖reciprocalPhaseSum N M 2 D (2 * D)‖ ≤
        ∑ k ∈ Finset.range count,
          ‖reciprocalPhaseSum N M 2
            (typeIQuadraticWeylBlockLower D k)
            (typeIQuadraticWeylBlockUpper D k)‖ := by
      simpa only [count] using
        norm_reciprocalPhaseSum_le_sum_typeIQuadraticWeylBlocks N M hDpos
    _ ≤ ∑ _k ∈ Finset.range count,
          typeIQuadraticWeylUniformBlockMajorant N M orders D := by
      apply Finset.sum_le_sum
      intro k _hk
      exact norm_reciprocalPhaseSum_typeIQuadraticWeylBlock_le_uniform
        N M orders hD hM hFlow hbudget hrFive hrSix
    _ = (count : ℝ) *
          typeIQuadraticWeylUniformBlockMajorant N M orders D := by
      rw [Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
    _ ≤ 10 * typeIQuadraticWeylUniformBlockMajorant N M orders D := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcount
      · exact typeIQuadraticWeylUniformBlockMajorant_nonneg
          N M orders (by omega)

/-! ## Arbitrary subintervals of a quadratic dyadic window -/

def typeIQuadraticWeylSubBlockLower (D a k : ℕ) : ℕ :=
  a + k * dyadicShortIntervalLength D 10

def typeIQuadraticWeylSubBlockUpper (D a b k : ℕ) : ℕ :=
  min b (a + (k + 1) * dyadicShortIntervalLength D 10)

theorem shortIntervalBlock_eq_typeIQuadraticWeylSubBlock
    {D a b k : ℕ} (hD : 0 < D) :
    shortIntervalBlock a b (dyadicShortIntervalLength D 10) k =
      Finset.Ico (typeIQuadraticWeylSubBlockLower D a k)
        (typeIQuadraticWeylSubBlockUpper D a b k) := by
  rw [shortIntervalBlock_eq_Ico
    (dyadicShortIntervalLength_pos hD (by norm_num : 0 < (10 : ℕ)))]
  rfl

theorem reciprocalPhaseSum_eq_sum_typeIQuadraticWeylSubBlocks
    (N M : ℝ) {D a b : ℕ} (hD : 0 < D) :
    reciprocalPhaseSum N M 2 a b =
      ∑ k ∈ Finset.range
          (shortIntervalBlockCount a b (dyadicShortIntervalLength D 10)),
        reciprocalPhaseSum N M 2
          (typeIQuadraticWeylSubBlockLower D a k)
          (typeIQuadraticWeylSubBlockUpper D a b k) := by
  unfold reciprocalPhaseSum
  rw [sum_shortIntervalBlocks _
    (dyadicShortIntervalLength_pos hD (by norm_num : 0 < (10 : ℕ)))]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [shortIntervalBlock_eq_typeIQuadraticWeylSubBlock hD]

theorem norm_reciprocalPhaseSum_le_sum_typeIQuadraticWeylSubBlocks
    (N M : ℝ) {D a b : ℕ} (hD : 0 < D) :
    ‖reciprocalPhaseSum N M 2 a b‖ ≤
      ∑ k ∈ Finset.range
          (shortIntervalBlockCount a b (dyadicShortIntervalLength D 10)),
        ‖reciprocalPhaseSum N M 2
          (typeIQuadraticWeylSubBlockLower D a k)
          (typeIQuadraticWeylSubBlockUpper D a b k)‖ := by
  rw [reciprocalPhaseSum_eq_sum_typeIQuadraticWeylSubBlocks N M hD]
  exact norm_sum_le _ _

/-- Every subinterval of `[D,2D)` uses at most ten canonical pieces. -/
theorem typeIQuadraticWeylSubBlockCount_le_ten
    {D a b : ℕ} (hD : 0 < D) (hDa : D ≤ a) (hbD : b ≤ 2 * D) :
    shortIntervalBlockCount a b (dyadicShortIntervalLength D 10) ≤ 10 := by
  apply shortIntervalBlockCount_le
    (dyadicShortIntervalLength_pos hD (by norm_num : 0 < (10 : ℕ)))
  have hlength : b - a ≤ D := by omega
  have hcover : D ≤ 10 * dyadicShortIntervalLength D 10 :=
    (ceilDiv_le_iff_le_mul (by norm_num : 0 < (10 : ℕ))).1 le_rfl
  calc
    b - a ≤ D := hlength
    _ ≤ 10 * dyadicShortIntervalLength D 10 := hcover
    _ = dyadicShortIntervalLength D 10 * 10 := Nat.mul_comm _ _

/-- Local geometry for a nonempty piece of an arbitrary source subinterval. -/
theorem typeIQuadraticWeylSubBlock_geometry
    {D a b k : ℕ} (hD : 10 ≤ D) (hDa : D ≤ a) (hbD : b ≤ 2 * D)
    (hLength : 1 ≤ typeIQuadraticWeylSubBlockUpper D a b k -
      typeIQuadraticWeylSubBlockLower D a k) :
    let lo := typeIQuadraticWeylSubBlockLower D a k
    let hi := typeIQuadraticWeylSubBlockUpper D a b k
    D ≤ lo ∧ lo ≤ 2 * D ∧ hi - lo ≤ dyadicShortIntervalLength D 10 ∧
      lo + 5 * (hi - lo) ≤ 2 * lo := by
  dsimp only
  let q := dyadicShortIntervalLength D 10
  let lo := typeIQuadraticWeylSubBlockLower D a k
  let hi := typeIQuadraticWeylSubBlockUpper D a b k
  change D ≤ lo ∧ lo ≤ 2 * D ∧ hi - lo ≤ q ∧
    lo + 5 * (hi - lo) ≤ 2 * lo
  change 1 ≤ hi - lo at hLength
  have hqfit : 5 * q ≤ D := by
    simpa only [q] using five_mul_dyadicShortIntervalLength_ten_le hD
  have hlo : D ≤ lo := by
    unfold lo typeIQuadraticWeylSubBlockLower
    omega
  have hhiTop : hi ≤ 2 * D := by
    unfold hi typeIQuadraticWeylSubBlockUpper
    exact (min_le_left _ _).trans hbD
  have hlohi : lo < hi := by omega
  have hloTop : lo ≤ 2 * D := hlohi.le.trans hhiTop
  have hhiWidth : hi ≤ lo + q := by
    unfold hi lo typeIQuadraticWeylSubBlockUpper typeIQuadraticWeylSubBlockLower
    calc
      min b (a + (k + 1) * q) ≤ a + (k + 1) * q := min_le_right _ _
      _ = a + k * q + q := by rw [Nat.add_mul]; omega
  have hlength : hi - lo ≤ q := by omega
  have hfive : 5 * (hi - lo) ≤ lo :=
    (Nat.mul_le_mul_left 5 hlength).trans (hqfit.trans hlo)
  exact ⟨hlo, hloTop, hlength, by omega⟩

/-- Uniform source majorant for every piece of every subinterval of the
quadratic dyadic window. -/
theorem norm_reciprocalPhaseSum_typeIQuadraticWeylSubBlock_le_uniform
    (N M : ℝ) (orders : Finset ℕ) {D a b k : ℕ}
    (hD : 10 ≤ D) (hDa : D ≤ a) (hbD : b ≤ 2 * D) (hM : M ≠ 0)
    (hFlow : reciprocalPhaseScale N M 2 D ≤ (D : ℝ) ^ 4)
    (hbudget :
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N M 2 D / (D : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N M 2 D ≤ 1)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M 2
        (typeIQuadraticWeylSubBlockLower D a k)
        (typeIQuadraticWeylSubBlockUpper D a b k)‖ ≤
      typeIQuadraticWeylUniformBlockMajorant N M orders D := by
  let lo := typeIQuadraticWeylSubBlockLower D a k
  let hi := typeIQuadraticWeylSubBlockUpper D a b k
  by_cases hLength : 1 ≤ hi - lo
  · have hgeom := typeIQuadraticWeylSubBlock_geometry hD hDa hbD hLength
    dsimp only at hgeom
    rcases hgeom with ⟨hDloNat, hloTopNat, hlength, hfitNat⟩
    have hDposNat : 0 < D := by omega
    have hDpos : (0 : ℝ) < D := by exact_mod_cast hDposNat
    have hloposNat : 0 < lo := hDposNat.trans_le hDloNat
    have hlopos : (0 : ℝ) < lo := by exact_mod_cast hloposNat
    have hDlo : (D : ℝ) ≤ lo := by exact_mod_cast hDloNat
    have hloTop : (lo : ℝ) ≤ 2 * D := by exact_mod_cast hloTopNat
    have hlocalScalePos : 0 < reciprocalPhaseScale N M 2 lo :=
      reciprocalPhaseScale_pos_of_right_ne_zero N M 2 hlopos hM
    have hscaleUpper : reciprocalPhaseScale N M 2 lo ≤
        reciprocalPhaseScale N M 2 D :=
      reciprocalPhaseScale_anti N M 2 hDpos hDlo
    have hpow : (D : ℝ) ^ 4 ≤ (lo : ℝ) ^ 4 :=
      pow_le_pow_left₀ hDpos.le hDlo 4
    have hFlowLocal : reciprocalPhaseScale N M 2 lo ≤ (lo : ℝ) ^ 4 :=
      hscaleUpper.trans (hFlow.trans hpow)
    have herrorSmall : reciprocalPhaseFourStepEffectiveErrorScale
        N M 2 lo (hi - lo) ≤ 1 :=
      reciprocalPhaseFourStepEffectiveErrorScale_quadratic_le_one_of_dyadic
        N M hDpos hlopos hDlo hloTop hM hLength hbudget
    have hfit : (lo : ℝ) + 5 * (hi - lo : ℕ) ≤ 2 * (lo : ℝ) := by
      exact_mod_cast hfitNat
    have hbase :=
      norm_reciprocalPhaseSum_le_fourStepWeyl_twoTerm_quadratic_of_five_fit
        N M orders lo hi hlopos hlocalScalePos hFlowLocal herrorSmall hM
          hLength le_rfl hfit hrFive hrSix
    have hqD : dyadicShortIntervalLength D 10 ≤ D := by
      unfold dyadicShortIntervalLength
      exact ceilDiv_le_self_of_pos D 10 (by norm_num)
    have hlengthD : hi - lo ≤ D := hlength.trans hqD
    have hlog : Real.log ((hi - lo : ℕ) : ℝ) ≤ Real.log (D : ℝ) :=
      Real.log_le_log (by exact_mod_cast (by omega : 0 < hi - lo))
        (by exact_mod_cast hlengthD)
    have hwidth : reciprocalPhaseFourStepTwoTermWidth N M 2 lo ≤
        typeIQuadraticWeylSourceWidth N M D := by
      unfold typeIQuadraticWeylSourceWidth
      exact reciprocalPhaseFourStepTwoTermWidth_quadratic_le_sourceWidth_of_dyadic
        N M hDpos hlopos hDlo hloTop hM
    dsimp only at hbase
    refine hbase.trans ?_
    unfold typeIQuadraticWeylUniformBlockMajorant
    have hlogNonneg : 0 ≤ 1 + Real.log ((hi - lo : ℕ) : ℝ) := by
      have hone : (1 : ℝ) ≤ (hi - lo : ℕ) := by exact_mod_cast hLength
      have := Real.log_nonneg hone
      linarith
    have hsourceNonneg := typeIQuadraticWeylSourceWidth_nonneg N M D
    have hwidthNonneg : 0 ≤ reciprocalPhaseFourStepTwoTermWidth N M 2 lo :=
      (reciprocalPhaseFourStepTwoTermWidth_pos N M hlopos hlocalScalePos).le
    gcongr
  · have hle : hi ≤ lo := by omega
    have hzero : reciprocalPhaseSum N M 2 lo hi = 0 := by
      have hIco : Finset.Ico lo hi = ∅ :=
        Finset.Ico_eq_empty (Nat.not_lt.mpr hle)
      simp [reciprocalPhaseSum, hIco]
    change ‖reciprocalPhaseSum N M 2 lo hi‖ ≤ _
    rw [hzero, norm_zero]
    exact typeIQuadraticWeylUniformBlockMajorant_nonneg N M orders (by omega)

/-- Uniform quadratic Weyl bound for every half-open natural subinterval of
`[D,2D)`. -/
theorem norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticWeylSource
    (N M : ℝ) (orders : Finset ℕ) {D a b : ℕ}
    (hD : 10 ≤ D) (hDa : D ≤ a) (hbD : b ≤ 2 * D) (hM : M ≠ 0)
    (hFlow : reciprocalPhaseScale N M 2 D ≤ (D : ℝ) ^ 4)
    (hbudget :
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N M 2 D / (D : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N M 2 D ≤ 1)
    (hrFive : 5 ∈ orders) (hrSix : 6 ∈ orders) :
    ‖reciprocalPhaseSum N M 2 a b‖ ≤
      10 * typeIQuadraticWeylUniformBlockMajorant N M orders D := by
  have hDpos : 0 < D := by omega
  let count := shortIntervalBlockCount a b (dyadicShortIntervalLength D 10)
  have hcount : count ≤ 10 := by
    unfold count
    exact typeIQuadraticWeylSubBlockCount_le_ten hDpos hDa hbD
  calc
    ‖reciprocalPhaseSum N M 2 a b‖ ≤
        ∑ k ∈ Finset.range count,
          ‖reciprocalPhaseSum N M 2
            (typeIQuadraticWeylSubBlockLower D a k)
            (typeIQuadraticWeylSubBlockUpper D a b k)‖ := by
      simpa only [count] using
        norm_reciprocalPhaseSum_le_sum_typeIQuadraticWeylSubBlocks
          N M (a := a) (b := b) hDpos
    _ ≤ ∑ _k ∈ Finset.range count,
          typeIQuadraticWeylUniformBlockMajorant N M orders D := by
      apply Finset.sum_le_sum
      intro k _hk
      exact norm_reciprocalPhaseSum_typeIQuadraticWeylSubBlock_le_uniform
        N M orders hD hDa hbD hM hFlow hbudget hrFive hrSix
    _ = (count : ℝ) *
          typeIQuadraticWeylUniformBlockMajorant N M orders D := by
      rw [Finset.sum_const, Finset.card_range]
      simp only [nsmul_eq_mul]
    _ ≤ 10 * typeIQuadraticWeylUniformBlockMajorant N M orders D := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hcount
      · exact typeIQuadraticWeylUniformBlockMajorant_nonneg
          N M orders (by omega)

/-! ## Rescaled Type I inner sums -/

/-- Minimal derivative-order set used by the quadratic Type I Weyl estimate. -/
def typeIQuadraticWeylOrders : Finset ℕ := {5, 6}

@[simp] theorem card_typeIQuadraticWeylOrders :
    typeIQuadraticWeylOrders.card = 2 := by
  simp [typeIQuadraticWeylOrders]

@[simp] theorem five_mem_typeIQuadraticWeylOrders :
    5 ∈ typeIQuadraticWeylOrders := by
  simp [typeIQuadraticWeylOrders]

@[simp] theorem six_mem_typeIQuadraticWeylOrders :
    6 ∈ typeIQuadraticWeylOrders := by
  simp [typeIQuadraticWeylOrders]

/-- The complete ten-block majorant after the literal Type I substitution
`(N,M,D) -> (N/m,M/m^2,ceil(P/m))`. -/
noncomputable def typeIQuadraticRescaledWeylMajorant
    (N M : ℝ) (P m : ℕ) : ℝ :=
  10 * typeIQuadraticWeylUniformBlockMajorant
    (N / m) (M / (m : ℝ) ^ 2) typeIQuadraticWeylOrders (P ⌈/⌉ m)

theorem typeIQuadraticRescaledWeylMajorant_nonneg
    (N M : ℝ) {P m : ℕ} (hD : 1 ≤ P ⌈/⌉ m) :
    0 ≤ typeIQuadraticRescaledWeylMajorant N M P m := by
  unfold typeIQuadraticRescaledWeylMajorant
  exact mul_nonneg (by norm_num)
    (typeIQuadraticWeylUniformBlockMajorant_nonneg _ _ _ hD)

/-- Source-facing unweighted Type I inner bound after exact ceiling rescaling.
-/
theorem norm_typeIProductRestrictedInnerSum_Ico_le_quadraticWeyl
    (N M : ℝ) {P a b B m : ℕ}
    (hP : 0 < P) (hPa : P ≤ a) (hbP : b ≤ 2 * P)
    (ha : 0 < a) (hbB : b ≤ B) (hm : 0 < m) (hM : M ≠ 0)
    (hD : 10 ≤ P ⌈/⌉ m)
    (hFlow : reciprocalPhaseScale N M 2 P ≤ ((P : ℝ) / m) ^ 4)
    (hbudget :
      let D := P ⌈/⌉ m
      let N' := N / m
      let M' := M / (m : ℝ) ^ 2
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N' M' 2 D / (D : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N' M' 2 D ≤ 1) :
    ‖typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B) (fun _ => 1) N M 2 m‖ ≤
      typeIQuadraticRescaledWeylMajorant N M P m := by
  rw [typeIProductRestrictedInnerSum_Ico_eq ha hbB hm]
  let D := P ⌈/⌉ m
  let N' := N / m
  let M' := M / (m : ℝ) ^ 2
  have hgeom := typeI_ceilDiv_dyadic_geometry hm hPa hbP
  have hM' : M' ≠ 0 := by
    unfold M'
    apply div_ne_zero hM
    exact pow_ne_zero 2 (by exact_mod_cast hm.ne')
  have hFlow' : reciprocalPhaseScale N' M' 2 D ≤ (D : ℝ) ^ 4 := by
    simpa only [D, N', M'] using
      reciprocalPhaseScale_typeI_rescale_ceilDiv_le_pow_four
        N M 2 hP hm hFlow
  have hresult :=
    norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticWeylSource
      N' M' typeIQuadraticWeylOrders hD hgeom.1 hgeom.2 hM'
        hFlow' (by simpa only [D, N', M'] using hbudget)
        five_mem_typeIQuadraticWeylOrders six_mem_typeIQuadraticWeylOrders
  simpa only [typeIQuadraticRescaledWeylMajorant, D, N', M'] using hresult

/-- Logarithmically weighted Type I inner bound, using the uniform arbitrary-
prefix theorem through finite Abel summation. -/
theorem norm_typeIProductRestrictedLogInnerSum_Ico_le_quadraticWeyl
    (N M : ℝ) {P a b B m : ℕ}
    (hP : 0 < P) (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (ha : 0 < a) (hbB : b ≤ B) (hm : 0 < m) (hM : M ≠ 0)
    (hD : 10 ≤ P ⌈/⌉ m)
    (hFlow : reciprocalPhaseScale N M 2 P ≤ ((P : ℝ) / m) ^ 4)
    (hbudget :
      let D := P ⌈/⌉ m
      let N' := N / m
      let M' := M / (m : ℝ) ^ 2
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N' M' 2 D / (D : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N' M' 2 D ≤ 1) :
    ‖typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B)
        (fun n => (Real.log n : ℂ)) N M 2 m‖ ≤
      2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
        typeIQuadraticRescaledWeylMajorant N M P m := by
  let D := P ⌈/⌉ m
  let N' := N / m
  let M' := M / (m : ℝ) ^ 2
  have hgeom := typeI_ceilDiv_dyadic_geometry hm hPa hbP
  have hM' : M' ≠ 0 := by
    unfold M'
    apply div_ne_zero hM
    exact pow_ne_zero 2 (by exact_mod_cast hm.ne')
  have hFlow' : reciprocalPhaseScale N' M' 2 D ≤ (D : ℝ) ^ 4 := by
    simpa only [D, N', M'] using
      reciprocalPhaseScale_typeI_rescale_ceilDiv_le_pow_four
        N M 2 hP hm hFlow
  have hR : 0 ≤ typeIQuadraticRescaledWeylMajorant N M P m :=
    typeIQuadraticRescaledWeylMajorant_nonneg N M (by omega)
  by_cases hceil : a ⌈/⌉ m < b ⌈/⌉ m
  · apply norm_typeIProductRestrictedLogInnerSum_Ico_le
      ha hbB hm N M 2 hceil hR
    intro k hak hkb
    have hkTop : k ≤ 2 * D := hkb.trans hgeom.2
    have hresult :=
      norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticWeylSource
        N' M' typeIQuadraticWeylOrders hD hgeom.1 hkTop hM'
          hFlow' (by simpa only [D, N', M'] using hbudget)
          five_mem_typeIQuadraticWeylOrders six_mem_typeIQuadraticWeylOrders
    simpa only [typeIQuadraticRescaledWeylMajorant, D, N', M'] using hresult
  · have hle : b ⌈/⌉ m ≤ a ⌈/⌉ m := Nat.le_of_not_gt hceil
    have hIco : Finset.Ico (a ⌈/⌉ m) (b ⌈/⌉ m) = ∅ :=
      Finset.Ico_eq_empty (Nat.not_lt.mpr hle)
    rw [typeIProductRestrictedLogInnerSum_Ico_eq ha hbB hm]
    simp only [hIco, Finset.sum_empty, norm_zero]
    have hbpos : 0 < b := hP.trans_le (hPa.trans hab)
    have hceilPos : 0 < b ⌈/⌉ m := typeI_ceilDiv_pos hbpos hm
    have hlog : 0 ≤ Real.log ((b ⌈/⌉ m : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hceilPos)
    positivity

/-! ## Active Type I family callbacks -/

/-- Every index in an active Vaughan Type I support is positive.  This is the
small but indispensable fact which permits the exact `t = m*n` rescaling in
each active fiber. -/
theorem pos_of_mem_vaughanTypeIActiveProductBlockSupport
    {B m : ℕ} {sk : ℕ × ℕ} {β : ℕ → ℂ}
    (hm : m ∈ vaughanTypeIActiveProductBlockSupport B sk β) :
    0 < m := by
  have hmRaw := (Finset.mem_filter.mp hm).1
  exact (Finset.mem_Ioc.mp (Finset.mem_filter.mp hmRaw).1).1

/-- The three analytic side conditions needed by the quadratic ten-block Weyl
estimate after the literal Type I substitution
`(N,M,D) -> (N/m,M/m^2,ceil(P/m))`. -/
def TypeIQuadraticWeylAdmissible (N M : ℝ) (P m : ℕ) : Prop :=
  10 ≤ P ⌈/⌉ m ∧
  reciprocalPhaseScale N M 2 P ≤ ((P : ℝ) / m) ^ 4 ∧
  let D := P ⌈/⌉ m
  let N' := N / m
  let M' := M / (m : ℝ) ^ 2
  240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      (reciprocalPhaseScale N' M' 2 D / (D : ℝ) ^ 5) +
    1 / 16 + 4 / reciprocalPhaseScale N' M' 2 D ≤ 1

/-- The second Vaughan Type I family, with zeta in the inner variable, is
bounded by the explicit quadratic Weyl majorant as soon as every genuinely
active outer fiber is admissible and has a common majorant `Q`. -/
theorem norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_quadraticWeyl
    (N M : ℝ) {P a b B U V : ℕ}
    (hP : 0 < P) (hPa : P ≤ a) (hbP : b ≤ 2 * P)
    (ha : 0 < a) (hbB : b ≤ B) (hB : 0 < B) (hM : M ≠ 0)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hadm : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
        TypeIQuadraticWeylAdmissible N M P m)
    (hmajor : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
        typeIQuadraticRescaledWeylMajorant N M P m ≤ Q) :
    ‖weightedConvolutionProductSum (Finset.Ico a b) B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 *
        (Real.log (2 * B) * (U * V) * Q) := by
  apply norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_uniform
    (Finset.Ico a b) B U V hB N M 2 hQ
  intro sk hsk m hm
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hm
  have hmAdm := hadm sk hsk m hm
  exact (norm_typeIProductRestrictedInnerSum_Ico_le_quadraticWeyl
    N M hP hPa hbP ha hbB hmpos hM hmAdm.1 hmAdm.2.1 hmAdm.2.2).trans
      (hmajor sk hsk m hm)

/-- The first Vaughan Type I family, with logarithm in the inner variable, is
bounded by the explicit quadratic Weyl majorant through the formal finite Abel
summation callback. -/
theorem norm_weightedConvolutionProductVaughanTypeILogSum_le_quadraticWeyl
    (N M : ℝ) {P a b B U : ℕ}
    (hP : 0 < P) (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (ha : 0 < a) (hbB : b ≤ B) (hM : M ≠ 0)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hadm : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ)),
        TypeIQuadraticWeylAdmissible N M P m)
    (hmajor : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ)),
        2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
          typeIQuadraticRescaledWeylMajorant N M P m ≤ Q) :
    ‖weightedConvolutionProductSum (Finset.Ico a b) B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
        (vaughanTypeICoefficient U) log‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 * U * Q := by
  apply norm_weightedConvolutionProductVaughanTypeILogSum_le_uniform
    (Finset.Ico a b) B U N M 2 hQ
  intro sk hsk m hm
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hm
  have hmAdm := hadm sk hsk m hm
  exact (norm_typeIProductRestrictedLogInnerSum_Ico_le_quadraticWeyl
    N M hP hPa hab hbP ha hbB hmpos hM hmAdm.1 hmAdm.2.1 hmAdm.2.2).trans
      (hmajor sk hsk m hm)

/-! ## Exact Type I high/low analytic split -/

/-- The source Vinogradov envelope after the same literal Type I substitution
used by the Weyl branch.  The ambient logarithmic scale `Z` is deliberately
kept separate from the integer source interval scale `P`. -/
noncomputable def typeIQuadraticRescaledVinogradovMajorantAt
    (C Z A N M : ℝ) (P m : ℕ) : ℝ :=
  let D := P ⌈/⌉ m
  let N' := N / m
  let M' := M / (m : ℝ) ^ 2
  let F := reciprocalPhaseScale N' M' 2 D
  (2 * Real.log Z + 1) *
      (C * (Real.log Z) ^ (4 * A) * D * Real.exp
        (-((2 : ℝ) ^ (-18 : ℝ)) * (Real.log D) ^ 3 /
          (Real.log F) ^ 2)) +
    Real.log Z *
      (16 * D * (Real.log Z) ^ (-3 * A) + Real.log Z + 1)

theorem typeIQuadraticRescaledVinogradovMajorantAt_nonneg
    {C Z A N M : ℝ} {P m : ℕ}
    (hC : 0 ≤ C) (hlog : 0 ≤ Real.log Z) :
    0 ≤ typeIQuadraticRescaledVinogradovMajorantAt C Z A N M P m := by
  unfold typeIQuadraticRescaledVinogradovMajorantAt
  positivity

/-- The high-scale Vinogradov theorem on an arbitrary subinterval of the
rounded Type I dyadic fiber. -/
theorem norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticVinogradovAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N M : ℝ) {P m a b : ℕ}
    (hD : 2 ≤ P ⌈/⌉ m) (haD : P ⌈/⌉ m ≤ a)
    (hbD : b ≤ 2 * (P ⌈/⌉ m)) (hm : 0 < m) (hM : M ≠ 0)
    (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    (hcutoff :
      let D := P ⌈/⌉ m
      let N' := N / m
      let M' := M / (m : ℝ) ^ 2
      (((vinogradovDerivativeCutoff D
        (reciprocalPhaseScale N' M' 2 D) + 2 : ℕ) : ℝ)) ≤ Real.log Z)
    (hFhigh :
      let D := P ⌈/⌉ m
      let N' := N / m
      let M' := M / (m : ℝ) ^ 2
      (D : ℝ) ^ 4 ≤ reciprocalPhaseScale N' M' 2 D)
    (hsmall :
      let D := P ⌈/⌉ m
      let N' := N / m
      let M' := M / (m : ℝ) ^ 2
      Real.log ((Real.log Z) ^ (4 * A)) *
          (Real.log (reciprocalPhaseScale N' M' 2 D)) ^ 2 /
            (Real.log D) ^ 3 < (1 / 1000 : ℝ)) :
    ‖reciprocalPhaseSum (N / m) (M / (m : ℝ) ^ 2) 2 a b‖ ≤
      typeIQuadraticRescaledVinogradovMajorantAt C Z A N M P m := by
  let D := P ⌈/⌉ m
  let N' := N / m
  let M' := M / (m : ℝ) ^ 2
  have hM' : M' ≠ 0 := by
    unfold M'
    apply div_ne_zero hM
    exact pow_ne_zero 2 (by exact_mod_cast hm.ne')
  have hbound := norm_reciprocalPhaseSum_le_sourceVinogradov_logEnvelopeAt
    C hVinogradov N' M' Z A 2 a b (X := (D : ℝ)) (Y := (2 * D : ℕ))
      (by exact_mod_cast hD) hM' (by norm_num) hlog hA hten
      (by simpa only [D, N', M'] using hcutoff)
      (by simpa only [D, N', M'] using hFhigh)
      (by simpa only [D, N', M'] using hsmall)
      (by exact_mod_cast haD) (by exact_mod_cast hbD) (by norm_num)
      (by
        intro t ht
        simpa using ht.2)
  simpa only [typeIQuadraticRescaledVinogradovMajorantAt, D, N', M'] using hbound

/-- A single majorant for the exact low-scale Weyl / high-scale Vinogradov
dichotomy on a Type I fiber. -/
noncomputable def typeIQuadraticRescaledHybridMajorantAt
    (C Z A N M : ℝ) (P m : ℕ) : ℝ :=
  max (typeIQuadraticRescaledWeylMajorant N M P m)
    (typeIQuadraticRescaledVinogradovMajorantAt C Z A N M P m)

theorem typeIQuadraticRescaledHybridMajorantAt_nonneg
    {C Z A N M : ℝ} {P m : ℕ} (hD : 1 ≤ P ⌈/⌉ m) :
    0 ≤ typeIQuadraticRescaledHybridMajorantAt C Z A N M P m := by
  exact (typeIQuadraticRescaledWeylMajorant_nonneg N M hD).trans
    (le_max_left _ _)

/-- Exact admissibility disjunction for the Type I analytic split.  The
low-scale branch carries only the Weyl effective-error budget, while the
high-scale branch carries only the Vinogradov cutoff and smallness premises.
No hypothesis from the unused branch is imposed. -/
def TypeIQuadraticHybridAdmissible
    (Z A N M : ℝ) (P m : ℕ) : Prop :=
  let D := P ⌈/⌉ m
  let N' := N / m
  let M' := M / (m : ℝ) ^ 2
  10 ≤ D ∧
  ((reciprocalPhaseScale N' M' 2 D ≤ (D : ℝ) ^ 4 ∧
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale N' M' 2 D / (D : ℝ) ^ 5) +
        1 / 16 + 4 / reciprocalPhaseScale N' M' 2 D ≤ 1) ∨
    ((D : ℝ) ^ 4 ≤ reciprocalPhaseScale N' M' 2 D ∧
      ((((vinogradovDerivativeCutoff D
          (reciprocalPhaseScale N' M' 2 D) + 2 : ℕ) : ℝ)) ≤ Real.log Z) ∧
      Real.log ((Real.log Z) ^ (4 * A)) *
          (Real.log (reciprocalPhaseScale N' M' 2 D)) ^ 2 /
            (Real.log D) ^ 3 < (1 / 1000 : ℝ)))

/-- Exact arbitrary-subinterval Type I estimate, splitting internally between
the Weyl and Vinogradov regimes at the source threshold `F=D^4`. -/
theorem norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticHybridAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N M : ℝ) {P m a b : ℕ}
    (haD : P ⌈/⌉ m ≤ a) (hbD : b ≤ 2 * (P ⌈/⌉ m))
    (hm : 0 < m) (hM : M ≠ 0)
    (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    (hadm : TypeIQuadraticHybridAdmissible Z A N M P m) :
    ‖reciprocalPhaseSum (N / m) (M / (m : ℝ) ^ 2) 2 a b‖ ≤
      typeIQuadraticRescaledHybridMajorantAt C Z A N M P m := by
  let D := P ⌈/⌉ m
  let N' := N / m
  let M' := M / (m : ℝ) ^ 2
  have hM' : M' ≠ 0 := by
    unfold M'
    apply div_ne_zero hM
    exact pow_ne_zero 2 (by exact_mod_cast hm.ne')
  have hadm' : 10 ≤ D ∧
      ((reciprocalPhaseScale N' M' 2 D ≤ (D : ℝ) ^ 4 ∧
          240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
              (reciprocalPhaseScale N' M' 2 D / (D : ℝ) ^ 5) +
            1 / 16 + 4 / reciprocalPhaseScale N' M' 2 D ≤ 1) ∨
        ((D : ℝ) ^ 4 ≤ reciprocalPhaseScale N' M' 2 D ∧
          ((((vinogradovDerivativeCutoff D
              (reciprocalPhaseScale N' M' 2 D) + 2 : ℕ) : ℝ)) ≤ Real.log Z) ∧
          Real.log ((Real.log Z) ^ (4 * A)) *
              (Real.log (reciprocalPhaseScale N' M' 2 D)) ^ 2 /
                (Real.log D) ^ 3 < (1 / 1000 : ℝ))) := by
    simpa only [TypeIQuadraticHybridAdmissible, D, N', M'] using hadm
  rcases hadm'.2 with hlow | hhigh
  · have hweyl :=
      norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticWeylSource
        N' M' typeIQuadraticWeylOrders hadm'.1 haD hbD hM' hlow.1 hlow.2
          five_mem_typeIQuadraticWeylOrders six_mem_typeIQuadraticWeylOrders
    have hweyl' :
        ‖reciprocalPhaseSum (N / m) (M / (m : ℝ) ^ 2) 2 a b‖ ≤
          typeIQuadraticRescaledWeylMajorant N M P m := by
      simpa only [typeIQuadraticRescaledWeylMajorant, D, N', M'] using hweyl
    exact hweyl'.trans (le_max_left _ _)
  · have hvin := norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticVinogradovAt
      C hVinogradov Z A N M (P := P) (m := m) (a := a) (b := b)
        (by omega) haD hbD hm hM hlog hA hten hhigh.2.1
        (by simpa only [D, N', M'] using hhigh.1) hhigh.2.2
    exact hvin.trans (le_max_right _ _)

/-- Literal unweighted Type I inner estimate with the analytic high/low split
performed internally. -/
theorem norm_typeIProductRestrictedInnerSum_Ico_le_quadraticHybridAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N M : ℝ) {P a b B m : ℕ}
    (hPa : P ≤ a) (hbP : b ≤ 2 * P) (ha : 0 < a) (hbB : b ≤ B)
    (hm : 0 < m) (hM : M ≠ 0)
    (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    (hadm : TypeIQuadraticHybridAdmissible Z A N M P m) :
    ‖typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B) (fun _ => 1) N M 2 m‖ ≤
      typeIQuadraticRescaledHybridMajorantAt C Z A N M P m := by
  rw [typeIProductRestrictedInnerSum_Ico_eq ha hbB hm]
  have hgeom := typeI_ceilDiv_dyadic_geometry hm hPa hbP
  exact norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticHybridAt
    C hVinogradov Z A N M hgeom.1 hgeom.2 hm hM hlog hA hten hadm

/-- Literal logarithmically weighted Type I inner estimate with uniform
high/low control of every Abel prefix. -/
theorem norm_typeIProductRestrictedLogInnerSum_Ico_le_quadraticHybridAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N M : ℝ) {P a b B m : ℕ}
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (ha : 0 < a) (hbB : b ≤ B) (hm : 0 < m) (hM : M ≠ 0)
    (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    (hadm : TypeIQuadraticHybridAdmissible Z A N M P m) :
    ‖typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B)
        (fun n => (Real.log n : ℂ)) N M 2 m‖ ≤
      2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
        typeIQuadraticRescaledHybridMajorantAt C Z A N M P m := by
  have hgeom := typeI_ceilDiv_dyadic_geometry hm hPa hbP
  have hDten : 10 ≤ P ⌈/⌉ m := by
    have h := hadm.1
    simpa only [TypeIQuadraticHybridAdmissible] using h
  have hR : 0 ≤ typeIQuadraticRescaledHybridMajorantAt C Z A N M P m :=
    typeIQuadraticRescaledHybridMajorantAt_nonneg (by omega)
  by_cases hceil : a ⌈/⌉ m < b ⌈/⌉ m
  · apply norm_typeIProductRestrictedLogInnerSum_Ico_le
      ha hbB hm N M 2 hceil hR
    intro k hak hkb
    exact norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticHybridAt
      C hVinogradov Z A N M hgeom.1 (hkb.trans hgeom.2) hm hM
        hlog hA hten hadm
  · have hle : b ⌈/⌉ m ≤ a ⌈/⌉ m := Nat.le_of_not_gt hceil
    have hIco : Finset.Ico (a ⌈/⌉ m) (b ⌈/⌉ m) = ∅ :=
      Finset.Ico_eq_empty (Nat.not_lt.mpr hle)
    rw [typeIProductRestrictedLogInnerSum_Ico_eq ha hbB hm]
    simp only [hIco, Finset.sum_empty, norm_zero]
    have hbpos : 0 < b := ha.trans_le hab
    have hceilPos : 0 < b ⌈/⌉ m := typeI_ceilDiv_pos hbpos hm
    have hlogb : 0 ≤ Real.log ((b ⌈/⌉ m : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hceilPos)
    positivity

/-- Complete second Vaughan Type I family with the exact analytic high/low
split performed independently on every active outer fiber. -/
theorem norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_quadraticHybridAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N M : ℝ) {P a b B U V : ℕ}
    (hPa : P ≤ a) (hbP : b ≤ 2 * P) (ha : 0 < a) (hbB : b ≤ B)
    (hB : 0 < B) (hM : M ≠ 0)
    (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hadm : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
        TypeIQuadraticHybridAdmissible Z A N M P m)
    (hmajor : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeIPrimeCoefficient U V m : ℂ)),
        typeIQuadraticRescaledHybridMajorantAt C Z A N M P m ≤ Q) :
    ‖weightedConvolutionProductSum (Finset.Ico a b) B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
        (vaughanTypeIPrimeCoefficient U V) (ζ : ArithmeticFunction ℝ)‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 *
        (Real.log (2 * B) * (U * V) * Q) := by
  apply norm_weightedConvolutionProductVaughanTypeIPrimeSum_le_uniform
    (Finset.Ico a b) B U V hB N M 2 hQ
  intro sk hsk m hm
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hm
  exact (norm_typeIProductRestrictedInnerSum_Ico_le_quadraticHybridAt
    C hVinogradov Z A N M hPa hbP ha hbB hmpos hM hlog hA hten
      (hadm sk hsk m hm)).trans (hmajor sk hsk m hm)

/-- Complete first Vaughan Type I family with the exact hybrid estimate on
every active outer fiber and finite Abel summation in the inner variable. -/
theorem norm_weightedConvolutionProductVaughanTypeILogSum_le_quadraticHybridAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N M : ℝ) {P a b B U : ℕ}
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (ha : 0 < a) (hbB : b ≤ B) (hM : M ≠ 0)
    (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    {Q : ℝ} (hQ : 0 ≤ Q)
    (hadm : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ)),
        TypeIQuadraticHybridAdmissible Z A N M P m)
    (hmajor : ∀ sk ∈ vaughanShortIntervalIndexBox B,
      ∀ m ∈ vaughanTypeIActiveProductBlockSupport B sk
        (fun m => (vaughanTypeICoefficient U m : ℂ)),
        2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
          typeIQuadraticRescaledHybridMajorantAt C Z A N M P m ≤ Q) :
    ‖weightedConvolutionProductSum (Finset.Ico a b) B
        (fun n => standardAdditiveCharacter (reciprocalPhase N M 2 n))
        (vaughanTypeICoefficient U) log‖ ≤
      (Nat.log 2 B + 1 : ℕ) ^ 102 * U * Q := by
  apply norm_weightedConvolutionProductVaughanTypeILogSum_le_uniform
    (Finset.Ico a b) B U N M 2 hQ
  intro sk hsk m hm
  have hmpos : 0 < m := pos_of_mem_vaughanTypeIActiveProductBlockSupport hm
  exact (norm_typeIProductRestrictedLogInnerSum_Ico_le_quadraticHybridAt
    C hVinogradov Z A N M hPa hab hbP ha hbB hmpos hM hlog hA hten
      (hadm sk hsk m hm)).trans (hmajor sk hsk m hm)

/-- Under the source exponential parameter bound and a fixed positive-power
lower bound for the rounded fiber scale, every high-scale Type I fiber
automatically satisfies the Vinogradov cutoff and smallness conditions.
Consequently only the low-scale Weyl budget remains as a branch-local
hypothesis. -/
theorem eventually_typeIQuadraticHybridAdmissible_of_parameterBound
    {A C c ε : ℝ} (hA : 1 / 4 ≤ A) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, ∀ (N M : ℝ) (P m : ℕ),
      10 ≤ P ⌈/⌉ m →
      reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
          ((P ⌈/⌉ m : ℕ) : ℝ) ≤
        C * Real.exp ((Real.log Z) ^ (3 / 2 - ε)) →
      c * Real.log Z ≤ Real.log ((P ⌈/⌉ m : ℕ) : ℝ) →
      (reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
          ((P ⌈/⌉ m : ℕ) : ℝ) ≤
          ((P ⌈/⌉ m : ℕ) : ℝ) ^ 4 →
        240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
                ((P ⌈/⌉ m : ℕ) : ℝ) /
              ((P ⌈/⌉ m : ℕ) : ℝ) ^ 5) +
          1 / 16 +
            4 / reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
              ((P ⌈/⌉ m : ℕ) : ℝ) ≤ 1) →
      TypeIQuadraticHybridAdmissible Z A N M P m := by
  have hparameters :=
    eventually_sourceVinogradov_quadraticParameterConditions_of_parameterBound
      hA hC hc hε ha
  filter_upwards [hparameters] with Z hparametersZ
  intro N M P m hD hupper hlower hbudget
  let D := P ⌈/⌉ m
  let N' := N / m
  let M' := M / (m : ℝ) ^ 2
  let F := reciprocalPhaseScale N' M' 2 D
  have hDreal : (2 : ℝ) ≤ D := by exact_mod_cast (by omega : 2 ≤ D)
  have hupper' : F ≤ C * Real.exp ((Real.log Z) ^ (3 / 2 - ε)) := by
    simpa only [D, N', M', F] using hupper
  have hlower' : c * Real.log Z ≤ Real.log (D : ℝ) := by
    simpa only [D] using hlower
  unfold TypeIQuadraticHybridAdmissible
  dsimp only
  refine ⟨hD, ?_⟩
  by_cases hlow : F ≤ (D : ℝ) ^ 4
  · left
    refine ⟨by simpa only [D, N', M', F] using hlow, ?_⟩
    apply hbudget
    simpa only [D, N', M', F] using hlow
  · right
    have hhigh : (D : ℝ) ^ 4 ≤ F := le_of_lt (lt_of_not_ge hlow)
    obtain ⟨_hlog, _hten, hcutoff, hsmall⟩ :=
      hparametersZ (D : ℝ) F hDreal hhigh hupper' hlower'
    exact ⟨by simpa only [D, N', M', F] using hhigh,
      by simpa only [D, N', M', F] using hcutoff,
      by simpa only [D, N', M', F] using hsmall⟩

/-! ## Branch-sensitive Type I majorant -/

/-- The source-faithful Type I envelope chooses only the majorant belonging
to the actual phase-scale branch.  Unlike the earlier `max` envelope, this
does not retain the unused Weyl expression on a high-scale fiber. -/
noncomputable def typeIQuadraticRescaledBranchMajorantAt
    (C Z A N M : ℝ) (P m : ℕ) : ℝ :=
  let D := P ⌈/⌉ m
  let N' := N / m
  let M' := M / (m : ℝ) ^ 2
  let F := reciprocalPhaseScale N' M' 2 D
  if F ≤ (D : ℝ) ^ 4 then
    typeIQuadraticRescaledWeylMajorant N M P m
  else
    typeIQuadraticRescaledVinogradovMajorantAt C Z A N M P m

theorem typeIQuadraticRescaledBranchMajorantAt_nonneg
    {C Z A N M : ℝ} {P m : ℕ}
    (hC : 0 ≤ C) (hlog : 0 ≤ Real.log Z) (hD : 1 ≤ P ⌈/⌉ m) :
    0 ≤ typeIQuadraticRescaledBranchMajorantAt C Z A N M P m := by
  unfold typeIQuadraticRescaledBranchMajorantAt
  dsimp only
  split
  · exact typeIQuadraticRescaledWeylMajorant_nonneg N M hD
  · exact typeIQuadraticRescaledVinogradovMajorantAt_nonneg hC hlog

/-- Absolute coefficient in the rescaled ten-block quadratic Weyl
majorant, after fixing the derivative orders to `{5,6}` and extracting the
rounded fiber length and its logarithm. -/
noncomputable def typeIQuadraticWeylConstant : ℝ :=
  20 * ((370 * 2 + 173 : ℕ) : ℝ) *
    (480 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
      (((((5 + 2) ^ 5 : ℕ) : ℝ)) + 1))

theorem typeIQuadraticRescaledWeylMajorant_eq
    (N M : ℝ) (P m : ℕ) :
    typeIQuadraticRescaledWeylMajorant N M P m =
      typeIQuadraticWeylConstant * (P ⌈/⌉ m : ℕ) *
        (1 + Real.log ((P ⌈/⌉ m : ℕ) : ℝ)) *
        typeIQuadraticWeylSourceWidth
          (N / m) (M / (m : ℝ) ^ 2) (P ⌈/⌉ m) := by
  simp only [typeIQuadraticRescaledWeylMajorant,
    typeIQuadraticWeylUniformBlockMajorant,
    typeIQuadraticWeylConstant, card_typeIQuadraticWeylOrders]
  push_cast
  ring

/-- A low-scale phase upper bound and any positive phase lower bound give a
two-term source-width envelope with no hidden constants. -/
theorem typeIQuadraticWeylSourceWidth_le_of_bounds
    (N M : ℝ) {D : ℕ} {H : ℝ}
    (hD : (0 : ℝ) < D) (hH : 0 < H)
    (hlow : reciprocalPhaseScale N M 2 D ≤ (D : ℝ) ^ 4)
    (hHscale : H ≤ reciprocalPhaseScale N M 2 D) :
    typeIQuadraticWeylSourceWidth N M D ≤
      (1 / (D : ℝ) + 4 / H) ^ (1 / 1024 : ℝ) := by
  have hfirst : reciprocalPhaseScale N M 2 D / (D : ℝ) ^ 5 ≤
      1 / (D : ℝ) :=
    div_pow_five_le_one_div_of_le_pow_four hD hlow
  have hinverse : 4 / reciprocalPhaseScale N M 2 D ≤ 4 / H :=
    div_le_div_of_nonneg_left (by norm_num) hH hHscale
  have hscale : 0 < reciprocalPhaseScale N M 2 D := hH.trans_le hHscale
  have hinside : 0 ≤
      reciprocalPhaseScale N M 2 D / (D : ℝ) ^ 5 +
        4 / reciprocalPhaseScale N M 2 D := by
    positivity
  unfold typeIQuadraticWeylSourceWidth
  apply Real.rpow_le_rpow
  · exact hinside
  · exact add_le_add hfirst hinverse
  · norm_num

/-- The high branch is already exactly the normalized source Vinogradov
envelope.  Its existing asymptotic theorem therefore gives arbitrary
logarithmic saving proportional to the rounded fiber length. -/
theorem eventually_typeIQuadraticRescaledVinogradovMajorantAt_le
    {C₀ C₁ c ε A T : ℝ} (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hc : 0 < c) (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε)
    (hAT : T + 2 ≤ 3 * A) :
    ∀ᶠ Z : ℝ in Filter.atTop, ∀ (N M : ℝ) (P m : ℕ),
      2 ≤ P ⌈/⌉ m →
      ((P ⌈/⌉ m : ℕ) : ℝ) ^ 4 ≤
        reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
          ((P ⌈/⌉ m : ℕ) : ℝ) →
      reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
          ((P ⌈/⌉ m : ℕ) : ℝ) ≤
        C₀ * Real.exp ((Real.log Z) ^ (3 / 2 - ε)) →
      c * Real.log Z ≤ Real.log ((P ⌈/⌉ m : ℕ) : ℝ) →
      typeIQuadraticRescaledVinogradovMajorantAt C₁ Z A N M P m ≤
        3 * (P ⌈/⌉ m : ℕ) * (Real.log Z) ^ (-T) := by
  have henvelope := eventually_sourceVinogradov_logEnvelope_le
    hC₀ hC₁ hc hε ha hAT
  filter_upwards [henvelope] with Z henvelopeZ
  intro N M P m hD hhigh hupper hlower
  have h := henvelopeZ
    ((P ⌈/⌉ m : ℕ) : ℝ)
    (reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
      ((P ⌈/⌉ m : ℕ) : ℝ))
    (by exact_mod_cast hD) hhigh hupper hlower
  simpa only [typeIQuadraticRescaledVinogradovMajorantAt] using h

/-- Arbitrary-subinterval hybrid estimate with a branch-sensitive output.
The extra implication supplies the low Weyl budget even in the equality case,
where the admissibility disjunction itself may have been witnessed by the
high branch. -/
theorem norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticBranchAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N M : ℝ) {P m a b : ℕ}
    (haD : P ⌈/⌉ m ≤ a) (hbD : b ≤ 2 * (P ⌈/⌉ m))
    (hm : 0 < m) (hM : M ≠ 0)
    (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    (hadm : TypeIQuadraticHybridAdmissible Z A N M P m)
    (hbudget :
      let D := P ⌈/⌉ m
      let N' := N / m
      let M' := M / (m : ℝ) ^ 2
      reciprocalPhaseScale N' M' 2 D ≤ (D : ℝ) ^ 4 →
        240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (reciprocalPhaseScale N' M' 2 D / (D : ℝ) ^ 5) +
          1 / 16 + 4 / reciprocalPhaseScale N' M' 2 D ≤ 1) :
    ‖reciprocalPhaseSum (N / m) (M / (m : ℝ) ^ 2) 2 a b‖ ≤
      typeIQuadraticRescaledBranchMajorantAt C Z A N M P m := by
  let D := P ⌈/⌉ m
  let N' := N / m
  let M' := M / (m : ℝ) ^ 2
  let F := reciprocalPhaseScale N' M' 2 D
  have hadm' : 10 ≤ D ∧
      ((F ≤ (D : ℝ) ^ 4 ∧
          240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
              (F / (D : ℝ) ^ 5) + 1 / 16 + 4 / F ≤ 1) ∨
        ((D : ℝ) ^ 4 ≤ F ∧
          ((((vinogradovDerivativeCutoff D F + 2 : ℕ) : ℝ)) ≤
              Real.log Z) ∧
          Real.log ((Real.log Z) ^ (4 * A)) * (Real.log F) ^ 2 /
              (Real.log D) ^ 3 < (1 / 1000 : ℝ))) := by
    simpa only [TypeIQuadraticHybridAdmissible, D, N', M', F] using hadm
  by_cases hlow : F ≤ (D : ℝ) ^ 4
  · have hweyl :=
      norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticWeylSource
        N' M' typeIQuadraticWeylOrders hadm'.1 haD hbD
          (by
            unfold M'
            apply div_ne_zero hM
            exact pow_ne_zero 2 (by exact_mod_cast hm.ne'))
          hlow (by simpa only [D, N', M', F] using hbudget hlow)
          five_mem_typeIQuadraticWeylOrders six_mem_typeIQuadraticWeylOrders
    have hweyl' :
        ‖reciprocalPhaseSum (N / m) (M / (m : ℝ) ^ 2) 2 a b‖ ≤
          typeIQuadraticRescaledWeylMajorant N M P m := by
      simpa only [typeIQuadraticRescaledWeylMajorant, D, N', M'] using hweyl
    simpa only [typeIQuadraticRescaledBranchMajorantAt, D, N', M', F,
      if_pos hlow] using hweyl'
  · have hhigh : (D : ℝ) ^ 4 ≤ F ∧
        ((((vinogradovDerivativeCutoff D F + 2 : ℕ) : ℝ)) ≤
            Real.log Z) ∧
        Real.log ((Real.log Z) ^ (4 * A)) * (Real.log F) ^ 2 /
            (Real.log D) ^ 3 < (1 / 1000 : ℝ) := by
      rcases hadm'.2 with hbad | hgood
      · exact False.elim (hlow hbad.1)
      · exact hgood
    have hvin := norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticVinogradovAt
      C hVinogradov Z A N M (P := P) (m := m) (a := a) (b := b)
        (by omega) haD hbD hm hM hlog hA hten
        (by simpa only [D, N', M', F] using hhigh.2.1)
        (by simpa only [D, N', M', F] using hhigh.1)
        (by simpa only [D, N', M', F] using hhigh.2.2)
    simpa only [typeIQuadraticRescaledBranchMajorantAt, D, N', M', F,
      if_neg hlow] using hvin

/-- Literal unweighted Type I fiber estimate with the branch-sensitive
majorant. -/
theorem norm_typeIProductRestrictedInnerSum_Ico_le_quadraticBranchAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N M : ℝ) {P a b B m : ℕ}
    (hPa : P ≤ a) (hbP : b ≤ 2 * P) (ha : 0 < a) (hbB : b ≤ B)
    (hm : 0 < m) (hM : M ≠ 0)
    (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    (hadm : TypeIQuadraticHybridAdmissible Z A N M P m)
    (hbudget :
      let D := P ⌈/⌉ m
      let N' := N / m
      let M' := M / (m : ℝ) ^ 2
      reciprocalPhaseScale N' M' 2 D ≤ (D : ℝ) ^ 4 →
        240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (reciprocalPhaseScale N' M' 2 D / (D : ℝ) ^ 5) +
          1 / 16 + 4 / reciprocalPhaseScale N' M' 2 D ≤ 1) :
    ‖typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B) (fun _ => 1) N M 2 m‖ ≤
      typeIQuadraticRescaledBranchMajorantAt C Z A N M P m := by
  rw [typeIProductRestrictedInnerSum_Ico_eq ha hbB hm]
  have hgeom := typeI_ceilDiv_dyadic_geometry hm hPa hbP
  exact norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticBranchAt
    C hVinogradov Z A N M hgeom.1 hgeom.2 hm hM hlog hA hten hadm hbudget

/-- Logarithmically weighted Type I fiber estimate with every Abel prefix
controlled by the branch-sensitive majorant. -/
theorem norm_typeIProductRestrictedLogInnerSum_Ico_le_quadraticBranchAt
    (C : ℝ) (hVinogradov : VinogradovExponentialSumEstimateAt C)
    (Z A N M : ℝ) {P a b B m : ℕ}
    (hPa : P ≤ a) (hab : a ≤ b) (hbP : b ≤ 2 * P)
    (ha : 0 < a) (hbB : b ≤ B) (hm : 0 < m) (hM : M ≠ 0)
    (hC : 0 ≤ C) (hlog : 1 ≤ Real.log Z) (hA : 1 / 4 ≤ A)
    (hten : 10 ≤ (Real.log Z) ^ A)
    (hadm : TypeIQuadraticHybridAdmissible Z A N M P m)
    (hbudget :
      let D := P ⌈/⌉ m
      let N' := N / m
      let M' := M / (m : ℝ) ^ 2
      reciprocalPhaseScale N' M' 2 D ≤ (D : ℝ) ^ 4 →
        240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
            (reciprocalPhaseScale N' M' 2 D / (D : ℝ) ^ 5) +
          1 / 16 + 4 / reciprocalPhaseScale N' M' 2 D ≤ 1) :
    ‖typeIProductRestrictedWeightedInnerSum
        (Finset.Ico a b) (Finset.Ioc 0 B)
        (fun n => (Real.log n : ℂ)) N M 2 m‖ ≤
      2 * Real.log ((b ⌈/⌉ m : ℕ) : ℝ) *
        typeIQuadraticRescaledBranchMajorantAt C Z A N M P m := by
  have hgeom := typeI_ceilDiv_dyadic_geometry hm hPa hbP
  have hDten : 10 ≤ P ⌈/⌉ m := by
    have h := hadm.1
    simpa only [TypeIQuadraticHybridAdmissible] using h
  have hR : 0 ≤ typeIQuadraticRescaledBranchMajorantAt C Z A N M P m :=
    typeIQuadraticRescaledBranchMajorantAt_nonneg hC (by linarith) (by omega)
  by_cases hceil : a ⌈/⌉ m < b ⌈/⌉ m
  · apply norm_typeIProductRestrictedLogInnerSum_Ico_le
      ha hbB hm N M 2 hceil hR
    intro k hak hkb
    exact norm_reciprocalPhaseSum_subinterval_le_typeIQuadraticBranchAt
      C hVinogradov Z A N M hgeom.1 (hkb.trans hgeom.2) hm hM
        hlog hA hten hadm hbudget
  · have hle : b ⌈/⌉ m ≤ a ⌈/⌉ m := Nat.le_of_not_gt hceil
    have hIco : Finset.Ico (a ⌈/⌉ m) (b ⌈/⌉ m) = ∅ :=
      Finset.Ico_eq_empty (Nat.not_lt.mpr hle)
    rw [typeIProductRestrictedLogInnerSum_Ico_eq ha hbB hm]
    simp only [hIco, Finset.sum_empty, norm_zero]
    have hbpos : 0 < b := ha.trans_le hab
    have hceilPos : 0 < b ⌈/⌉ m := typeI_ceilDiv_pos hbpos hm
    have hlogb : 0 ≤ Real.log ((b ⌈/⌉ m : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hceilPos)
    positivity

/-! ## Automatic low-scale Weyl budget -/

/-- Ceiling rounding costs at most a factor two when the divisor does not
exceed the numerator. -/
theorem ceilDiv_cast_le_two_mul_div
    {P m : ℕ} (hm : 0 < m) (hmP : m ≤ P) :
    ((P ⌈/⌉ m : ℕ) : ℝ) ≤ 2 * (P : ℝ) / m := by
  have hmul : (P ⌈/⌉ m) * m ≤ 2 * P := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    have hbase := Nat.div_mul_le_self (P + m - 1) m
    omega
  rw [le_div_iff₀ (by exact_mod_cast hm : (0 : ℝ) < m)]
  exact_mod_cast hmul

/-- The source reciprocal-phase scale is at most four times its value at the
ceiling-rounded rescaled Type I scale. -/
theorem reciprocalPhaseScale_le_four_mul_typeI_rescale_ceilDiv
    (N M : ℝ) {P m : ℕ} (hP : 0 < P) (hm : 0 < m) (hmP : m ≤ P) :
    reciprocalPhaseScale N M 2 P ≤
      4 * reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
        ((P ⌈/⌉ m : ℕ) : ℝ) := by
  have hX : (0 : ℝ) < (P : ℝ) / m := div_pos (by exact_mod_cast hP) (by exact_mod_cast hm)
  have hDposNat : 0 < P ⌈/⌉ m := typeI_ceilDiv_pos hP hm
  have hDpos : (0 : ℝ) < (P ⌈/⌉ m : ℕ) := by exact_mod_cast hDposNat
  have htop : ((P ⌈/⌉ m : ℕ) : ℝ) ≤ 2 * ((P : ℝ) / m) := by
    simpa only [mul_div_assoc] using ceilDiv_cast_le_two_mul_div hm hmP
  have hcompare := reciprocalPhaseScale_quadratic_le_four_mul_of_le_two_mul
    (N / m) (M / (m : ℝ) ^ 2) hX hDpos htop
  rw [← reciprocalPhaseScale_rescale N M P 2 m (by exact_mod_cast hP.ne') hm]
  exact hcompare

/-- Source-frequency growth and the factor-four ceiling comparison give the
concrete logarithmic low-branch width used in the final Type I ledger. -/
theorem typeIQuadraticWeylSourceWidth_le_of_sourceLogScale
    (N M Z d : ℝ) {P m : ℕ}
    (hP : 0 < P) (hm : 0 < m) (hmP : m ≤ P)
    (hlogpow : 0 < (Real.log Z) ^ d)
    (hsource : (Real.log Z) ^ d ≤ reciprocalPhaseScale N M 2 P)
    (hlow : reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
        ((P ⌈/⌉ m : ℕ) : ℝ) ≤
      ((P ⌈/⌉ m : ℕ) : ℝ) ^ 4) :
    typeIQuadraticWeylSourceWidth
        (N / m) (M / (m : ℝ) ^ 2) (P ⌈/⌉ m) ≤
      (1 / ((P ⌈/⌉ m : ℕ) : ℝ) +
        16 / (Real.log Z) ^ d) ^ (1 / 1024 : ℝ) := by
  have hDposNat : 0 < P ⌈/⌉ m := typeI_ceilDiv_pos hP hm
  have hDpos : (0 : ℝ) < (P ⌈/⌉ m : ℕ) := by exact_mod_cast hDposNat
  have hcompare := reciprocalPhaseScale_le_four_mul_typeI_rescale_ceilDiv
    N M hP hm hmP
  have hlower : (Real.log Z) ^ d / 4 ≤
      reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
        ((P ⌈/⌉ m : ℕ) : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
    simpa only [mul_comm] using hsource.trans hcompare
  have hbase := typeIQuadraticWeylSourceWidth_le_of_bounds
    (N / m) (M / (m : ℝ) ^ 2) hDpos
      (div_pos hlogpow (by norm_num)) hlow hlower
  convert hbase using 1
  congr 2
  field_simp [ne_of_gt hlogpow]
  norm_num

/-- A completely explicit numerical criterion for the quadratic four-step
Weyl budget. The constant is twice the coefficient of the degree-five term;
the lower scale `16` controls the inverse term. -/
theorem quadraticWeylBudget_of_lowScale
    {F D : ℝ} (hD : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ D)
    (hF : 16 ≤ F) (hlow : F ≤ D ^ 4) :
    240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) * (F / D ^ 5) +
        1 / 16 + 4 / F ≤ 1 := by
  have hDpos : 0 < D := by positivity
  have hFpos : 0 < F := by positivity
  have hnormalized : F / D ^ 5 ≤ 1 / D :=
    div_pow_five_le_one_div_of_le_pow_four hDpos hlow
  have hcoefficient :
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) * (1 / D) ≤ 1 / 2 := by
    calc
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) * (1 / D) =
          (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) / D := by ring
      _ ≤ 1 / 2 := (div_le_iff₀ hDpos).2 (by
        norm_num at hD ⊢
        linarith)
  have hfirst :
      240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) * (F / D ^ 5) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left hnormalized (by positivity)).trans hcoefficient
  have hinverse : 4 / F ≤ 1 / 4 := by
    rw [div_le_iff₀ hFpos]
    nlinarith
  nlinarith

/-- Source-scale lower growth and ceiling geometry automatically discharge
the low-branch effective-error budget. -/
theorem typeIQuadraticWeylBudget_of_sourceScale
    (N M : ℝ) {P m : ℕ} (hP : 0 < P) (hm : 0 < m) (hmP : m ≤ P)
    (hD : 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ (P ⌈/⌉ m : ℕ))
    (hsource : 64 ≤ reciprocalPhaseScale N M 2 P)
    (hlow : reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
        ((P ⌈/⌉ m : ℕ) : ℝ) ≤
      ((P ⌈/⌉ m : ℕ) : ℝ) ^ 4) :
    240 * ((((5 + 2) ^ 5 : ℕ) : ℝ)) *
          (reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
              ((P ⌈/⌉ m : ℕ) : ℝ) /
            ((P ⌈/⌉ m : ℕ) : ℝ) ^ 5) +
        1 / 16 +
          4 / reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
            ((P ⌈/⌉ m : ℕ) : ℝ) ≤ 1 := by
  have hcompare := reciprocalPhaseScale_le_four_mul_typeI_rescale_ceilDiv
    N M hP hm hmP
  have hlocal : 16 ≤
      reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
        ((P ⌈/⌉ m : ℕ) : ℝ) := by
    linarith
  exact quadraticWeylBudget_of_lowScale hD hlocal hlow

/-- Fully automatic hybrid admissibility under concrete source bounds.  The
high branch uses the eventual Vinogradov parameter package; the low branch
uses `typeIQuadraticWeylBudget_of_sourceScale`. -/
theorem eventually_typeIQuadraticHybridAdmissible_of_sourceBounds
    {A C c ε : ℝ} (hA : 1 / 4 ≤ A) (hC : 0 < C) (hc : 0 < c)
    (hε : 0 < ε) (ha : 0 ≤ 3 / 2 - ε) :
    ∀ᶠ Z : ℝ in Filter.atTop, ∀ (N M : ℝ) (P m : ℕ),
      0 < P → 0 < m → m ≤ P →
      2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) ≤ (P ⌈/⌉ m : ℕ) →
      64 ≤ reciprocalPhaseScale N M 2 P →
      reciprocalPhaseScale (N / m) (M / (m : ℝ) ^ 2) 2
          ((P ⌈/⌉ m : ℕ) : ℝ) ≤
        C * Real.exp ((Real.log Z) ^ (3 / 2 - ε)) →
      c * Real.log Z ≤ Real.log ((P ⌈/⌉ m : ℕ) : ℝ) →
      TypeIQuadraticHybridAdmissible Z A N M P m := by
  have hadm := eventually_typeIQuadraticHybridAdmissible_of_parameterBound
    hA hC hc hε ha
  filter_upwards [hadm] with Z hadmZ
  intro N M P m hP hm hmP hD hsource hupper hlower
  apply hadmZ N M P m (by
    have : (10 : ℝ) ≤ 2 * (240 * ((((5 + 2) ^ 5 : ℕ) : ℝ))) := by norm_num
    exact_mod_cast this.trans hD) hupper hlower
  intro hlow
  exact typeIQuadraticWeylBudget_of_sourceScale
    N M hP hm hmP hD hsource hlow

end

end Tao2026
