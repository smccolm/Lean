import Tao2026.SmoothNumberSaddleHTSmallBetaWidth
import GafniTao.FordVKScale

/-!
# Absorption scale for the small-beta origin residue

At the HT frequency ceiling, the contour shift times the VK denominator
times one additional `log log` factor is

`2 * (log y)^(-epsilon/6) *
  (((3/2-epsilon) * log log y)^(4/3))`.

It tends to zero for every fixed positive `epsilon`.  Consequently a
variable-disk logarithmic-derivative estimate with a residual `log log`
factor is still absorbed by the `1 / beta` term throughout
`beta <= 2 * contourShift`; an exact coefficient-free `O(D)` theorem is not
needed for the HT application.
-/

open Filter Topology Set Complex

namespace Tao2026

noncomputable section

/-- Exact iterated logarithm at the source frequency ceiling. -/
theorem fordVKLogLog_smoothSaddleHTFrequencyCeiling
    {y : ℕ} (hy : 2 ≤ y) (epsilon : ℝ) :
    GafniTao.fordVKLogLog (smoothSaddleHTFrequencyCeiling y epsilon) =
      (3 / 2 - epsilon) * Real.log (Real.log y) := by
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  unfold GafniTao.fordVKLogLog smoothSaddleHTFrequencyCeiling
  rw [Real.log_exp, Real.log_rpow hlog]

/-- Exact product governing a possible extra `log log` loss in the
high-height origin-residue estimate. -/
theorem smoothSaddleHTContourShift_mul_vkDenominator_mul_logLog
    {y : ℕ} (hy : 3 ≤ y) {epsilon : ℝ}
    (hEpsilon : epsilon < 3 / 2) :
    smoothSaddleHTContourShift y epsilon *
        GafniTao.vinogradovKorobovDenominator
          (smoothSaddleHTFrequencyCeiling y epsilon) *
        GafniTao.fordVKLogLog
          (smoothSaddleHTFrequencyCeiling y epsilon) =
      2 * (Real.log y) ^ (-epsilon / 6) *
        (((3 / 2 - epsilon) * Real.log (Real.log y)) ^
          (4 / 3 : ℝ)) := by
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have ha : 0 < 3 / 2 - epsilon := by linarith
  have hloglog : 0 < Real.log (Real.log y) := by
    have hlogOne : 1 < Real.log (y : ℝ) := by
      rw [Real.lt_log_iff_exp_lt (by positivity : (0 : ℝ) < y)]
      exact Real.exp_one_lt_three.trans_le (by exact_mod_cast hy)
    exact Real.log_pos hlogOne
  have hu : 0 < (3 / 2 - epsilon) * Real.log (Real.log y) :=
    mul_pos ha hloglog
  rw [smoothSaddleHTContourShift_mul_vinogradovKorobovDenominator
      (by omega : 2 ≤ y) hEpsilon,
    fordVKLogLog_smoothSaddleHTFrequencyCeiling (by omega : 2 ≤ y) epsilon]
  rw [show (4 / 3 : ℝ) = (1 / 3 : ℝ) + 1 by ring,
    Real.rpow_add hu, Real.rpow_one]
  ring

/-- A fixed positive power of `log y` absorbs the fourth-third power of
`log log y`. -/
theorem eventually_sixteen_mul_smoothSaddleHTVKLogLogFactor_le
    {c epsilon : ℝ} (hc : 0 < c)
    (hEpsilon : 0 < epsilon) (hEpsilonOne : epsilon < 1) :
    ∀ᶠ x : ℝ in atTop,
      16 * x ^ (-epsilon / 6) *
          (((3 / 2 - epsilon) * Real.log x) ^ (4 / 3 : ℝ)) ≤ c := by
  have ha : 0 < 3 / 2 - epsilon := by linarith
  have hp : 0 < epsilon / 6 := by positivity
  have hsmall :=
    (isLittleO_log_rpow_rpow_atTop (4 / 3 : ℝ) hp).const_mul_left
      (16 * (3 / 2 - epsilon) ^ (4 / 3 : ℝ))
  have hbound := hsmall.bound hc
  filter_upwards [hbound, eventually_ge_atTop (Real.exp 1)] with x hx hbase
  have hxPos : 0 < x := (Real.exp_pos 1).trans_le hbase
  have hlogOne : 1 ≤ Real.log x := by
    simpa only [Real.log_exp] using
      Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hxPos hbase
  have hlogNonneg : 0 ≤ Real.log x := zero_le_one.trans hlogOne
  have haPow : 0 ≤ (3 / 2 - epsilon) ^ (4 / 3 : ℝ) :=
    Real.rpow_nonneg ha.le _
  have hlogPow : 0 ≤ Real.log x ^ (4 / 3 : ℝ) :=
    Real.rpow_nonneg hlogNonneg _
  have hxPow : 0 < x ^ (epsilon / 6) := Real.rpow_pos_of_pos hxPos _
  rw [Real.norm_of_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) haPow) hlogPow),
    Real.norm_eq_abs, abs_of_pos hxPow] at hx
  rw [Real.mul_rpow ha.le hlogNonneg]
  rw [show -epsilon / 6 = -(epsilon / 6) by ring,
    Real.rpow_neg hxPos.le]
  calc
    16 * (x ^ (epsilon / 6))⁻¹ *
          ((3 / 2 - epsilon) ^ (4 / 3 : ℝ) *
            Real.log x ^ (4 / 3 : ℝ)) =
        (16 * (3 / 2 - epsilon) ^ (4 / 3 : ℝ) *
          Real.log x ^ (4 / 3 : ℝ)) / x ^ (epsilon / 6) := by ring
    _ ≤ c := (div_le_iff₀ hxPow).2 (by simpa [mul_assoc] using hx)

/-- At the source ceiling, even eight copies of the shift-denominator-
`log log` product are eventually bounded by any prescribed positive
coefficient. -/
theorem eventually_eight_mul_smoothSaddleHTContourShift_mul_vk_logLog_le
    {c epsilon : ℝ} (hc : 0 < c)
    (hEpsilon : 0 < epsilon) (hEpsilonOne : epsilon < 1) :
    ∀ᶠ y : ℕ in atTop,
      8 * (smoothSaddleHTContourShift y epsilon *
        GafniTao.vinogradovKorobovDenominator
          (smoothSaddleHTFrequencyCeiling y epsilon) *
        GafniTao.fordVKLogLog
          (smoothSaddleHTFrequencyCeiling y epsilon)) ≤ c := by
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hbound := hlogTop.eventually
    (eventually_sixteen_mul_smoothSaddleHTVKLogLogFactor_le
      hc hEpsilon hEpsilonOne)
  filter_upwards [hbound, eventually_ge_atTop (3 : ℕ)] with y hbound hy
  rw [smoothSaddleHTContourShift_mul_vkDenominator_mul_logLog
    hy (by linarith : epsilon < 3 / 2)]
  ring_nf at hbound ⊢
  exact hbound

/-- Multiplication of a sufficiently large height by a factor in `[1,4]`
costs at most a factor two in `log log`. -/
theorem fordVKLogLog_mul_le_two
    {T q : ℝ} (hT : 100 ≤ T) (hU : 9 ≤ GafniTao.fordVKLogLog T)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4) :
    GafniTao.fordVKLogLog (q * T) ≤
      2 * GafniTao.fordVKLogLog T := by
  have hTPos : 0 < T := by linarith
  have hqPos : 0 < q := zero_lt_one.trans_le hqOne
  have hqTPos : 0 < q * T := mul_pos hqPos hTPos
  have hqT : q * T ≤ T ^ 2 := by
    have hqT' : q * T ≤ T * T := by nlinarith
    simpa [pow_two] using hqT'
  have hlogTPos : 0 < Real.log T := Real.log_pos (by linarith)
  have hlogqTPos : 0 < Real.log (q * T) := Real.log_pos (by nlinarith)
  have hlog : Real.log (q * T) ≤ 2 * Real.log T := by
    calc
      Real.log (q * T) ≤ Real.log (T ^ 2) :=
        Real.strictMonoOn_log.monotoneOn hqTPos (sq_pos_of_pos hTPos) hqT
      _ = 2 * Real.log T := by rw [Real.log_pow]; norm_num
  have hmono : Real.log (Real.log (q * T)) ≤
      Real.log (2 * Real.log T) :=
    Real.strictMonoOn_log.monotoneOn hlogqTPos
      (mul_pos two_pos hlogTPos) hlog
  have hlogTwo : Real.log 2 ≤ 1 :=
    (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans_eq
      (by norm_num)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogTPos.ne'] at hmono
  change Real.log (Real.log (q * T)) ≤
    2 * Real.log (Real.log T)
  change 9 ≤ Real.log (Real.log T) at hU
  linarith

/-- Uniform actual-height form of the extra-`log log` absorption. -/
theorem eventually_smoothSaddleHTContourShift_mul_vk_actualHeight_logLog_le
    {c epsilon : ℝ} (hc : 0 < c)
    (hEpsilon : 0 < epsilon) (hEpsilonOne : epsilon < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ t : ℝ,
      |t| ≤ smoothSaddleHTFrequencyCeiling y epsilon →
      smoothSaddleHTContourShift y epsilon *
          GafniTao.vinogradovKorobovDenominator
            (|t| + smoothSaddleHTContourHeight y epsilon) *
          GafniTao.fordVKLogLog
            (|t| + smoothSaddleHTContourHeight y epsilon) ≤ c := by
  have ha : 0 < 3 / 2 - epsilon := by linarith
  have hlogTop : Tendsto (fun y : ℕ => Real.log (y : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hYTop : Tendsto
      (fun y : ℕ => smoothSaddleHTFrequencyCeiling y epsilon)
      atTop atTop := by
    simpa only [smoothSaddleHTFrequencyCeiling] using
      Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop ha).comp hlogTop)
  have hUTop : Tendsto
      (fun y : ℕ => GafniTao.fordVKLogLog
        (smoothSaddleHTFrequencyCeiling y epsilon)) atTop atTop :=
    GafniTao.tendsto_fordVKLogLog_atTop.comp hYTop
  filter_upwards
      [eventually_eight_mul_smoothSaddleHTContourShift_mul_vk_logLog_le
        hc hEpsilon hEpsilonOne,
      hYTop.eventually (eventually_ge_atTop (100 : ℝ)),
      hYTop.eventually
        (eventually_ge_atTop (Real.exp (Real.exp 1))),
      hUTop.eventually (eventually_ge_atTop (9 : ℝ)),
      eventually_ge_atTop (3 : ℕ)] with y hceiling hY100 hYBase hU9 hy
  intro t ht
  let Y : ℝ := smoothSaddleHTFrequencyCeiling y epsilon
  let A : ℝ := |t| + smoothSaddleHTContourHeight y epsilon
  have hYPos : 0 < Y := by
    dsimp [Y]
    exact smoothSaddleHTFrequencyCeiling_pos y epsilon
  have hAPos : 0 < A := by
    dsimp [A, smoothSaddleHTContourHeight]
    nlinarith [abs_nonneg t]
  have hAUpper : A ≤ 3 * Y := by
    dsimp [A, Y]
    exact smoothSaddleHT_totalHeight_le ht
  have hABase : Real.exp (Real.exp 1) ≤ A := by
    dsimp [A, smoothSaddleHTContourHeight, Y] at hYBase ⊢
    nlinarith [abs_nonneg t]
  have hthreeBase : Real.exp (Real.exp 1) ≤ 3 * Y :=
    hABase.trans hAUpper
  have hExpOneBase : Real.exp 1 ≤ Real.exp (Real.exp 1) := by
    exact Real.exp_le_exp.mpr
      (one_le_two.trans Real.exp_one_gt_two.le)
  have hAExpOne : Real.exp 1 ≤ A := hExpOneBase.trans hABase
  have hthreeExpOne : Real.exp 1 ≤ 3 * Y := hAExpOne.trans hAUpper
  have hDMono : GafniTao.vinogradovKorobovDenominator A ≤
      GafniTao.vinogradovKorobovDenominator (3 * Y) :=
    GafniTao.monotoneOn_vinogradovKorobovDenominator
      hAExpOne hthreeExpOne hAUpper
  have hDThree : GafniTao.vinogradovKorobovDenominator (3 * Y) ≤
      4 * GafniTao.vinogradovKorobovDenominator Y := by
    exact GafniTao.vinogradovKorobovDenominator_mul_le_four
      hY100 hU9 (q := (3 : ℝ)) (by norm_num) (by norm_num)
  have hD : GafniTao.vinogradovKorobovDenominator A ≤
      4 * GafniTao.vinogradovKorobovDenominator Y :=
    hDMono.trans hDThree
  have hUALe : GafniTao.fordVKLogLog A ≤
      GafniTao.fordVKLogLog (3 * Y) := by
    unfold GafniTao.fordVKLogLog
    apply Real.strictMonoOn_log.monotoneOn
    · exact Real.log_pos ((show (1 : ℝ) < Real.exp (Real.exp 1) by
        exact Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hABase)
    · exact Real.log_pos ((show (1 : ℝ) < Real.exp (Real.exp 1) by
        exact Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hthreeBase)
    · exact Real.strictMonoOn_log.monotoneOn hAPos
        (mul_pos (by norm_num) hYPos) hAUpper
  have hUThree : GafniTao.fordVKLogLog (3 * Y) ≤
      2 * GafniTao.fordVKLogLog Y :=
    fordVKLogLog_mul_le_two hY100 hU9 (q := (3 : ℝ))
      (by norm_num) (by norm_num)
  have hU : GafniTao.fordVKLogLog A ≤
      2 * GafniTao.fordVKLogLog Y := hUALe.trans hUThree
  have hshift : 0 ≤ smoothSaddleHTContourShift y epsilon :=
    (smoothSaddleHTContourShift_pos (by omega : 2 ≤ y) epsilon).le
  have hDA : 0 ≤ GafniTao.vinogradovKorobovDenominator A :=
    (GafniTao.vinogradovKorobovDenominator_pos hABase).le
  have hDY : 0 ≤ GafniTao.vinogradovKorobovDenominator Y :=
    (GafniTao.vinogradovKorobovDenominator_pos hYBase).le
  have hUA : 0 ≤ GafniTao.fordVKLogLog A := by
    unfold GafniTao.fordVKLogLog
    exact Real.log_nonneg (by
      have : Real.exp 1 ≤ Real.log A := by
        simpa using Real.strictMonoOn_log.monotoneOn
          (Real.exp_pos _) hAPos hABase
      exact one_le_two.trans Real.exp_one_gt_two.le |>.trans this)
  calc
    smoothSaddleHTContourShift y epsilon *
          GafniTao.vinogradovKorobovDenominator A *
          GafniTao.fordVKLogLog A ≤
        smoothSaddleHTContourShift y epsilon *
          (4 * GafniTao.vinogradovKorobovDenominator Y) *
          GafniTao.fordVKLogLog A :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hD hshift) hUA
    _ ≤ smoothSaddleHTContourShift y epsilon *
          (4 * GafniTao.vinogradovKorobovDenominator Y) *
          (2 * GafniTao.fordVKLogLog Y) :=
      mul_le_mul_of_nonneg_left hU (mul_nonneg hshift (by positivity))
    _ = 8 * (smoothSaddleHTContourShift y epsilon *
          GafniTao.vinogradovKorobovDenominator Y *
          GafniTao.fordVKLogLog Y) := by ring
    _ ≤ c := by simpa [Y] using hceiling

/-- In the small-beta range, the complete actual-height VK denominator with
one residual `log log` factor is absorbed by the source pole scale
`1 / beta`. -/
theorem eventually_vk_actualHeight_mul_logLog_le_div_beta
    {c epsilon : ℝ} (hc : 0 < c)
    (hEpsilon : 0 < epsilon) (hEpsilonOne : epsilon < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ beta t : ℝ,
      0 < beta →
      beta ≤ 2 * smoothSaddleHTContourShift y epsilon →
      |t| ≤ smoothSaddleHTFrequencyCeiling y epsilon →
      GafniTao.vinogradovKorobovDenominator
          (|t| + smoothSaddleHTContourHeight y epsilon) *
        GafniTao.fordVKLogLog
          (|t| + smoothSaddleHTContourHeight y epsilon) ≤ c / beta := by
  have hcHalf : 0 < c / 2 := by positivity
  filter_upwards
      [eventually_smoothSaddleHTContourShift_mul_vk_actualHeight_logLog_le
        hcHalf hEpsilon hEpsilonOne,
      eventually_smoothSaddleHT_native_contourHeight
        (H := Real.exp (Real.exp 1)) hEpsilonOne] with y hscale hbase
  intro beta t hbeta hbetaUpper ht
  let A : ℝ := |t| + smoothSaddleHTContourHeight y epsilon
  have hABase : Real.exp (Real.exp 1) ≤ A := by
    simpa [A] using hbase t
  have hU : 0 ≤ GafniTao.fordVKLogLog A := by
    unfold GafniTao.fordVKLogLog
    have hlogLower : Real.exp 1 ≤ Real.log A := by
      simpa using Real.strictMonoOn_log.monotoneOn
        (Real.exp_pos _) ((Real.exp_pos _).trans_le hABase) hABase
    exact Real.log_nonneg
      (one_le_two.trans Real.exp_one_gt_two.le |>.trans hlogLower)
  have hD : 0 ≤ GafniTao.vinogradovKorobovDenominator A := by
    unfold GafniTao.vinogradovKorobovDenominator
    exact mul_nonneg
      (Real.rpow_nonneg
        (Real.log_pos ((show (1 : ℝ) < Real.exp (Real.exp 1) by
          exact Real.one_lt_exp_iff.mpr (Real.exp_pos 1)).trans_le hABase)).le _)
      (Real.rpow_nonneg hU _)
  have hDU : 0 ≤ GafniTao.vinogradovKorobovDenominator A *
      GafniTao.fordVKLogLog A := mul_nonneg hD hU
  rw [le_div_iff₀ hbeta]
  calc
    GafniTao.vinogradovKorobovDenominator A *
          GafniTao.fordVKLogLog A * beta =
        beta * (GafniTao.vinogradovKorobovDenominator A *
          GafniTao.fordVKLogLog A) := by ring
    _ ≤ (2 * smoothSaddleHTContourShift y epsilon) *
          (GafniTao.vinogradovKorobovDenominator A *
            GafniTao.fordVKLogLog A) :=
      mul_le_mul_of_nonneg_right hbetaUpper hDU
    _ = 2 * (smoothSaddleHTContourShift y epsilon *
          GafniTao.vinogradovKorobovDenominator A *
          GafniTao.fordVKLogLog A) := by ring
    _ ≤ c := by
      have := hscale t ht
      dsimp [A] at this ⊢
      linarith

/-- Any fixed multiple of the variable-disk majorant
`D(actualHeight) * log log(actualHeight) + 1 / beta` collapses to twice that
multiple of the source pole scale in the small-beta branch. -/
theorem eventually_smoothSaddleHT_variableDiskMajorant_le_two_mul_div_beta
    {K epsilon : ℝ} (hK : 0 ≤ K)
    (hEpsilon : 0 < epsilon) (hEpsilonOne : epsilon < 1) :
    ∀ᶠ y : ℕ in atTop, ∀ beta t : ℝ,
      0 < beta →
      beta ≤ 2 * smoothSaddleHTContourShift y epsilon →
      |t| ≤ smoothSaddleHTFrequencyCeiling y epsilon →
      K * (GafniTao.vinogradovKorobovDenominator
            (|t| + smoothSaddleHTContourHeight y epsilon) *
          GafniTao.fordVKLogLog
            (|t| + smoothSaddleHTContourHeight y epsilon) +
          1 / beta) ≤ 2 * K / beta := by
  filter_upwards
      [eventually_vk_actualHeight_mul_logLog_le_div_beta
        (c := (1 : ℝ)) (by norm_num) hEpsilon hEpsilonOne] with y hy
  intro beta t hbeta hbetaUpper ht
  have hDU := hy beta t hbeta hbetaUpper ht
  calc
    K * (GafniTao.vinogradovKorobovDenominator
            (|t| + smoothSaddleHTContourHeight y epsilon) *
          GafniTao.fordVKLogLog
            (|t| + smoothSaddleHTContourHeight y epsilon) +
          1 / beta) ≤ K * (1 / beta + 1 / beta) :=
      mul_le_mul_of_nonneg_left (add_le_add hDU le_rfl) hK
    _ = 2 * K / beta := by ring

end

end Tao2026
