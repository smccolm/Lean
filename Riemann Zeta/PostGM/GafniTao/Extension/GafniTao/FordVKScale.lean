import GafniTao.FordSingleZeroCotangentBound
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The physical Vinogradov--Korobov detector scale

The contour radius is written exponentially in the variable
`u = log log t`.  This makes the two balancing identities exact while the
public zero-free width continues to use the source denominator from
`VinogradovKorobov`.
-/

open Filter

namespace GafniTao

noncomputable section

noncomputable def fordVKLogLog (t : ℝ) : ℝ :=
  Real.log (Real.log t)

noncomputable def fordVKRadius (t : ℝ) : ℝ :=
  Real.exp ((2 / 3 : ℝ) *
    (Real.log (fordVKLogLog t) - fordVKLogLog t))

theorem fordVKRadius_pos (t : ℝ) : 0 < fordVKRadius t := by
  unfold fordVKRadius
  positivity

theorem tendsto_fordVKLogLog_atTop :
    Tendsto fordVKLogLog atTop atTop := by
  exact Real.tendsto_log_atTop.comp Real.tendsto_log_atTop

theorem fordVKRadius_mul_denominator
    {t : ℝ} (ht : Real.exp (Real.exp 1) ≤ t) :
    fordVKRadius t * vinogradovKorobovDenominator t =
      fordVKLogLog t := by
  have htPos : 0 < t := (Real.exp_pos _).trans_le ht
  have hlogLower : Real.exp 1 ≤ Real.log t := by
    simpa using Real.strictMonoOn_log.monotoneOn
      (Real.exp_pos _) htPos ht
  have hlogPos : 0 < Real.log t := (Real.exp_pos 1).trans_le hlogLower
  have hU : 0 < Real.log (Real.log t) :=
    Real.log_pos ((show (1 : ℝ) < Real.exp 1 by
      exact one_lt_two.trans Real.exp_one_gt_two).trans_le hlogLower)
  let u : ℝ := Real.log (Real.log t)
  have hu : 0 < u := by simpa [u] using hU
  change Real.exp ((2 / 3 : ℝ) * (Real.log u - u)) *
      (Real.log t ^ (2 / 3 : ℝ) * u ^ (1 / 3 : ℝ)) = u
  rw [Real.rpow_def_of_pos hlogPos, Real.rpow_def_of_pos hu]
  rw [← Real.exp_add, ← Real.exp_add]
  rw [show Real.log (Real.log t) = u by rfl]
  convert Real.exp_log hu using 1
  ring_nf

theorem fordVKRadius_rpow_three_halves_mul_log
    {t : ℝ} (ht : Real.exp (Real.exp 1) ≤ t) :
    fordVKRadius t ^ (3 / 2 : ℝ) * Real.log t =
      fordVKLogLog t := by
  have htPos : 0 < t := (Real.exp_pos _).trans_le ht
  have hlogLower : Real.exp 1 ≤ Real.log t := by
    simpa using Real.strictMonoOn_log.monotoneOn
      (Real.exp_pos _) htPos ht
  have hlogPos : 0 < Real.log t := (Real.exp_pos 1).trans_le hlogLower
  have hU : 0 < Real.log (Real.log t) :=
    Real.log_pos ((show (1 : ℝ) < Real.exp 1 by
      exact one_lt_two.trans Real.exp_one_gt_two).trans_le hlogLower)
  let u : ℝ := Real.log (Real.log t)
  have hu : 0 < u := by simpa [u] using hU
  change (Real.exp ((2 / 3 : ℝ) * (Real.log u - u))) ^
      (3 / 2 : ℝ) * Real.log t = u
  rw [Real.rpow_def_of_pos (Real.exp_pos _) , Real.log_exp]
  rw [show Real.log t = Real.exp u by
    dsimp [u]
    rw [Real.exp_log hlogPos]]
  rw [← Real.exp_add]
  convert Real.exp_log hu using 1
  ring_nf

theorem log_fordVKRadius (t : ℝ) :
    Real.log (fordVKRadius t) =
      (2 / 3 : ℝ) * (Real.log (fordVKLogLog t) - fordVKLogLog t) := by
  unfold fordVKRadius
  rw [Real.log_exp]

/-- Eventually the balancing radius is small, while `log log t` is large
enough to absorb every fixed constant used later. -/
theorem eventually_fordVK_scale_data :
    ∀ᶠ t : ℝ in atTop,
      Real.exp (Real.exp 1) ≤ t ∧
      9 ≤ fordVKLogLog t ∧
      2 * Real.log (fordVKLogLog t) ≤ fordVKLogLog t ∧
      fordVKRadius t ≤ 1 / 8 := by
  have hbase : ∀ᶠ t : ℝ in atTop,
      Real.exp (Real.exp 1) ≤ t := eventually_ge_atTop _
  have hu9 := tendsto_fordVKLogLog_atTop.eventually
    (eventually_ge_atTop (9 : ℝ))
  have hlogSmallU : ∀ᶠ u : ℝ in atTop, 2 * Real.log u ≤ u := by
    have hLittle := Real.isLittleO_log_id_atTop.const_mul_left (2 : ℝ)
    filter_upwards [hLittle.eventuallyLE, eventually_ge_atTop (1 : ℝ)]
      with u hu hOne
    have huNonneg : 0 ≤ u := by linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hOne),
      abs_of_nonneg huNonneg] using hu
  have hlogSmall := tendsto_fordVKLogLog_atTop.eventually hlogSmallU
  filter_upwards [hbase, hu9, hlogSmall] with t ht hu hlog
  refine ⟨ht, hu, hlog, ?_⟩
  have hexponent :
      (2 / 3 : ℝ) *
          (Real.log (fordVKLogLog t) - fordVKLogLog t) ≤ -3 := by
    linarith
  have hexp := Real.exp_le_exp.mpr hexponent
  have hnegOne : Real.exp (-1) < 1 / 2 := Real.exp_neg_one_lt_half
  have hnegThree : Real.exp (-3) < 1 / 8 := by
    rw [show (-3 : ℝ) = -1 + -1 + -1 by ring, Real.exp_add,
      Real.exp_add]
    nlinarith [Real.exp_pos (-1)]
  unfold fordVKRadius
  exact hexp.trans hnegThree.le

/-- Multiplying the height by a factor between one and four changes the
source denominator by at most a factor four.  This coarse constant is enough
for the three auxiliary frequencies and keeps all logarithms literal. -/
theorem vinogradovKorobovDenominator_mul_le_four
    {t q : ℝ} (ht : 100 ≤ t) (hu : 9 ≤ fordVKLogLog t)
    (hqOne : 1 ≤ q) (hqFour : q ≤ 4) :
    vinogradovKorobovDenominator (q * t) ≤
      4 * vinogradovKorobovDenominator t := by
  have htPos : 0 < t := by linarith
  have hqPos : 0 < q := zero_lt_one.trans_le hqOne
  have hqtPos : 0 < q * t := mul_pos hqPos htPos
  have hqt : q * t ≤ t ^ 2 := by
    have hqt' : q * t ≤ t * t := by nlinarith
    simpa [pow_two] using hqt'
  have hlogtPos : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogqtPos : 0 < Real.log (q * t) := Real.log_pos (by nlinarith)
  have honeLogqt : 1 ≤ Real.log (q * t) := by
    have hexp : Real.exp 1 ≤ q * t := by
      exact Real.exp_one_lt_three.le.trans (by nlinarith)
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hexp
  have hlog : Real.log (q * t) ≤ 2 * Real.log t := by
    calc
      Real.log (q * t) ≤ Real.log (t ^ 2) :=
        Real.strictMonoOn_log.monotoneOn hqtPos (sq_pos_of_pos htPos) hqt
      _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
  have huPos : 0 < Real.log (Real.log t) := by
    change 0 < fordVKLogLog t
    linarith
  have hloglog : Real.log (Real.log (q * t)) ≤
      2 * Real.log (Real.log t) := by
    have hmono : Real.log (Real.log (q * t)) ≤
        Real.log (2 * Real.log t) :=
      Real.strictMonoOn_log.monotoneOn hlogqtPos
        (mul_pos two_pos hlogtPos) hlog
    have hlogTwo : Real.log 2 ≤ 1 := by
      exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans_eq
        (by norm_num)
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogtPos.ne'] at hmono
    change 9 ≤ Real.log (Real.log t) at hu
    linarith
  have hfirst := Real.rpow_le_rpow hlogqtPos.le hlog (by norm_num :
    (0 : ℝ) ≤ 2 / 3)
  have hsecond := Real.rpow_le_rpow (Real.log_nonneg honeLogqt)
    hloglog (by norm_num : (0 : ℝ) ≤ 1 / 3)
  have htwo23 : (2 : ℝ) ^ (2 / 3 : ℝ) ≤ 2 := by
    exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have htwo13 : (2 : ℝ) ^ (1 / 3 : ℝ) ≤ 2 := by
    exact Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  unfold vinogradovKorobovDenominator
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hlogtPos.le] at hfirst
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) huPos.le] at hsecond
  have hbaseFirst : 0 ≤ Real.log t ^ (2 / 3 : ℝ) :=
    Real.rpow_nonneg hlogtPos.le _
  have hbaseSecond : 0 ≤ Real.log (Real.log t) ^ (1 / 3 : ℝ) :=
    Real.rpow_nonneg huPos.le _
  calc
    Real.log (q * t) ^ (2 / 3 : ℝ) *
        Real.log (Real.log (q * t)) ^ (1 / 3 : ℝ) ≤
      ((2 : ℝ) ^ (2 / 3 : ℝ) *
          Real.log t ^ (2 / 3 : ℝ)) *
        ((2 : ℝ) ^ (1 / 3 : ℝ) *
          Real.log (Real.log t) ^ (1 / 3 : ℝ)) :=
      mul_le_mul hfirst hsecond
        (Real.rpow_nonneg (Real.log_nonneg honeLogqt) _)
        (mul_nonneg (Real.rpow_nonneg (by norm_num) _) hbaseFirst)
    _ ≤ (2 * Real.log t ^ (2 / 3 : ℝ)) *
        (2 * Real.log (Real.log t) ^ (1 / 3 : ℝ)) := by
      gcongr
    _ = 4 * (Real.log t ^ (2 / 3 : ℝ) *
        Real.log (Real.log t) ^ (1 / 3 : ℝ)) := by ring

#print axioms fordVKRadius_mul_denominator
#print axioms fordVKRadius_rpow_three_halves_mul_log
#print axioms eventually_fordVK_scale_data
#print axioms vinogradovKorobovDenominator_mul_le_four

end

end GafniTao
