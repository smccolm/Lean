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
      6 ≤ fordVKLogLog t ∧
      2 * Real.log (fordVKLogLog t) ≤ fordVKLogLog t ∧
      fordVKRadius t ≤ 1 / 4 := by
  have hbase : ∀ᶠ t : ℝ in atTop,
      Real.exp (Real.exp 1) ≤ t := eventually_ge_atTop _
  have hu6 := tendsto_fordVKLogLog_atTop.eventually
    (eventually_ge_atTop (6 : ℝ))
  have hlogSmallU : ∀ᶠ u : ℝ in atTop, 2 * Real.log u ≤ u := by
    have hLittle := Real.isLittleO_log_id_atTop.const_mul_left (2 : ℝ)
    filter_upwards [hLittle.eventuallyLE, eventually_ge_atTop (1 : ℝ)]
      with u hu hOne
    have huNonneg : 0 ≤ u := by linarith
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hOne),
      abs_of_nonneg huNonneg] using hu
  have hlogSmall := tendsto_fordVKLogLog_atTop.eventually hlogSmallU
  filter_upwards [hbase, hu6, hlogSmall] with t ht hu hlog
  refine ⟨ht, hu, hlog, ?_⟩
  have hexponent :
      (2 / 3 : ℝ) *
          (Real.log (fordVKLogLog t) - fordVKLogLog t) ≤ -2 := by
    linarith
  have hexp := Real.exp_le_exp.mpr hexponent
  have hnegOne : Real.exp (-1) < 1 / 2 := Real.exp_neg_one_lt_half
  have hnegTwo : Real.exp (-2) < 1 / 4 := by
    rw [show (-2 : ℝ) = -1 + -1 by ring, Real.exp_add]
    nlinarith [Real.exp_pos (-1)]
  unfold fordVKRadius
  exact hexp.trans hnegTwo.le

#print axioms fordVKRadius_mul_denominator
#print axioms fordVKRadius_rpow_three_halves_mul_log
#print axioms eventually_fordVK_scale_data

end

end GafniTao
