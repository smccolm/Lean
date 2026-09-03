import GafniTao.PintzUniformError

/-!
# Elementary bounds for Pintz's moving Möbius cutoff

All ceiling, logarithm, harmonic-number, and dyadic-cover losses associated
with `ceil(exp(lambda+3))` are kept explicit here.
-/

namespace GafniTao

open RiemannZeta.GuthMaynard

noncomputable section

theorem pintzMobiusCutoff_cast_lt_two_exp
    {lambda : ℝ} (hlambda : -3 ≤ lambda) :
    (pintzMobiusCutoff lambda : ℝ) < 2 * Real.exp (lambda + 3) := by
  have hexpOne : 1 ≤ Real.exp (lambda + 3) := Real.one_le_exp (by linarith)
  have hceil : (pintzMobiusCutoff lambda : ℝ) <
      Real.exp (lambda + 3) + 1 := by
    exact Nat.ceil_lt_add_one (Real.exp_pos _).le
  linarith

theorem pintzMobiusCutoff_log_le
    {lambda : ℝ} (hlambda : -3 ≤ lambda) :
    Real.log (pintzMobiusCutoff lambda) ≤ lambda + 4 := by
  have hcutoffPos : (0 : ℝ) < pintzMobiusCutoff lambda := by
    exact_mod_cast pintzMobiusCutoff_one_le lambda
  have hupperPos : 0 < 2 * Real.exp (lambda + 3) := by positivity
  have hlogStrict : Real.log (pintzMobiusCutoff lambda) <
      Real.log (2 * Real.exp (lambda + 3)) :=
    Real.strictMonoOn_log (Set.mem_Ioi.mpr hcutoffPos)
      (Set.mem_Ioi.mpr hupperPos) (pintzMobiusCutoff_cast_lt_two_exp hlambda)
  have hlogProduct : Real.log (2 * Real.exp (lambda + 3)) =
      Real.log 2 + (lambda + 3) := by
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (Real.exp_ne_zero (lambda + 3)), Real.log_exp]
  rw [hlogProduct] at hlogStrict
  linarith [Real.log_two_lt_d9]

theorem pintzMobiusCutoff_harmonic_le
    {lambda : ℝ} (hlambda : -3 ≤ lambda) :
    (harmonic (pintzMobiusCutoff lambda) : ℝ) ≤ lambda + 5 := by
  have hraw := harmonic_le_one_add_log (pintzMobiusCutoff lambda)
  have hlog := pintzMobiusCutoff_log_le hlambda
  exact hraw.trans (by linarith)

theorem pintzMobiusCutoff_clog_le
    {lambda : ℝ} (hlambda : -3 ≤ lambda) :
    (Nat.clog 2 (pintzMobiusCutoff lambda) : ℝ) ≤
      1 + (lambda + 4) / Real.log 2 := by
  have hraw := natCast_clog_two_le_one_add_log
    (pintzMobiusCutoff lambda) (pintzMobiusCutoff_one_le lambda)
  have hlog := pintzMobiusCutoff_log_le hlambda
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv := div_le_div_of_nonneg_right hlog hlogTwo.le
  exact hraw.trans (by simpa [add_comm] using add_le_add_left hdiv 1)

theorem pintzMobiusCutoff_rpow_le
    {lambda a : ℝ} (hlambda : -3 ≤ lambda) (ha : 0 ≤ a) :
    (pintzMobiusCutoff lambda : ℝ) ^ a ≤
      (2 * Real.exp (lambda + 3)) ^ a := by
  exact Real.rpow_le_rpow (Nat.cast_nonneg _)
    (pintzMobiusCutoff_cast_lt_two_exp hlambda).le ha

#print axioms pintzMobiusCutoff_cast_lt_two_exp
#print axioms pintzMobiusCutoff_log_le
#print axioms pintzMobiusCutoff_harmonic_le
#print axioms pintzMobiusCutoff_clog_le
#print axioms pintzMobiusCutoff_rpow_le

end

end GafniTao
