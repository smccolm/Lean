import GafniTao.HeathBrownCriticalExponents

/-!
# Quantitative logarithmic absorption in Heath-Brown's Lemma 1

The source writes powers of `log N` as `N^epsilon`.  Here the loss is
budgeted explicitly: half of the requested epsilon absorbs the logarithm,
and the remaining half absorbs the `H^epsilon` loss from the critical VMVT.
-/

namespace GafniTao

noncomputable section

noncomputable def heathBrownLogConstant (epsilon : ℝ) : ℝ :=
  1 + 2 / epsilon

theorem heathBrownLogConstant_pos
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    0 < heathBrownLogConstant epsilon := by
  unfold heathBrownLogConstant
  positivity

theorem heathBrown_one_add_log_le
    {N : ℕ} {epsilon : ℝ}
    (hN : 1 ≤ N) (hepsilon : 0 < epsilon) :
    1 + Real.log (N : ℝ) ≤
      heathBrownLogConstant epsilon *
        (N : ℝ) ^ (epsilon / 2) := by
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hhalf : 0 < epsilon / 2 := by positivity
  have hone : (1 : ℝ) ≤ (N : ℝ) ^ (epsilon / 2) :=
    Real.one_le_rpow hNReal hhalf.le
  have hlog := Real.log_le_rpow_div
    (show (0 : ℝ) ≤ N by positivity) hhalf
  calc
    1 + Real.log (N : ℝ) ≤
        (N : ℝ) ^ (epsilon / 2) +
          (N : ℝ) ^ (epsilon / 2) / (epsilon / 2) :=
      add_le_add hone hlog
    _ = heathBrownLogConstant epsilon *
          (N : ℝ) ^ (epsilon / 2) := by
      unfold heathBrownLogConstant
      field_simp

/-- Raising the logarithmic loss to any exponent in `[0,1]` costs at most
the same `N^(epsilon/2)` budget. -/
theorem heathBrown_one_add_log_rpow_le
    {N : ℕ} {epsilon r : ℝ}
    (hN : 1 ≤ N) (hepsilon : 0 < epsilon)
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    (1 + Real.log (N : ℝ)) ^ r ≤
      (heathBrownLogConstant epsilon) ^ r *
        (N : ℝ) ^ (epsilon / 2) := by
  have hNReal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hbase : 0 ≤ 1 + Real.log (N : ℝ) := by
    have := Real.log_nonneg hNReal
    linarith
  have hmain := Real.rpow_le_rpow hbase
    (heathBrown_one_add_log_le hN hepsilon) hr0
  have hconstant : 0 ≤ heathBrownLogConstant epsilon :=
    (heathBrownLogConstant_pos hepsilon).le
  rw [Real.mul_rpow hconstant (by positivity)] at hmain
  have hexponent : epsilon / 2 * r ≤ epsilon / 2 := by
    nlinarith
  have hpower :
      ((N : ℝ) ^ (epsilon / 2)) ^ r ≤
        (N : ℝ) ^ (epsilon / 2) := by
    rw [← Real.rpow_mul (show (0 : ℝ) ≤ N by positivity)]
    exact Real.rpow_le_rpow_of_exponent_le hNReal hexponent
  exact hmain.trans (mul_le_mul_of_nonneg_left hpower (by positivity))

#print axioms heathBrownLogConstant_pos
#print axioms heathBrown_one_add_log_le
#print axioms heathBrown_one_add_log_rpow_le

end

end GafniTao
