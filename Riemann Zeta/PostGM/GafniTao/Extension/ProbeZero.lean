import GafniTao.FordKZeroSeries

open scoped Topology

set_option maxHeartbeats 800000 in

example : Summable (fun n : ℕ =>
    Real.log ((n : ℝ) + 2) / (n : ℝ) ^ 2) := by
  have hp : Summable (fun n : ℕ => 4 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    by
      simpa [div_eq_mul_inv] using
        (Real.summable_one_div_nat_rpow.mpr
          (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 4
  refine Summable.of_norm_bounded_eventually hp ?_
  rw [Nat.cofinite_eq_atTop]
  refine Filter.eventually_atTop.2 ⟨2, ?_⟩
  intro n hnNat
  have hnReal : (2 : ℝ) ≤ n := by exact_mod_cast hnNat
  have hlogNonneg : 0 ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by linarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hlogNonneg (by positivity))]
  ·
    have hn : (0 : ℝ) < n + 2 := by positivity
    have hlog := Real.log_le_rpow_div (show (0 : ℝ) ≤ n + 2 by positivity)
      (show (0 : ℝ) < 1 / 2 by norm_num)
    have hden : (0 : ℝ) < (n + 2) ^ 2 := by positivity
    have hcomp : (n : ℝ) + 2 ≤ 2 * (n : ℝ) := by linarith
    have hnpos : (0 : ℝ) < n := by linarith
    have hpow : ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤
        2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
      calc
        ((n : ℝ) + 2) ^ (1 / 2 : ℝ) ≤
            (2 * (n : ℝ)) ^ (1 / 2 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hcomp (by norm_num)
        _ = 2 ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
          rw [Real.mul_rpow (by norm_num) hnpos.le]
        _ ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hnpos.le _)
          calc
            (2 : ℝ) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
            _ = 2 := by norm_num
    calc
      Real.log ((n : ℝ) + 2) / (n : ℝ) ^ 2 ≤
          (2 * ((n : ℝ) + 2) ^ (1 / 2 : ℝ)) / (n : ℝ) ^ 2 := by
        gcongr
        simpa [div_eq_mul_inv, mul_comm] using hlog
      _ ≤ (4 * (n : ℝ) ^ (1 / 2 : ℝ)) / (n : ℝ) ^ 2 := by
        exact div_le_div_of_nonneg_right (by linarith [hpow]) (by positivity)
      _ = 4 / (n : ℝ) ^ (3 / 2 : ℝ) := by
        field_simp [hnpos.ne', (Real.rpow_pos_of_pos hnpos _).ne']
        rw [show (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) by
          exact (Real.rpow_natCast (n : ℝ) 2).symm]
        rw [← Real.rpow_add hnpos]
        norm_num
