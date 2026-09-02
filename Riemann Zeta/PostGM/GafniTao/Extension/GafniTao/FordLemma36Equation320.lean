import GafniTao.FordLemma36Decrement

/-!
# Ford equation (3.20)

This file proves the literal comparison
`W^(Delta_(n-1)-Delta_n) > k^(3k) 1.06^(4k(n-1)+k^2)`
on Ford's source range.  All displayed decimals are exact rationals.
-/

namespace GafniTao

noncomputable section

def fordW36 (k : ℕ) : ℝ :=
  (k : ℝ) ^ ((411 / 100 : ℝ) * k)

theorem ford_exp_sixty_nine_tenths_lt_thousand :
    Real.exp (69 / 10 : ℝ) < 1000 := by
  have hbase := real_exp_le_fordExpTaylorUpper
    (n := 20) (x := (69 / 70 : ℝ)) (by norm_num) (by norm_num [abs_of_nonneg])
  have hpow := pow_le_pow_left₀ (Real.exp_pos (69 / 70 : ℝ)).le hbase 7
  calc
    Real.exp (69 / 10 : ℝ) = Real.exp ((7 : ℝ) * (69 / 70 : ℝ)) := by norm_num
    _ = Real.exp (69 / 70 : ℝ) ^ 7 := Real.exp_nat_mul (69 / 70 : ℝ) 7
    _ ≤ fordExpTaylorUpper 20 (69 / 70 : ℝ) ^ 7 := hpow
    _ < 1000 := by norm_num [fordExpTaylorUpper]

theorem ford_log_thousand_lower : (69 / 10 : ℝ) < Real.log 1000 := by
  have h := ford_exp_sixty_nine_tenths_lt_thousand
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 1000)] at h
  exact Real.exp_lt_exp.mp h

theorem ford_log_k_lower {k : ℕ} (hk : 1000 ≤ k) :
    (69 / 10 : ℝ) < Real.log k := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  exact ford_log_thousand_lower.trans_le
    (Real.strictMonoOn_log.monotoneOn
      (by norm_num : (1000 : ℝ) ∈ Set.Ioi 0)
      (by exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1000) hkR)
      hkR)

theorem ford_log_one_point_zero_six_upper :
    Real.log (53 / 50 : ℝ) ≤ 1821 / 31250 := by
  have h := log_one_add_le_cubic (x := (3 / 50 : ℝ)) (by norm_num)
  norm_num at h ⊢
  exact h

theorem fordEquation320_eta_exponent
    {k n : ℕ} (hk : 1000 ≤ k)
    (hnUpper : 100 * (n - 1) ≤ 197 * k) :
    (((4 * k * (n - 1) + k ^ 2 : ℕ) : ℝ)) * Real.log (53 / 50) ≤
      (3 / 40 : ℝ) * (k : ℝ) ^ 2 * Real.log k := by
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : 100 * (((n - 1 : ℕ) : ℝ)) ≤ 197 * (k : ℝ) := by
    exact_mod_cast hnUpper
  have hM : (((4 * k * (n - 1) + k ^ 2 : ℕ) : ℝ)) ≤
      (222 / 25 : ℝ) * (k : ℝ) ^ 2 := by
    push_cast
    nlinarith
  have hlogEta := ford_log_one_point_zero_six_upper
  have hlogEta0 : 0 ≤ Real.log (53 / 50 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hlogK := ford_log_k_lower hk
  calc
    (((4 * k * (n - 1) + k ^ 2 : ℕ) : ℝ)) * Real.log (53 / 50) ≤
        ((222 / 25 : ℝ) * (k : ℝ) ^ 2) * Real.log (53 / 50) := by
      gcongr
    _ ≤ ((222 / 25 : ℝ) * (k : ℝ) ^ 2) * (1821 / 31250) := by
      gcongr
    _ ≤ (3 / 40 : ℝ) * (k : ℝ) ^ 2 * (69 / 10) := (by
      have hk0 : (0 : ℝ) < k := by positivity
      nlinarith [sq_pos_of_pos hk0])
    _ ≤ (3 / 40 : ℝ) * (k : ℝ) ^ 2 * Real.log k := by
      gcongr

theorem fordEquation320_eta_power
    {k n : ℕ} (hk : 1000 ≤ k)
    (hnUpper : 100 * (n - 1) ≤ 197 * k) :
    (53 / 50 : ℝ) ^ (4 * k * (n - 1) + k ^ 2) ≤
      (k : ℝ) ^ ((3 / 40 : ℝ) * (k : ℝ) ^ 2) := by
  have heta : (0 : ℝ) < 53 / 50 := by norm_num
  have hk0 : (0 : ℝ) < k := by positivity
  rw [← Real.rpow_natCast]
  rw [Real.rpow_def_of_pos heta]
  rw [Real.rpow_def_of_pos hk0]
  apply Real.exp_le_exp.mpr
  simpa [mul_comm] using fordEquation320_eta_exponent hk hnUpper

theorem fordEquation320_k_power
    {k : ℕ} (hk : 1000 ≤ k) :
    (k : ℝ) ^ (3 * k) ≤
      (k : ℝ) ^ ((3 / 1000 : ℝ) * (k : ℝ) ^ 2) := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hk1
  push_cast
  have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

theorem fordEquation320_rhs_upper
    {k n : ℕ} (hk : 1000 ≤ k)
    (hnUpper : 100 * (n - 1) ≤ 197 * k) :
    (k : ℝ) ^ (3 * k) * (53 / 50 : ℝ) ^ (4 * k * (n - 1) + k ^ 2) ≤
      (k : ℝ) ^ ((39 / 500 : ℝ) * (k : ℝ) ^ 2) := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  calc
    (k : ℝ) ^ (3 * k) * (53 / 50 : ℝ) ^ (4 * k * (n - 1) + k ^ 2) ≤
        (k : ℝ) ^ ((3 / 1000 : ℝ) * (k : ℝ) ^ 2) *
          (k : ℝ) ^ ((3 / 40 : ℝ) * (k : ℝ) ^ 2) :=
      mul_le_mul (fordEquation320_k_power hk) (fordEquation320_eta_power hk hnUpper)
        (by positivity : 0 ≤ (53 / 50 : ℝ) ^ (4 * k * (n - 1) + k ^ 2))
        (Real.rpow_nonneg hk0 ((3 / 1000 : ℝ) * (k : ℝ) ^ 2))
    _ = (k : ℝ) ^
        (((3 / 1000 : ℝ) * (k : ℝ) ^ 2) +
          ((3 / 40 : ℝ) * (k : ℝ) ^ 2)) := by
      exact (Real.rpow_add (show (0 : ℝ) < k by positivity)
        ((3 / 1000 : ℝ) * (k : ℝ) ^ 2)
        ((3 / 40 : ℝ) * (k : ℝ) ^ 2)).symm
    _ = (k : ℝ) ^ ((39 / 500 : ℝ) * (k : ℝ) ^ 2) := by
      congr 2
      ring

theorem fordEquation320_lhs_lower
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 2 ≤ n)
    (hnUpper : 100 * (n - 1) ≤ 197 * k)
    (habove : ∀ m, m < n - 2 → (k : ℝ) < fordDeltaSequence36 k m) :
    (k : ℝ) ^ ((787 / 10000 : ℝ) * (k : ℝ) ^ 2) ≤
      (fordW36 k) ^
        (fordDeltaSequence36 k (n - 2) - fordDeltaSequence36 k (n - 1)) := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have hdiff := fordDeltaSequence36_source_decrement hk hnLower hnUpper habove
  have hexponent : (787 / 10000 : ℝ) * (k : ℝ) ^ 2 ≤
      ((411 / 100 : ℝ) * k) *
        (fordDeltaSequence36 k (n - 2) - fordDeltaSequence36 k (n - 1)) := by
    have hmul := mul_le_mul_of_nonneg_left hdiff
      (show 0 ≤ (411 / 100 : ℝ) * k by positivity)
    nlinarith
  calc
    (k : ℝ) ^ ((787 / 10000 : ℝ) * (k : ℝ) ^ 2) ≤
        (k : ℝ) ^ (((411 / 100 : ℝ) * k) *
          (fordDeltaSequence36 k (n - 2) - fordDeltaSequence36 k (n - 1))) :=
      Real.rpow_le_rpow_of_exponent_le hk1 hexponent
    _ = (fordW36 k) ^
        (fordDeltaSequence36 k (n - 2) - fordDeltaSequence36 k (n - 1)) := by
      unfold fordW36
      simpa using (Real.rpow_mul hk0.le
        ((411 / 100 : ℝ) * k)
        (fordDeltaSequence36 k (n - 2) - fordDeltaSequence36 k (n - 1)))

/-- Ford's equation (3.20), in the source's one-based index. -/
theorem fordEquation320
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 2 ≤ n)
    (hnUpper : 100 * (n - 1) ≤ 197 * k)
    (habove : ∀ m, m < n - 2 → (k : ℝ) < fordDeltaSequence36 k m) :
    (k : ℝ) ^ (3 * k) * (53 / 50 : ℝ) ^ (4 * k * (n - 1) + k ^ 2) <
      (fordW36 k) ^
        (fordDeltaSequence36 k (n - 2) - fordDeltaSequence36 k (n - 1)) := by
  have hk1 : (1 : ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hstrict :
      (k : ℝ) ^ ((39 / 500 : ℝ) * (k : ℝ) ^ 2) <
        (k : ℝ) ^ ((787 / 10000 : ℝ) * (k : ℝ) ^ 2) := by
    apply Real.rpow_lt_rpow_of_exponent_lt hk1
    have hk0 : (0 : ℝ) < k := by positivity
    nlinarith [sq_pos_of_pos hk0]
  exact (fordEquation320_rhs_upper hk hnUpper).trans_lt
    (hstrict.trans_le (fordEquation320_lhs_lower hk hnLower hnUpper habove))

/-- The canonical Ford sequence remains in the `Delta > k` branch throughout
the complete early range.  This discharges the branch premise used above. -/
theorem fordDeltaSequence36_above_through_197
    {k i : ℕ} (hk : 1000 ≤ k)
    (hi : 100 * (i + 1) ≤ 197 * k) :
    (k : ℝ) < fordDeltaSequence36 k i := by
  induction i using Nat.strong_induction_on with
  | h i ih =>
      have habove : ∀ m, m < i → (k : ℝ) < fordDeltaSequence36 k m := by
        intro m hm
        apply ih m hm
        have hm1 : m + 1 ≤ i + 1 := by omega
        omega
      have hlow := fordDSequence36_source_predecessor_lower
        (k := k) (n := i + 2) hk (by omega) (by simpa using hi) habove
      have hindex : i + 2 - 2 = i := by omega
      rw [hindex] at hlow
      have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
      have hscaled := mul_le_mul_of_nonneg_right hlow hkSq.le
      unfold fordDSequence36 at hscaled
      have hscaled' : (24119 / 2500000 : ℝ) * (k : ℝ) ^ 2 ≤
          fordDeltaSequence36 k i := by
        convert hscaled using 1
        all_goals field_simp
      have hkR : (1000 : ℝ) ≤ k := by exact_mod_cast hk
      have hcut : (k : ℝ) <
          (24119 / 2500000 : ℝ) * (k : ℝ) ^ 2 := by
        nlinarith
      exact hcut.trans_le hscaled'

/-- Equation (3.20) with every sequence-range premise discharged from Ford's
canonical recurrence. -/
theorem fordEquation320_native
    {k n : ℕ} (hk : 1000 ≤ k) (hnLower : 2 ≤ n)
    (hnUpper : 100 * (n - 1) ≤ 197 * k) :
    (k : ℝ) ^ (3 * k) * (53 / 50 : ℝ) ^ (4 * k * (n - 1) + k ^ 2) <
      (fordW36 k) ^
        (fordDeltaSequence36 k (n - 2) - fordDeltaSequence36 k (n - 1)) := by
  apply fordEquation320 hk hnLower hnUpper
  intro m hm
  apply fordDeltaSequence36_above_through_197 hk
  have hm1 : m + 1 ≤ n - 1 := by omega
  omega

#print axioms ford_exp_sixty_nine_tenths_lt_thousand
#print axioms ford_log_thousand_lower
#print axioms ford_log_k_lower
#print axioms ford_log_one_point_zero_six_upper
#print axioms fordEquation320_eta_exponent
#print axioms fordEquation320_eta_power
#print axioms fordEquation320_k_power
#print axioms fordEquation320_rhs_upper
#print axioms fordEquation320_lhs_lower
#print axioms fordEquation320
#print axioms fordDeltaSequence36_above_through_197
#print axioms fordEquation320_native

end

end GafniTao
