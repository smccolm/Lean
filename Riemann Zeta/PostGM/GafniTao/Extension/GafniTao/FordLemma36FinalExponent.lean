import GafniTao.FordLemma36Decay

/-!
# Ford Lemma 3.6: final exponent estimate

The source TeX displays a positive `0.49/k` in the reciprocal-factor line.
The advertised final `1.69/k` requires the negative estimate proved below;
it follows from the actual recurrence in the range of Lemma 3.6.
-/

namespace GafniTao

noncomputable section

theorem fordInitialFactor36_bound {k : ℕ} (hk : 1000 ≤ k) :
    fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
        Real.exp (fordDSequence36 k 0) ≤
      (3 / 4 : ℝ) * Real.exp (1 / 2 - 7 / (6 * (k : ℝ))) := by
  have hk0 : (0 : ℝ) < k := by positivity
  let x : ℝ := 1 / (k : ℝ)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hd0 : fordDSequence36 k 0 = (1 - x) / 2 := by
    rw [fordDSequence36_zero]
    dsimp [x]
    field_simp
  have hp : (1 - x) * (1 + x / 3) ≤ Real.exp (-2 * x / 3) := by
    have hone := Real.add_one_le_exp (-2 * x / 3)
    have halg : (1 - x) * (1 + x / 3) ≤ 1 - 2 * x / 3 := by
      nlinarith [sq_nonneg x]
    linarith
  have hform :
      fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
          Real.exp (fordDSequence36 k 0) =
        (3 / 4 : ℝ) * Real.exp (1 / 2) *
          ((1 - x) * (1 + x / 3)) * Real.exp (-x / 2) := by
    rw [hd0]
    rw [show (1 - x) / 2 = 1 / 2 + (-x / 2) by ring, Real.exp_add]
    ring
  rw [hform]
  calc
    (3 / 4 : ℝ) * Real.exp (1 / 2) *
        ((1 - x) * (1 + x / 3)) * Real.exp (-x / 2) ≤
      (3 / 4 : ℝ) * Real.exp (1 / 2) *
        Real.exp (-2 * x / 3) * Real.exp (-x / 2) := by
          gcongr
    _ = (3 / 4 : ℝ) * Real.exp (1 / 2 - 7 / (6 * (k : ℝ))) := by
      rw [show (3 / 4 : ℝ) * Real.exp (1 / 2) * Real.exp (-2 * x / 3) *
          Real.exp (-x / 2) =
          (3 / 4 : ℝ) *
            (Real.exp (1 / 2) * Real.exp (-2 * x / 3) * Real.exp (-x / 2)) by
        ring]
      rw [← Real.exp_add, ← Real.exp_add]
      dsimp [x]
      congr 2
      field_simp
      ring

theorem fordReciprocalFactor36_bound
    {k : ℕ} {d : ℝ} (hk : 1000 ≤ k)
    (hdLower : 1 / (k : ℝ) < d) (hdUpper : d ≤ 1 / 50) :
    Real.exp (-d) / (2 - d) ≤
      (1 / 2 : ℝ) * Real.exp (-49 / (100 * (k : ℝ))) := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hdLower.le
  have htwo : 0 < 2 - d := by linarith
  have hratioLower : (49 / 100 : ℝ) ≤ (1 - d) / (2 - d) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 100) htwo]
    nlinarith
  have hkd : 1 < (k : ℝ) * d := by
    have := (div_lt_iff₀ hk0).mp hdLower
    nlinarith
  have hexponent : d / (2 - d) - d ≤ -49 / (100 * (k : ℝ)) := by
    have hprod : 49 / (100 * (k : ℝ)) ≤ d * (1 - d) / (2 - d) := by
      have hmul : (49 / 100 : ℝ) * 1 ≤
          ((1 - d) / (2 - d)) * ((k : ℝ) * d) :=
        mul_le_mul hratioLower hkd.le (by norm_num)
          (by positivity : (0 : ℝ) ≤ (1 - d) / (2 - d))
      have hmul' : (49 / 100 : ℝ) ≤
          ((1 - d) / (2 - d)) * ((k : ℝ) * d) := by
        simpa using hmul
      calc
        49 / (100 * (k : ℝ)) = (49 / 100 : ℝ) / (k : ℝ) := by ring
        _ ≤ (((1 - d) / (2 - d)) * ((k : ℝ) * d)) / (k : ℝ) :=
          div_le_div_of_nonneg_right hmul' hk0.le
        _ = d * (1 - d) / (2 - d) := by field_simp [hk0.ne']
    have hid : d / (2 - d) - d = -(d * (1 - d) / (2 - d)) := by
      field_simp [htwo.ne']
      ring
    rw [hid]
    simpa only [neg_div] using neg_le_neg hprod
  have hone := Real.add_one_le_exp (d / (2 - d))
  have hinv : 1 / (2 - d) ≤ (1 / 2 : ℝ) * Real.exp (d / (2 - d)) := by
    have heq : (1 / 2 : ℝ) * (d / (2 - d) + 1) = 1 / (2 - d) := by
      field_simp [htwo.ne']
      ring
    rw [← heq]
    exact mul_le_mul_of_nonneg_left hone (by norm_num)
  calc
    Real.exp (-d) / (2 - d) = Real.exp (-d) * (1 / (2 - d)) := by ring
    _ ≤ Real.exp (-d) * ((1 / 2 : ℝ) * Real.exp (d / (2 - d))) :=
      mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le
    _ = (1 / 2 : ℝ) * Real.exp (d / (2 - d) - d) := by
      rw [show Real.exp (-d) * ((1 / 2 : ℝ) * Real.exp (d / (2 - d))) =
          (1 / 2 : ℝ) * (Real.exp (-d) * Real.exp (d / (2 - d))) by ring]
      rw [← Real.exp_add]
      congr 2
      ring
    _ ≤ (1 / 2 : ℝ) * Real.exp (-49 / (100 * (k : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)

theorem fordLemma36_delta_exponent_above
    {k n : ℕ} (hk : 1000 ≤ k) (hn : 2 * k - 1 ≤ n)
    (habove : ∀ m, m ≤ n → (k : ℝ) < fordDeltaSequence36 k m) :
    fordDSequence36 k n ≤
      (3 / 8 : ℝ) * Real.exp
        (1 / 2 - 2 * ((n + 1 : ℕ) : ℝ) / (k : ℝ) +
          169 / (100 * (k : ℝ))) := by
  have habovePrev : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m := by
    intro m hm
    exact habove m hm.le
  have heq319 := fordEquation319 hk (by omega) habovePrev
  have hsmall := fordDSequence36_small_after_two_k hk hn habovePrev
  have hdLower : 1 / (k : ℝ) < fordDSequence36 k n := by
    unfold fordDSequence36
    have hk0 : (0 : ℝ) < k := by positivity
    have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
    rw [div_lt_div_iff₀ hk0 hkSq]
    have hmul := mul_lt_mul_of_pos_right (habove n le_rfl) hk0
    nlinarith
  have hinit := fordInitialFactor36_bound hk
  have hinv := fordReciprocalFactor36_bound hk hdLower hsmall.le
  have hloss := fordPotentialLoss36_lower hk
  let E : ℝ := -(n : ℝ) * fordPotentialLoss36 k + 67 / (50 * (k : ℝ))
  have hE : E ≤ -2 * (n : ℝ) / (k : ℝ) + 67 / (50 * (k : ℝ)) := by
    dsimp [E]
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hmul := mul_le_mul_of_nonneg_left hloss hn0
    have hneg : -(n : ℝ) * fordPotentialLoss36 k ≤
        -(n : ℝ) * (2 / (k : ℝ)) := by nlinarith
    calc
      -(n : ℝ) * fordPotentialLoss36 k + 67 / (50 * (k : ℝ)) ≤
          -(n : ℝ) * (2 / (k : ℝ)) + 67 / (50 * (k : ℝ)) :=
        by linarith
      _ = -2 * (n : ℝ) / (k : ℝ) + 67 / (50 * (k : ℝ)) := by ring
  have hrewrite :
      (fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
          Real.exp (fordDSequence36 k 0)) /
        ((2 - fordDSequence36 k n) * Real.exp (fordDSequence36 k n)) *
          Real.exp E =
      (fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
          Real.exp (fordDSequence36 k 0)) *
        (Real.exp (-fordDSequence36 k n) / (2 - fordDSequence36 k n)) *
          Real.exp E := by
    rw [Real.exp_neg]
    field_simp [Real.exp_ne_zero]
  have hbound :
      (fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
          Real.exp (fordDSequence36 k 0)) *
        (Real.exp (-fordDSequence36 k n) / (2 - fordDSequence36 k n)) *
          Real.exp E ≤
      (3 / 8 : ℝ) * Real.exp
        (1 / 2 - 2 * (n : ℝ) / (k : ℝ) -
          19 / (60 * (k : ℝ))) := by
    calc
      (fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
          Real.exp (fordDSequence36 k 0)) *
        (Real.exp (-fordDSequence36 k n) / (2 - fordDSequence36 k n)) *
          Real.exp E ≤
        ((3 / 4 : ℝ) * Real.exp (1 / 2 - 7 / (6 * (k : ℝ)))) *
          ((1 / 2 : ℝ) * Real.exp (-49 / (100 * (k : ℝ)))) *
            Real.exp (-2 * (n : ℝ) / (k : ℝ) +
              67 / (50 * (k : ℝ))) := by
                gcongr
                · exact div_nonneg (Real.exp_pos _).le (by linarith [hsmall])
      _ = (3 / 8 : ℝ) * Real.exp
          (1 / 2 - 2 * (n : ℝ) / (k : ℝ) -
            19 / (60 * (k : ℝ))) := by
              rw [show ((3 / 4 : ℝ) * Real.exp
                  (1 / 2 - 7 / (6 * (k : ℝ)))) *
                    ((1 / 2 : ℝ) * Real.exp (-49 / (100 * (k : ℝ)))) *
                      Real.exp (-2 * (n : ℝ) / (k : ℝ) +
                        67 / (50 * (k : ℝ))) =
                    (3 / 8 : ℝ) *
                      (Real.exp (1 / 2 - 7 / (6 * (k : ℝ))) *
                        Real.exp (-49 / (100 * (k : ℝ))) *
                          Real.exp (-2 * (n : ℝ) / (k : ℝ) +
                            67 / (50 * (k : ℝ)))) by ring]
              rw [← Real.exp_add, ← Real.exp_add]
              congr 2
              field_simp
              ring
  rw [show -(n : ℝ) * fordPotentialLoss36 k +
      67 / (50 * (k : ℝ)) = E by rfl] at heq319
  rw [hrewrite] at heq319
  calc
    fordDSequence36 k n ≤
        (fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
          Real.exp (fordDSequence36 k 0)) *
        (Real.exp (-fordDSequence36 k n) / (2 - fordDSequence36 k n)) *
          Real.exp E := heq319
    _ ≤ (3 / 8 : ℝ) * Real.exp
        (1 / 2 - 2 * (n : ℝ) / (k : ℝ) -
          19 / (60 * (k : ℝ))) := hbound
    _ ≤ (3 / 8 : ℝ) * Real.exp
        (1 / 2 - 2 * ((n + 1 : ℕ) : ℝ) / (k : ℝ) +
          169 / (100 * (k : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      have hk0 : (0 : ℝ) < k := by positivity
      push_cast
      field_simp [hk0.ne']
      nlinarith

#print axioms fordInitialFactor36_bound
#print axioms fordReciprocalFactor36_bound
#print axioms fordLemma36_delta_exponent_above

end

end GafniTao
