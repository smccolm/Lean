import GafniTao.FordLemma36Below

/-!
# Ford Lemma 3.6: the first crossing of `Delta = k`

The printed proof uses a reciprocal correction at the final iterate.  That
correction only needs the normalized exponent to be at least `0.99/k`; below
that cutoff the advertised endpoint bound is already larger.  This split
also covers the first iterate crossing from `Delta > k` to `Delta ≤ k`.
-/

namespace GafniTao

noncomputable section

theorem fordReciprocalFactor36_crossing_bound
    {k : ℕ} {d : ℝ} (hk : 1000 ≤ k)
    (hdLower : 99 / (100 * (k : ℝ)) ≤ d) (hdUpper : d ≤ 1 / 50) :
    Real.exp (-d) / (2 - d) ≤
      (1 / 2 : ℝ) * Real.exp (-4851 / (10000 * (k : ℝ))) := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hd0 : 0 < d := lt_of_lt_of_le (by positivity) hdLower
  have htwo : 0 < 2 - d := by linarith
  have hratioLower : (49 / 100 : ℝ) ≤ (1 - d) / (2 - d) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 100) htwo]
    nlinarith
  have hkd : (99 / 100 : ℝ) ≤ (k : ℝ) * d := by
    have h := mul_le_mul_of_nonneg_left hdLower hk0.le
    calc
      (99 / 100 : ℝ) = (k : ℝ) * (99 / (100 * (k : ℝ))) := by
        field_simp
      _ ≤ (k : ℝ) * d := h
  have hexponent : d / (2 - d) - d ≤
      -4851 / (10000 * (k : ℝ)) := by
    have hmul : (4851 / 10000 : ℝ) ≤
        ((1 - d) / (2 - d)) * ((k : ℝ) * d) := by
      have := mul_le_mul hratioLower hkd (by norm_num : (0 : ℝ) ≤ 99 / 100)
        (by positivity : (0 : ℝ) ≤ (1 - d) / (2 - d))
      norm_num at this ⊢
      exact this
    have hprod : 4851 / (10000 * (k : ℝ)) ≤
        d * (1 - d) / (2 - d) := by
      calc
        4851 / (10000 * (k : ℝ)) =
            (4851 / 10000 : ℝ) / (k : ℝ) := by ring
        _ ≤ (((1 - d) / (2 - d)) * ((k : ℝ) * d)) / (k : ℝ) :=
          div_le_div_of_nonneg_right hmul hk0.le
        _ = d * (1 - d) / (2 - d) := by field_simp [hk0.ne']
    have hid : d / (2 - d) - d =
        -(d * (1 - d) / (2 - d)) := by
      field_simp [htwo.ne']
      ring
    rw [hid]
    simpa only [neg_div] using neg_le_neg hprod
  have hone := Real.add_one_le_exp (d / (2 - d))
  have hinv : 1 / (2 - d) ≤
      (1 / 2 : ℝ) * Real.exp (d / (2 - d)) := by
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
    _ ≤ (1 / 2 : ℝ) * Real.exp (-4851 / (10000 * (k : ℝ))) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) (by norm_num)

theorem fordLemma36_normalized_target_ge_crossing_cutoff
    {k N : ℕ} (hk : 1000 ≤ k)
    (hN : (N : ℝ) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) :
    99 / (100 * (k : ℝ)) ≤
      (3 / 8 : ℝ) * Real.exp
        (1 / 2 - 2 * (N : ℝ) / (k : ℝ) +
          169 / (100 * (k : ℝ))) := by
  have hk0 : (0 : ℝ) < k := by positivity
  have hcut : 99 / 100 ≤ 1 - 1 / (k : ℝ) := by
    have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
    have : 1 / (k : ℝ) ≤ 1 / 1000 := by
      exact one_div_le_one_div_of_le (by norm_num) hk1000
    linarith
  have hfull := fordLemma36_target_ge_contracted_k hk hN
  have hcutScaled : (k : ℝ) * (99 / 100) ≤
      (k : ℝ) * (1 - 1 / (k : ℝ)) := by gcongr
  have hcombined := hcutScaled.trans hfull
  have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  calc
    99 / (100 * (k : ℝ)) =
        ((k : ℝ) * (99 / 100)) / (k : ℝ) ^ 2 := by field_simp
    _ ≤ ((3 / 8 : ℝ) * (k : ℝ) ^ 2 * Real.exp
          (1 / 2 - 2 * (N : ℝ) / (k : ℝ) +
            169 / (100 * (k : ℝ)))) / (k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hcombined hkSq.le
    _ = (3 / 8 : ℝ) * Real.exp
          (1 / 2 - 2 * (N : ℝ) / (k : ℝ) +
            169 / (100 * (k : ℝ))) := by field_simp

theorem fordLemma36_delta_exponent_of_previous_above
    {k n : ℕ} (hk : 1000 ≤ k) (hn : 2 * k - 1 ≤ n)
    (habovePrev : ∀ m, m < n → (k : ℝ) < fordDeltaSequence36 k m)
    (hN : (((n + 1 : ℕ) : ℝ)) ≤
      (k : ℝ) / 2 * (1 / 2 + Real.log (3 * (k : ℝ) / 8)) + 1) :
    fordDSequence36 k n ≤
      (3 / 8 : ℝ) * Real.exp
        (1 / 2 - 2 * (((n + 1 : ℕ) : ℝ)) / (k : ℝ) +
          169 / (100 * (k : ℝ))) := by
  have hsmall := fordDSequence36_small_after_two_k hk hn habovePrev
  by_cases hcut : fordDSequence36 k n < 99 / (100 * (k : ℝ))
  · exact hcut.le.trans (fordLemma36_normalized_target_ge_crossing_cutoff hk hN)
  · have heq319 := fordEquation319 hk (by omega) habovePrev
    have hinit := fordInitialFactor36_bound hk
    have hinv := fordReciprocalFactor36_crossing_bound hk (le_of_not_gt hcut) hsmall.le
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
            -(n : ℝ) * (2 / (k : ℝ)) + 67 / (50 * (k : ℝ)) := by linarith
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
            9353 / (30000 * (k : ℝ))) := by
      calc
        (fordDSequence36 k 0 * (2 - fordDSequence36 k 0) *
            Real.exp (fordDSequence36 k 0)) *
          (Real.exp (-fordDSequence36 k n) / (2 - fordDSequence36 k n)) *
            Real.exp E ≤
          ((3 / 4 : ℝ) * Real.exp (1 / 2 - 7 / (6 * (k : ℝ)))) *
            ((1 / 2 : ℝ) * Real.exp (-4851 / (10000 * (k : ℝ)))) *
              Real.exp (-2 * (n : ℝ) / (k : ℝ) +
                67 / (50 * (k : ℝ))) := by
          gcongr
          exact div_nonneg (Real.exp_pos _).le (by linarith [hsmall])
        _ = (3 / 8 : ℝ) * Real.exp
            (1 / 2 - 2 * (n : ℝ) / (k : ℝ) -
              9353 / (30000 * (k : ℝ))) := by
          rw [show ((3 / 4 : ℝ) * Real.exp
              (1 / 2 - 7 / (6 * (k : ℝ)))) *
                ((1 / 2 : ℝ) * Real.exp (-4851 / (10000 * (k : ℝ)))) *
                  Real.exp (-2 * (n : ℝ) / (k : ℝ) +
                    67 / (50 * (k : ℝ))) =
                (3 / 8 : ℝ) *
                  (Real.exp (1 / 2 - 7 / (6 * (k : ℝ))) *
                    Real.exp (-4851 / (10000 * (k : ℝ))) *
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
            9353 / (30000 * (k : ℝ))) := hbound
      _ ≤ (3 / 8 : ℝ) * Real.exp
          (1 / 2 - 2 * (((n + 1 : ℕ) : ℝ)) / (k : ℝ) +
            169 / (100 * (k : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.exp_le_exp.mpr
        have hk0 : (0 : ℝ) < k := by positivity
        push_cast
        field_simp [hk0.ne']
        nlinarith

#print axioms fordReciprocalFactor36_crossing_bound
#print axioms fordLemma36_normalized_target_ge_crossing_cutoff
#print axioms fordLemma36_delta_exponent_of_previous_above

end

end GafniTao
