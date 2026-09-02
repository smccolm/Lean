import GafniTao.FordLemma36Exponent

/-!
# Ford equation (3.21)

This is the quantitative decrement extracted from the exact recurrence
(3.14).  Ford's decimal `0.002` is represented by `1/500`.
-/

namespace GafniTao

noncomputable section

theorem fordEquation321
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let r := fordR36 k delta
    let d := delta / (k : ℝ) ^ 2
    d - fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≥
      (2 * d / (k : ℝ)) * ((2 - d) / (2 - d ^ 2) - 1 / 500) := by
  let r := fordR36 k delta
  let d := delta / (k : ℝ) ^ 2
  dsimp only
  have hk0 : (0 : ℝ) < k := by positivity
  have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hd0 : 0 < d := by
    dsimp [d]
    exact div_pos (lt_of_lt_of_le (by positivity) hdeltaLower.le) hkSq
  have hdLower : 1 / (k : ℝ) < d := by
    dsimp [d]
    rw [div_lt_div_iff₀ hk0 hkSq]
    have hmul := mul_lt_mul_of_pos_right hdeltaLower hk0
    nlinarith
  have hdHalf : d ≤ 1 / 2 := by
    dsimp [d]
    rw [div_le_iff₀ hkSq]
    nlinarith
  let a : ℝ := (2 - d) / (2 - d ^ 2)
  have hden : 0 < 2 - d ^ 2 := by nlinarith [sq_nonneg d]
  have ha0 : 0 ≤ a := by
    dsimp [a]
    exact div_nonneg (by linarith) hden.le
  have haOne : a ≤ 1 := by
    dsimp [a]
    rw [div_le_one hden]
    nlinarith [mul_nonneg hd0.le (by linarith : 0 ≤ 1 - d)]
  have hinvD : 1 / d < (k : ℝ) := by
    rw [div_lt_iff₀ hd0]
    have := (div_lt_iff₀ hk0).mp hdLower
    nlinarith
  have herr :
      a * (32 / (21 * (k : ℝ) ^ 2) +
        16 / (7 * d * (k : ℝ) ^ 3)) ≤ 1 / (250 * (k : ℝ)) := by
    have hsecond : 16 / (7 * d * (k : ℝ) ^ 3) ≤
        16 / (7 * (k : ℝ) ^ 2) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hkd : 1 ≤ (k : ℝ) * d := by
        have := hdLower.le
        rw [div_le_iff₀ hk0] at this
        simpa [mul_comm] using this
      nlinarith
    have hsum : 32 / (21 * (k : ℝ) ^ 2) +
          16 / (7 * d * (k : ℝ) ^ 3) ≤
        80 / (21 * (k : ℝ) ^ 2) := by
      have heq : 32 / (21 * (k : ℝ) ^ 2) +
          16 / (7 * (k : ℝ) ^ 2) =
            80 / (21 * (k : ℝ) ^ 2) := by field_simp; ring
      linarith
    have hsum0 : 0 ≤ 32 / (21 * (k : ℝ) ^ 2) +
        16 / (7 * d * (k : ℝ) ^ 3) := by positivity
    have haMul : a * (32 / (21 * (k : ℝ) ^ 2) +
          16 / (7 * d * (k : ℝ) ^ 3)) ≤
        80 / (21 * (k : ℝ) ^ 2) := by
      calc
        a * (32 / (21 * (k : ℝ) ^ 2) +
            16 / (7 * d * (k : ℝ) ^ 3)) ≤
          1 * (32 / (21 * (k : ℝ) ^ 2) +
            16 / (7 * d * (k : ℝ) ^ 3)) := by gcongr
        _ ≤ 80 / (21 * (k : ℝ) ^ 2) := by simpa using hsum
    have hnumeric : 80 / (21 * (k : ℝ) ^ 2) ≤
        1 / (250 * (k : ℝ)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hk1000 : (1000 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    exact haMul.trans hnumeric
  have hfactor :
      (2 / (k : ℝ)) * (a - 1 / 500) ≤
        a * (2 / (k : ℝ) - 32 / (21 * (k : ℝ) ^ 2) -
          16 / (7 * d * (k : ℝ) ^ 3)) := by
    have herr' : a * (32 / (21 * (k : ℝ) ^ 2) +
        16 / (7 * d * (k : ℝ) ^ 3)) ≤
          (2 / (k : ℝ)) * (1 / 500) := by
      calc
        a * (32 / (21 * (k : ℝ) ^ 2) +
            16 / (7 * d * (k : ℝ) ^ 3)) ≤
              1 / (250 * (k : ℝ)) := herr
        _ = (2 / (k : ℝ)) * (1 / 500) := by
          field_simp
          norm_num
    calc
      (2 / (k : ℝ)) * (a - 1 / 500) =
          a * (2 / (k : ℝ)) - (2 / (k : ℝ)) * (1 / 500) := by ring
      _ ≤ a * (2 / (k : ℝ)) -
          a * (32 / (21 * (k : ℝ) ^ 2) +
            16 / (7 * d * (k : ℝ) ^ 3)) := sub_le_sub_left herr' _
      _ = a * (2 / (k : ℝ) - 32 / (21 * (k : ℝ) ^ 2) -
          16 / (7 * d * (k : ℝ) ^ 3)) := by ring
  have h314 := fordEquation314 hk hdeltaLower hdeltaUpper
  change fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≤
    d * (1 - a * (2 / (k : ℝ) - 32 / (21 * (k : ℝ) ^ 2) -
      16 / (7 * d * (k : ℝ) ^ 3))) at h314
  have hdMul := mul_le_mul_of_nonneg_left hfactor hd0.le
  change d - fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≥
    (2 * d / (k : ℝ)) * (a - 1 / 500)
  calc
    (2 * d / (k : ℝ)) * (a - 1 / 500) =
        d * ((2 / (k : ℝ)) * (a - 1 / 500)) := by ring
    _ ≤ d * (a * (2 / (k : ℝ) - 32 / (21 * (k : ℝ) ^ 2) -
        16 / (7 * d * (k : ℝ) ^ 3))) := hdMul
    _ ≤ d - fordDeltaZero35 k r delta / (k : ℝ) ^ 2 := by linarith

theorem fordEquation321_sequence
    {k i : ℕ} (hk : 1000 ≤ k)
    (hiLower : (k : ℝ) < fordDeltaSequence36 k i)
    (hiUpper : fordDeltaSequence36 k i ≤ ((k : ℝ) ^ 2 - k) / 2) :
    fordDSequence36 k i - fordDSequence36 k (i + 1) ≥
      (2 * fordDSequence36 k i / (k : ℝ)) *
        ((2 - fordDSequence36 k i) /
          (2 - fordDSequence36 k i ^ 2) - 1 / 500) := by
  simpa [fordDSequence36, fordDeltaSequence36_succ, fordRSequence36] using
    fordEquation321 hk hiLower hiUpper

#print axioms fordEquation321
#print axioms fordEquation321_sequence

end

end GafniTao
