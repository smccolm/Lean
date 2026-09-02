import GafniTao.FordLemma36Equation317

/-!
# Ford Lemma 3.6: equation (3.14)

This is the normalized exponent recurrence obtained by combining (3.16) and
(3.17).  All occurrences of Ford's normalized `delta` are tied to the actual
updated exponent `fordDeltaZero35`.
-/

namespace GafniTao

noncomputable section

theorem fordEquation314
    {k : ℕ} {delta : ℝ} (hk : 1000 ≤ k)
    (hdeltaLower : (k : ℝ) < delta)
    (hdeltaUpper : delta ≤ ((k : ℝ) ^ 2 - k) / 2) :
    let r := fordR36 k delta
    let d := delta / (k : ℝ) ^ 2
    fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≤
      d * (1 - (2 - d) / (2 - d ^ 2) *
        (2 / (k : ℝ) - 32 / (21 * (k : ℝ) ^ 2) -
          16 / (7 * d * (k : ℝ) ^ 3))) := by
  let r := fordR36 k delta
  let d := delta / (k : ℝ) ^ 2
  let D : ℝ := 2 * (r : ℝ) * k + fordY35 k r delta
  let S : ℝ := 2 - d ^ 2
  dsimp only
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkSq : (0 : ℝ) < (k : ℝ) ^ 2 := by positivity
  have hd0 : 0 < d := by
    dsimp [d]
    have hdelta0 : 0 < delta := lt_of_lt_of_le (by positivity) hdeltaLower.le
    positivity
  have hdUpper : d ≤ ((k : ℝ) - 1) / (2 * k) := by
    dsimp [d]
    rw [div_le_iff₀ hkSq]
    field_simp
    nlinarith
  have hdHalf : d ≤ 1 / 2 := by
    have : ((k : ℝ) - 1) / (2 * k) < 1 / 2 := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith
  have hS : 0 < S := by
    dsimp [S]
    nlinarith [sq_nonneg d]
  have h316 := fordEquation316 hk hdeltaLower hdeltaUpper
  have hscaled := div_le_div_of_nonneg_right h316 hkSq.le
  have hnorm :
      (delta - 2 * (k : ℝ) +
          4 * (k : ℝ) ^ 2 * fordR36 k delta /
            (2 * (fordR36 k delta : ℝ) * k +
              fordY35 k (fordR36 k delta) delta) +
          16 * (1 - delta / (k : ℝ) ^ 2) / (7 * k)) /
          (k : ℝ) ^ 2 =
        d - 2 / (k : ℝ) + 4 * ((r : ℝ) / D) +
          16 * (1 - d) / (7 * (k : ℝ) ^ 3) := by
    dsimp [d, D, r]
    field_simp
  have hscaled' :
      fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≤
        d - 2 / (k : ℝ) + 4 * ((r : ℝ) / D) +
          16 * (1 - d) / (7 * (k : ℝ) ^ 3) := by
    rw [hnorm] at hscaled
    simpa [r] using hscaled
  have h317 := fordEquation317 hk hdeltaLower hdeltaUpper
  have hratio : (r : ℝ) / D ≤ fordRatioUpper36 k d := by
    simpa [r, d, D] using h317.2
  have hfirst :
      fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≤
        d - 2 / (k : ℝ) +
          4 * ((1 - d) / (S * k) + d / (S ^ 2 * (k : ℝ) ^ 2)) +
          16 * (1 - d) / (7 * (k : ℝ) ^ 3) := by
    have hfour := mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 4)
    dsimp [fordRatioUpper36, S] at hfour
    linarith
  have htwentyOne : 21 ≤ 8 * S * (2 - d) := by
    have hq : 4 * d ^ 2 - 6 * d - 11 ≤ 0 := by
      nlinarith [sq_nonneg d]
    have hp : 0 ≤ (2 * d - 1) * (4 * d ^ 2 - 6 * d - 11) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) hq
    dsimp [S]
    nlinarith
  have hsourceFactor : (1 - d) * S ≤ 2 - d := by
    have hb : 0 ≤ 1 + d - d ^ 2 := by nlinarith [sq_nonneg (d - 1 / 2)]
    have hp : 0 ≤ d * (1 + d - d ^ 2) := mul_nonneg hd0.le hb
    dsimp [S]
    nlinarith
  have htermTwo :
      4 * d / (S ^ 2 * (k : ℝ) ^ 2) ≤
        32 * d * (2 - d) / (21 * S * (k : ℝ) ^ 2) := by
    have hp :
        0 ≤ 4 * d * S * (k : ℝ) ^ 2 *
          (8 * S * (2 - d) - 21) := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have htermThree :
      16 * (1 - d) / (7 * (k : ℝ) ^ 3) ≤
        16 * (2 - d) / (7 * S * (k : ℝ) ^ 3) := by
    have hp :
        0 ≤ 16 * 7 * (k : ℝ) ^ 3 *
          ((2 - d) - (1 - d) * S) := by positivity
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  calc
    fordDeltaZero35 k r delta / (k : ℝ) ^ 2 ≤
        d - 2 / (k : ℝ) +
          4 * ((1 - d) / (S * k) + d / (S ^ 2 * (k : ℝ) ^ 2)) +
          16 * (1 - d) / (7 * (k : ℝ) ^ 3) := hfirst
    _ = d - 2 / (k : ℝ) + 4 * (1 - d) / (S * k) +
          4 * d / (S ^ 2 * (k : ℝ) ^ 2) +
          16 * (1 - d) / (7 * (k : ℝ) ^ 3) := by ring
    _ ≤ d - 2 / (k : ℝ) + 4 * (1 - d) / (S * k) +
          32 * d * (2 - d) / (21 * S * (k : ℝ) ^ 2) +
          16 * (2 - d) / (7 * S * (k : ℝ) ^ 3) := by
      have hleft :
          d - 2 / (k : ℝ) + 4 * (1 - d) / (S * k) +
              4 * d / (S ^ 2 * (k : ℝ) ^ 2) ≤
            d - 2 / (k : ℝ) + 4 * (1 - d) / (S * k) +
              32 * d * (2 - d) / (21 * S * (k : ℝ) ^ 2) := by
        gcongr
      exact add_le_add hleft htermThree
    _ = d * (1 - (2 - d) / S *
        (2 / (k : ℝ) - 32 / (21 * (k : ℝ) ^ 2) -
          16 / (7 * d * (k : ℝ) ^ 3))) := by
      field_simp
      ring

#print axioms fordEquation314

end

end GafniTao
