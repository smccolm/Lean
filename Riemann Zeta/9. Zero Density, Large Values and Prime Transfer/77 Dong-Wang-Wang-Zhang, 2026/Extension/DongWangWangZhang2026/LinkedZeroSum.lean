import DongWangWangZhang2026.DiskZeroGeometry

/-!
# Uniform farther-resolvent bound on the actual source scales

The absolute constant in Lemma 3.4 is absorbed by one threshold. This
derives the five-ninths log T bound used by the near/far count, including
both height signs and the displaced center.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex

/-- The larger horizontal shift pays at most one eightieth of the height logarithm. -/
theorem source_outer_shift_reciprocal {l Y Q : ℝ} (hl : 0 < l) (hY : 0 < Y)
    (hYQ : Y ≤ Q / 2) (hlY : 1 ≤ l * Y) :
    1 / (20 * l * Q / Y) ≤ Q / 80 := by
  have hQ : 0 < Q := by linarith
  have ha : 0 < 20 * l * Q / Y := by positivity
  apply (div_le_iff₀ ha).mpr
  have he : Q / 80 * (20 * l * Q / Y) = l * Q ^ 2 / (4 * Y) := by ring
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < 4 * Y)).mpr
  have hsq : 4 * Y ^ 2 ≤ Q ^ 2 := by nlinarith
  have h := mul_le_mul_of_nonneg_left hsq hl.le
  have h' := mul_le_mul_of_nonneg_right hlY hY.le
  nlinarith only [h, h']

/-- Lemma 3.4 supplies the precise uniform bound needed by the linked disk transfer. -/
theorem exists_source_linked_resolvent_upper :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ T t φ Y l : ℝ,
      4 ≤ T → Q₀ ≤ Real.log T → T ≤ |t| → |t| ≤ 2 * T →
      1 ≤ Y → Y ≤ Real.log T / 2 → |φ - t| ≤ Y →
      0 < l → l ≤ 1 / 80 → 1 ≤ l * Y →
      (∑' p : XiZero,
        (1 / ((((1 + 20 * l * Real.log T / Y : ℝ) : ℂ) +
          (φ : ℂ) * I) - xiZeroPoint p)).re) ≤ 5 * Real.log T / 9 := by
  obtain ⟨C, hC, hsource⟩ := exists_source_zero_sum_upper
  let Q₀ := 80 * (C + Real.log 5 / 2 + 1)
  have hlog5 : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)
  have hQ₀ : 1 ≤ Q₀ := by dsimp only [Q₀]; linarith
  refine ⟨Q₀, hQ₀, ?_⟩
  intro T t φ Y l hT4 hQlarge ht ht2 hY1 hYQ hφ hl hl80 hlY
  have hT : 0 < T := by linarith
  have hY : 0 < Y := by linarith
  have hQ : 0 < Real.log T := by linarith
  have hQT : Real.log T ≤ T := Real.log_le_self hT.le
  have hYhalf : Y ≤ T / 2 := by linarith
  have hφlower : 2 ≤ |φ| := by
    have h := abs_add_le φ (t - φ)
    have he : φ + (t - φ) = t := by ring
    rw [he, abs_sub_comm t φ] at h
    linarith
  have hφupper : |φ| ≤ 3 * T := by
    have h := abs_add_le (φ - t) t
    simp only [sub_add_cancel] at h
    linarith
  let a := 20 * l * Real.log T / Y
  have ha : 0 < a := by dsimp only [a]; positivity
  have haQ : a ≤ Real.log T / 4 := by
    apply (div_le_iff₀ hY).mpr
    have h := mul_le_mul_of_nonneg_right hl80 hQ.le
    have h' := mul_le_mul_of_nonneg_left hY1 (div_nonneg hQ.le (by norm_num : (0 : ℝ) ≤ 4))
    nlinarith only [h, h']
  have haT : a ≤ T := by linarith
  have hlog : Real.log (2 + a + |φ|) ≤ Real.log T + Real.log 5 := by
    have h := Real.log_le_log (by positivity : 0 < 2 + a + |φ|)
      (by linarith : 2 + a + |φ| ≤ 5 * T)
    rw [Real.log_mul (by norm_num : (5 : ℝ) ≠ 0) hT.ne'] at h
    linarith
  have hinv := source_outer_shift_reciprocal hl hY hYQ hlY
  have hu := (hsource a φ ha hφlower).2
  have hconstant : C + Real.log 5 / 2 ≤ Real.log T / 80 := by
    dsimp only [Q₀] at hQlarge
    linarith
  change (∑' p : XiZero, (1 / ((((1 + a : ℝ) : ℂ) +
    (φ : ℂ) * I) - xiZeroPoint p)).re) ≤ _
  change 1 / a ≤ Real.log T / 80 at hinv
  linarith

end
end DongWangWangZhang2026

