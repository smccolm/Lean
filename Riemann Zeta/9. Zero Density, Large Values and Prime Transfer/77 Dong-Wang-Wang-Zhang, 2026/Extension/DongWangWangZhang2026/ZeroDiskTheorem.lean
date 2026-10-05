import DongWangWangZhang2026.DiskZeroCount
import DongWangWangZhang2026.LinkedZeroSum

/-!
# Theorem 1.1: large zeta sums force an actual zero disk

One maximizing twist is selected before every admissible source scale.
The count uses all analytic multiplicity labels and the disk is open.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex

/-- The exact public source Theorem 1.1, for both height signs and every admissible scale. -/
theorem large_zeta_sum_forces_zero_disk :
    ∃ c T₀ : ℝ, 0 < c ∧ 3 ≤ T₀ ∧
      ∀ T t x N : ℝ, T₀ ≤ T → T ≤ |t| → |t| ≤ 2 * T →
        Real.exp (Real.sqrt (Real.log T)) ≤ x → x ≤ Real.sqrt T →
        1 ≤ N → N ≤ (Real.log x) ^ (1 / 100 : ℝ) → ‖zetaSum x t‖ = x / N →
        ∃ φ : ℝ, |φ - t| ≤ c * N ∧
          ∀ L : ℝ, c * N ^ (6 : ℕ) ≤ L → L ≤ Real.log x / 2 →
            L / 360 ≤ (zeroCountIn
              (sourceZeroDisk φ (L * Real.log T / (Real.log x) ^ (2 : ℕ))) : ℝ) := by
  obtain ⟨c₀, T₁, hc₀, hT₁, hforcing⟩ := exists_large_sum_weighted_zero_forcing
  obtain ⟨Q₀, hQ₀, hupper⟩ := exists_source_linked_resolvent_upper
  let c := 40 * max c₀ 1
  have hc : 0 < c := by dsimp only [c]; positivity
  have hc40 : 40 * c₀ ≤ c := mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)
  have hc1 : 40 ≤ c := by
    have h := mul_le_mul_of_nonneg_left (le_max_right c₀ 1) (by norm_num : (0 : ℝ) ≤ 40)
    simpa only [mul_one] using h
  have hcold : c₀ ≤ c := by linarith
  refine ⟨c, max T₁ (max 4 (Real.exp Q₀)), hc, hT₁.trans (le_max_left _ _), ?_⟩
  intro T t x N hT₀ ht httop hxlow hxtop hN hNtop hsum
  have hTold : T₁ ≤ T := (le_max_left _ _).trans hT₀
  have hT4 : 4 ≤ T := (le_max_left _ _).trans ((le_max_right _ _).trans hT₀)
  have hT : 0 < T := by linarith
  have hQlarge : Q₀ ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos Q₀)
      ((le_max_right _ _).trans ((le_max_right _ _).trans hT₀))
    simpa only [Real.log_exp] using h
  have hQ1 : 1 ≤ Real.log T := hQ₀.trans hQlarge
  have hx : 0 < x := (Real.exp_pos _).trans_le hxlow
  have hYroot : Real.sqrt (Real.log T) ≤ Real.log x := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hxlow
  have hY1 : 1 ≤ Real.log x := by
    have h : 1 ≤ Real.sqrt (Real.log T) := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hQ1
    exact h.trans hYroot
  have hY : 0 < Real.log x := by linarith
  have hYQ : Real.log x ≤ Real.log T / 2 := by
    simpa only [Real.log_sqrt hT.le] using Real.log_le_log hx hxtop
  have hN0 : 0 < N := by linarith
  have hN6 : 1 ≤ N ^ (6 : ℕ) := one_le_pow₀ hN
  obtain ⟨t₀, ht₀, _, hdisplace, hscales⟩ :=
    hforcing T t x N hTold ht httop hxlow hxtop hN hNtop hsum
  refine ⟨t - t₀, ?_, ?_⟩
  · have he : t - t₀ - t = -t₀ := by ring
    rw [he, abs_neg]
    exact hdisplace.trans (mul_le_mul_of_nonneg_right hcold hN0.le)
  · intro L hLlow hLtop
    let l := L / (40 * Real.log x)
    have hL : 0 < L := (mul_pos hc (pow_pos hN0 _)).trans_le hLlow
    have hl : 0 < l := by dsimp only [l]; positivity
    have hl80 : l ≤ 1 / 80 := by
      apply (div_le_iff₀ (by positivity : 0 < 40 * Real.log x)).mpr
      linarith
    have hlY : 1 ≤ l * Real.log x := by
      have he : l * Real.log x = L / 40 := by dsimp only [l]; field_simp
      rw [he]
      have h := mul_le_mul_of_nonneg_left hN6 hc.le
      linarith
    have hlow : c₀ * N ^ (6 : ℕ) / Real.log x ≤ l := by
      have h := mul_le_mul_of_nonneg_right hc40 (by positivity : 0 ≤ N ^ (6 : ℕ))
      dsimp only [l]
      apply (div_le_div_iff₀ hY (by positivity : 0 < 40 * Real.log x)).mpr
      nlinarith [mul_le_mul_of_nonneg_right (h.trans hLlow) hY.le]
    obtain ⟨η, hη, _, hforce⟩ := hscales l hlow (by linarith)
    have hφ : |t - t₀ - t| ≤ Real.log x := by
      simpa only [show t - t₀ - t = -t₀ by ring, abs_neg] using ht₀
    have hu := hupper T t (t - t₀) (Real.log x) l
      hT4 hQlarge ht httop hY1 hYQ hφ hl hl80 hlY
    have hcount := source_disk_count_of_weighted_forcing hl hY hYQ hη hforce hu
    have hradius : 40 * l * Real.log T / Real.log x =
        L * Real.log T / (Real.log x) ^ (2 : ℕ) := by
      dsimp only [l]
      field_simp
    have hleft : l * Real.log x / 9 = L / 360 := by
      dsimp only [l]
      field_simp
      norm_num
    rw [hradius, hleft] at hcount
    exact hcount

end
end DongWangWangZhang2026
