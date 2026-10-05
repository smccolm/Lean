import DongWangWangZhang2026.ZeroDiskTheorem

/-!
# Admissible source scale for the local-zero contradiction

The strict epsilon hypothesis and one delta-dependent threshold supply
all T1 scale conditions; no source zero estimate is assumed here.
-/

namespace DongWangWangZhang2026
noncomputable section
open Filter Real

/-- The fixed delta eventually absorbs the source sixth-power cutoff. -/
theorem exists_local_window_scale_threshold (c : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Q₀ : ℝ, 1 ≤ Q₀ ∧ ∀ Q : ℝ, Q₀ ≤ Q →
      c * Q ^ (3 / 50 : ℝ) ≤ δ * Q ^ (1 / 3 : ℝ) := by
  obtain ⟨Q₁, h₁⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 41 / 150)).eventually_ge_atTop (c / δ))
  refine ⟨max 1 Q₁, le_max_left _ _, ?_⟩
  intro Q hQ₀
  have hQ1 : 1 ≤ Q := (le_max_left _ _).trans hQ₀
  have hQ : 0 < Q := by linarith
  have h := h₁ Q ((le_max_right _ _).trans hQ₀)
  have hm := mul_le_mul_of_nonneg_right ((div_le_iff₀ hδ).mp h)
    (Real.rpow_nonneg hQ.le (3 / 50))
  have he : Q ^ (41 / 150 : ℝ) * Q ^ (3 / 50 : ℝ) = Q ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_add hQ]
    norm_num
  calc
    c * Q ^ (3 / 50 : ℝ) ≤ (Q ^ (41 / 150 : ℝ) * δ) * Q ^ (3 / 50 : ℝ) := hm
    _ = δ * Q ^ (1 / 3 : ℝ) := by rw [mul_assoc, mul_comm δ, ← mul_assoc, he]; ring

/-- Exact linked scale conclusions, retaining the strict epsilon hypothesis. -/
theorem source_local_window_scale {c δ ε Q Y N : ℝ}
    (hc : 0 < c) (hδ : 0 < δ) (hδ4 : δ ≤ 1 / 4) (hQ1 : 1 ≤ Q)
    (hε : Q ^ (-1 / 3 : ℝ) < ε) (hεY : ε * Q ≤ Y) (hYQ : Y ≤ Q / 2)
    (hN : 1 ≤ N) (hNY : N ≤ Y ^ (1 / 100 : ℝ))
    (hthreshold : c * Q ^ (3 / 50 : ℝ) ≤ δ * Q ^ (1 / 3 : ℝ)) :
    0 < ε ∧ Real.sqrt Q ≤ Y ∧
      c * N ^ (6 : ℕ) ≤ δ * ε ^ 2 * Q ∧
      δ * ε ^ 2 * Q ≤ Y / 2 ∧
      (δ * ε ^ 2 * Q) * Q / Y ^ (2 : ℕ) ≤ δ ∧
      c * N ≤ c * Q ^ (1 / 100 : ℝ) := by
  have hQ : 0 < Q := by linarith
  have hε0 : 0 < ε := (Real.rpow_pos_of_pos hQ _).trans hε
  have hε2 : ε ≤ 1 / 2 := by nlinarith
  have hY : 0 < Y := (mul_pos hε0 hQ).trans_le hεY
  have hYQ' : Y ≤ Q := by linarith
  have hpow : Q ^ (-1 / 3 : ℝ) * Q = Q ^ (2 / 3 : ℝ) := by
    calc
      _ = Q ^ (-1 / 3 : ℝ) * Q ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hQ]; norm_num
  have hroot : Real.sqrt Q ≤ Y := by
    have h := mul_lt_mul_of_pos_right hε hQ
    rw [hpow] at h
    have hroot' : Real.sqrt Q ≤ Q ^ (2 / 3 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
    exact hroot'.trans (h.le.trans hεY)
  have hNQ : N ≤ Q ^ (1 / 100 : ℝ) :=
    hNY.trans (Real.rpow_le_rpow hY.le hYQ' (by norm_num))
  have hN6 : N ^ (6 : ℕ) ≤ Q ^ (3 / 50 : ℝ) := by
    have h := pow_le_pow_left₀ (by linarith : 0 ≤ N) hNQ 6
    rw [← Real.rpow_mul_natCast hQ.le] at h
    norm_num at h
    exact h
  have hεsq : (Q ^ (-1 / 3 : ℝ)) ^ (2 : ℕ) < ε ^ (2 : ℕ) :=
    (sq_lt_sq₀ (Real.rpow_nonneg hQ.le _) hε0.le).mpr hε
  have hscaleId : (Q ^ (-1 / 3 : ℝ)) ^ (2 : ℕ) * Q = Q ^ (1 / 3 : ℝ) := by
    rw [← Real.rpow_mul_natCast hQ.le]
    calc
      _ = Q ^ ((-1 / 3 : ℝ) * 2) * Q ^ (1 : ℝ) := by rw [Real.rpow_one]; norm_num
      _ = _ := by rw [← Real.rpow_add hQ]; norm_num
  have hLlow : c * N ^ (6 : ℕ) ≤ δ * ε ^ 2 * Q := by
    have h := mul_lt_mul_of_pos_right hεsq hQ
    rw [hscaleId] at h
    have h' := mul_lt_mul_of_pos_left h hδ
    exact (mul_le_mul_of_nonneg_left hN6 hc.le).trans (hthreshold.trans (by nlinarith only [h']))
  have hLhi : δ * ε ^ 2 * Q ≤ Y / 2 := by
    have hde : δ * ε ≤ 1 / 8 := by nlinarith
    have h := mul_le_mul_of_nonneg_left hεY (by positivity : 0 ≤ δ * ε)
    have h' := mul_le_mul_of_nonneg_right hde hY.le
    nlinarith only [h, h', hY]
  have hradius : (δ * ε ^ 2 * Q) * Q / Y ^ (2 : ℕ) ≤ δ := by
    apply (div_le_iff₀ (sq_pos_of_pos hY)).mpr
    have hsq := (sq_le_sq₀ (mul_pos hε0 hQ).le hY.le).mpr hεY
    have h := mul_le_mul_of_nonneg_left hsq hδ.le
    nlinarith only [h]
  exact ⟨hε0, hroot, hLlow, hLhi, hradius, mul_le_mul_of_nonneg_left hNQ hc.le⟩

end
end DongWangWangZhang2026
