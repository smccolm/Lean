import DongWangWangZhang2026.LocalWindowScale

/-!
# The small-x local zero-window consequence

This consumes the actual Theorem 1.1 and proves cancellation throughout
T^epsilon ≤ x ≤ sqrt T. The full polynomial range still requires the
independent large-x estimate.
-/

namespace DongWangWangZhang2026
noncomputable section
open Complex

/-- The complete small-range part of T2, with one absolute window displacement constant. -/
theorem exists_small_range_local_zero_cancellation :
    ∃ C : ℝ, 0 < C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
      ∃ T₀ : ℝ, 3 ≤ T₀ ∧ ∀ T t ε : ℝ,
        T₀ ≤ T → T ≤ |t| → |t| ≤ 2 * T →
        (Real.log T) ^ (-1 / 3 : ℝ) < ε →
        (∀ u : ℝ, |u - t| ≤ C * (Real.log T) ^ (1 / 100 : ℝ) →
          (zeroCountIn (sourceZeroWindow u δ) : ℝ) ≤ δ * ε ^ 2 * Real.log T / 400) →
        ∀ x : ℝ, T ^ ε ≤ x → x ≤ Real.sqrt T →
          ‖zetaSum x t‖ ≤ x / (Real.log x) ^ (1 / 100 : ℝ) := by
  obtain ⟨c, T₁, hc, hT₁, hmain⟩ := large_zeta_sum_forces_zero_disk
  refine ⟨c, hc, ?_⟩
  intro δ hδ hδ4
  obtain ⟨Q₀, hQ₀, hthreshold⟩ := exists_local_window_scale_threshold c hδ
  refine ⟨max T₁ (Real.exp Q₀), hT₁.trans (le_max_left _ _), ?_⟩
  intro T t ε hT₀ ht httop hε hwindows x hxlow hxtop
  have hTold : T₁ ≤ T := (le_max_left _ _).trans hT₀
  have hT3 : 3 ≤ T := hT₁.trans hTold
  have hT : 0 < T := by linarith
  have hQlarge : Q₀ ≤ Real.log T := by
    have h := Real.log_le_log (Real.exp_pos Q₀) ((le_max_right _ _).trans hT₀)
    simpa only [Real.log_exp] using h
  have hQ1 : 1 ≤ Real.log T := hQ₀.trans hQlarge
  have hQ : 0 < Real.log T := by linarith
  have hε0 : 0 < ε := (Real.rpow_pos_of_pos hQ _).trans hε
  have hx : 0 < x := (Real.rpow_pos_of_pos hT _).trans_le hxlow
  have hεY : ε * Real.log T ≤ Real.log x := by
    have h := Real.log_le_log (Real.rpow_pos_of_pos hT ε) hxlow
    simpa only [Real.log_rpow hT] using h
  have hY : 0 < Real.log x := (mul_pos hε0 hQ).trans_le hεY
  have hYQ : Real.log x ≤ Real.log T / 2 := by
    simpa only [Real.log_sqrt hT.le] using Real.log_le_log hx hxtop
  have hYpow : 0 < (Real.log x) ^ (1 / 100 : ℝ) := Real.rpow_pos_of_pos hY _
  by_contra hn
  have hlarge : x / (Real.log x) ^ (1 / 100 : ℝ) < ‖zetaSum x t‖ := lt_of_not_ge hn
  have hnorm : 0 < ‖zetaSum x t‖ := (div_pos hx hYpow).trans hlarge
  let N := x / ‖zetaSum x t‖
  have hN : 1 ≤ N := by
    apply (le_div_iff₀ hnorm).mpr
    simpa only [one_mul] using norm_zetaSum_le hx.le t
  have hNtop : N ≤ (Real.log x) ^ (1 / 100 : ℝ) := by
    apply (div_le_iff₀ hnorm).mpr
    have h := (div_lt_iff₀ hYpow).mp hlarge
    nlinarith only [h]
  have hsum : ‖zetaSum x t‖ = x / N := by
    dsimp only [N]
    field_simp
  obtain ⟨_, hroot, hLlow, hLtop, hradius, hdisplace⟩ :=
    source_local_window_scale hc hδ hδ4 hQ1 hε hεY hYQ hN hNtop (hthreshold _ hQlarge)
  have hxexp : Real.exp (Real.sqrt (Real.log T)) ≤ x := by
    simpa only [Real.exp_log hx] using Real.exp_le_exp.mpr hroot
  obtain ⟨φ, hφ, hcount⟩ := hmain T t x N hTold ht httop hxexp hxtop hN hNtop hsum
  have hu := hwindows φ (hφ.trans hdisplace)
  have hdisk := hcount (δ * ε ^ 2 * Real.log T) hLlow hLtop
  have htransfer : (zeroCountIn (sourceZeroDisk φ
      ((δ * ε ^ 2 * Real.log T) * Real.log T / (Real.log x) ^ (2 : ℕ))) : ℝ) ≤
      (zeroCountIn (sourceZeroWindow φ δ) : ℝ) := by
    exact_mod_cast zeroCountIn_disk_le_window φ hradius
  have hL : 0 < δ * ε ^ 2 * Real.log T := by positivity
  linarith

end
end DongWangWangZhang2026

