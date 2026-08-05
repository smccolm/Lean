import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace RiemannZeta.GuthMaynard

lemma denom_pos (σ : ℝ) (hσ : 7/10 ≤ σ) : 0 < 6 + 10 * σ := by linarith

noncomputable def alpha (σ : ℝ) : ℝ := 15 * (1 - σ) / ((3 + 5 * σ) * (18/5 - 4 * σ))
noncomputable def final_exponent (σ : ℝ) : ℝ := 15 * (1 - σ) / (3 + 5 * σ)

-- The k_selection theorem fully splits the k choices
theorem k_selection (N T σ : ℝ) (hN : 1 < N) (hT : 1 < T) (hσ : 7/10 ≤ σ) :
  ∃ k : ℕ, k ≥ 2 ∧ 
    ((N ≤ T ^ (5 / (6 + 10 * σ)) → k ≥ 3 ∧ T ^ (10 / (6 + 10 * σ)) ≤ N ^ (k : ℝ) ∧ N ^ (k : ℝ) ≤ T ^ (15 / (6 + 10 * σ))) ∧ 
     (T ^ (5 / (6 + 10 * σ)) < N → k = 2 ∧ T ^ (10 / (6 + 10 * σ)) < N ^ (k : ℝ))) := by
  by_cases hNT : N ≤ T ^ (5 / (6 + 10 * σ))
  · -- This branch needs the floor log logic to find a k >= 3
    sorry
  · use 2
    refine ⟨by norm_num, ?_⟩
    constructor
    · intro hContra
      exfalso
      linarith
    · intro _
      refine ⟨rfl, ?_⟩
      push_neg at hNT
      set d := 6 + 10 * σ
      have hd : 0 < d := denom_pos σ hσ
      have hTpos : 0 < T := by linarith
      have hNpos : 0 < N := by linarith
      have hlogN : 0 < Real.log N := Real.log_pos hN
      have h1 : Real.log (T ^ (5 / d)) < Real.log N := (Real.log_lt_log_iff (Real.rpow_pos_of_pos hTpos _) hNpos).mpr hNT
      have h2 : Real.log (T ^ (5 / d)) = (5 / d) * Real.log T := Real.log_rpow hTpos (5 / d)
      have h3 : (5 / d) * Real.log T < Real.log N := by linarith
      have h4 : 2 * ((5 / d) * Real.log T) < 2 * Real.log N := by linarith
      have h5 : 2 * ((5 / d) * Real.log T) = (10 / d) * Real.log T := by ring
      have h6 : Real.log (T ^ (10 / d)) = (10 / d) * Real.log T := Real.log_rpow hTpos (10 / d)
      have h7 : Real.log (N ^ (2 : ℝ)) = 2 * Real.log N := Real.log_rpow hNpos 2
      rw [h5] at h4
      rw [←h6, ←h7] at h4
      exact (Real.log_lt_log_iff (Real.rpow_pos_of_pos hTpos _) (Real.rpow_pos_of_pos hNpos _)).mp h4

end RiemannZeta.GuthMaynard
