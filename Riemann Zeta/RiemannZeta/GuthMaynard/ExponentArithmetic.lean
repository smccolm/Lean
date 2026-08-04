import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace RiemannZeta.GuthMaynard

lemma denom_pos (σ : ℝ) (hσ : 7/10 ≤ σ) : 0 < 6 + 10 * σ := by linarith

noncomputable def alpha (σ : ℝ) : ℝ := 15 * (1 - σ) / ((3 + 5 * σ) * (18/5 - 4 * σ))
noncomputable def final_exponent (σ : ℝ) : ℝ := 15 * (1 - σ) / (3 + 5 * σ)

lemma exists_k_bound (N T : ℝ) (hN : 1 < N) (hT : 1 < T) (σ : ℝ) (hσ : 7/10 ≤ σ) :
  (N ≤ T ^ (5 / (6 + 10 * σ))) →
  ∃ (k : ℕ), k ≥ 3 ∧ (T ^ (10 / (6 + 10 * σ)) ≤ N ^ (k : ℝ)) ∧ (N ^ (k : ℝ) ≤ T ^ (15 / (6 + 10 * σ))) := by
  intro hNT
  set d := 6 + 10 * σ
  have hd : 0 < d := denom_pos σ hσ
  have hTpos : 0 < T := by linarith
  have hNpos : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hlogT : 0 < Real.log T := Real.log_pos hT

  have h1 : Real.log N ≤ Real.log (T ^ (5 / d)) := (Real.log_le_log_iff hNpos (Real.rpow_pos_of_pos hTpos _)).mpr hNT
  have h2 : Real.log (T ^ (5 / d)) = (5 / d) * Real.log T := Real.log_rpow hTpos (5 / d)
  have h3 : Real.log N ≤ (5 / d) * Real.log T := by linarith

  set X := (15 / d) * Real.log T / Real.log N
  have hA_pos : 0 < 15 / d := div_pos (by positivity) hd
  have hX_pos : 0 < X := div_pos (mul_pos hA_pos hlogT) hlogN
  
  have X_ge_3 : 3 ≤ X := by
    have mul_logN_le : 3 * Real.log N ≤ (15 / d) * Real.log T := by
      calc 3 * Real.log N ≤ 3 * ((5 / d) * Real.log T) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (15 / d) * Real.log T := by ring
    exact (le_div_iff₀ hlogN).mpr mul_logN_le

  use Nat.floor X
  have hk_bounds : (Nat.floor X : ℝ) ≤ X ∧ X < (Nat.floor X : ℝ) + 1 := by
    refine ⟨Nat.floor_le (by linarith), Nat.lt_floor_add_one X⟩
  
  have hk_ge_3 : 3 ≤ Nat.floor X := Nat.le_floor X_ge_3

  refine ⟨hk_ge_3, ?_, ?_⟩
  · have h4 : X - 1 < (Nat.floor X : ℝ) := by linarith
    have h5 : (X - 1) * Real.log N < (Nat.floor X : ℝ) * Real.log N := mul_lt_mul_of_pos_right h4 hlogN
    have h6 : X * Real.log N - Real.log N < (Nat.floor X : ℝ) * Real.log N := by
      calc X * Real.log N - Real.log N = (X - 1) * Real.log N := by ring
      _ < (Nat.floor X : ℝ) * Real.log N := h5
    have h7 : X * Real.log N = (15 / d) * Real.log T := div_mul_cancel₀ _ (ne_of_gt hlogN)
    have h8 : (15 / d) * Real.log T - Real.log N < (Nat.floor X : ℝ) * Real.log N := by linarith
    have h9 : (10 / d) * Real.log T ≤ (15 / d) * Real.log T - Real.log N := by
      calc (10 / d) * Real.log T = (15 / d) * Real.log T - (5 / d) * Real.log T := by ring
      _ ≤ (15 / d) * Real.log T - Real.log N := sub_le_sub_left h3 _
    have h10 : (10 / d) * Real.log T ≤ (Nat.floor X : ℝ) * Real.log N := by linarith
    have h11 : Real.log (T ^ (10 / d)) = (10 / d) * Real.log T := Real.log_rpow hTpos (10 / d)
    have h12 : Real.log (N ^ (Nat.floor X : ℝ)) = (Nat.floor X : ℝ) * Real.log N := Real.log_rpow hNpos (Nat.floor X : ℝ)
    rw [←h11, ←h12] at h10
    exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hTpos _) (Real.rpow_pos_of_pos hNpos _)).mp h10
  · have h4 : (Nat.floor X : ℝ) * Real.log N ≤ X * Real.log N := mul_le_mul_of_nonneg_right hk_bounds.1 (by positivity)
    have h5 : X * Real.log N = (15 / d) * Real.log T := div_mul_cancel₀ _ (ne_of_gt hlogN)
    have h6 : (Nat.floor X : ℝ) * Real.log N ≤ (15 / d) * Real.log T := by linarith
    have h7 : Real.log (N ^ (Nat.floor X : ℝ)) = (Nat.floor X : ℝ) * Real.log N := Real.log_rpow hNpos (Nat.floor X : ℝ)
    have h8 : Real.log (T ^ (15 / d)) = (15 / d) * Real.log T := Real.log_rpow hTpos (15 / d)
    rw [←h7, ←h8] at h6
    exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hTpos _)).mp h6

lemma k_equals_2_bound (N T : ℝ) (hN : 1 < N) (hT : 1 < T) (σ : ℝ) (hσ : 7/10 ≤ σ) :
  (T ^ (5 / (6 + 10 * σ)) < N) →
  (T ^ (10 / (6 + 10 * σ)) < N ^ (2 : ℝ)) := by
  intro hNT
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
