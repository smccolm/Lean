import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace RiemannZeta.GuthMaynard

lemma denom_pos (σ : ℝ) (hσ : 7/10 ≤ σ) : 0 < 6 + 10 * σ := by linarith

noncomputable def alpha (σ : ℝ) : ℝ := (15 * σ - 9) / (6 + 10 * σ)
noncomputable def final_exponent (σ : ℝ) : ℝ := 15 * (1 - σ) / (3 + 5 * σ)

lemma exists_k_bound (N T : ℝ) (hN : 1 < N) (hT : 1 < T) (σ : ℝ) (hσ : 7/10 ≤ σ) :
  (N ≤ T ^ (5 / (6 + 10 * σ))) →
  ∃ (k : ℕ), k ≥ 1 ∧ (N ^ (k : ℝ) ≤ T ^ (15 / (6 + 10 * σ))) ∧ (T ^ (15 / (6 + 10 * σ)) < N ^ ((k : ℝ) + 1)) := by
  intro hNT
  set A := 15 / (6 + 10 * σ)
  set d := 6 + 10 * σ
  have hd : 0 < d := denom_pos σ hσ
  have hTpos : 0 < T := by linarith
  have hNpos : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hlogT : 0 < Real.log T := Real.log_pos hT

  have h1 : Real.log N ≤ Real.log (T ^ (5 / d)) := (Real.log_le_log_iff hNpos (Real.rpow_pos_of_pos hTpos _)).mpr hNT
  have h2 : Real.log (T ^ (5 / d)) = (5 / d) * Real.log T := Real.log_rpow hTpos (5 / d)
  have h3 : Real.log N ≤ (5 / d) * Real.log T := by linarith

  set X := A * Real.log T / Real.log N
  have hA_pos : 0 < A := div_pos (by positivity) hd
  have hX_pos : 0 < X := div_pos (mul_pos hA_pos hlogT) hlogN
  
  have X_ge_3 : 3 ≤ X := by
    have mul_logN_le : 3 * Real.log N ≤ A * Real.log T := by
      calc 3 * Real.log N ≤ 3 * ((5 / d) * Real.log T) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (15 / d) * Real.log T := by ring
      _ = A * Real.log T := by rfl
    exact (le_div_iff₀ hlogN).mpr mul_logN_le

  use Nat.floor X
  have hk_bounds : (Nat.floor X : ℝ) ≤ X ∧ X < (Nat.floor X : ℝ) + 1 := by
    refine ⟨Nat.floor_le (by linarith), Nat.lt_floor_add_one X⟩
  
  have hk_ge_1 : 1 ≤ Nat.floor X := by
    have h_floor : 3 ≤ Nat.floor X := Nat.le_floor X_ge_3
    omega

  refine ⟨hk_ge_1, ?_, ?_⟩
  · have h4 : (Nat.floor X : ℝ) * Real.log N ≤ X * Real.log N := mul_le_mul_of_nonneg_right hk_bounds.1 (by positivity)
    have h5 : X * Real.log N = A * Real.log T := div_mul_cancel₀ (A * Real.log T) (ne_of_gt hlogN)
    have h6 : (Nat.floor X : ℝ) * Real.log N ≤ A * Real.log T := by linarith
    have h7 : Real.log (N ^ (Nat.floor X : ℝ)) = (Nat.floor X : ℝ) * Real.log N := Real.log_rpow hNpos (Nat.floor X : ℝ)
    have h8 : Real.log (T ^ A) = A * Real.log T := Real.log_rpow hTpos A
    rw [←h7, ←h8] at h6
    exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hTpos _)).mp h6
  · have h4 : X * Real.log N < ((Nat.floor X : ℝ) + 1) * Real.log N := mul_lt_mul_of_pos_right hk_bounds.2 hlogN
    have h5 : X * Real.log N = A * Real.log T := div_mul_cancel₀ (A * Real.log T) (ne_of_gt hlogN)
    have h6 : A * Real.log T < ((Nat.floor X : ℝ) + 1) * Real.log N := by linarith
    have h7 : Real.log (N ^ ((Nat.floor X : ℝ) + 1)) = ((Nat.floor X : ℝ) + 1) * Real.log N := Real.log_rpow hNpos _
    have h8 : Real.log (T ^ A) = A * Real.log T := Real.log_rpow hTpos A
    rw [←h7, ←h8] at h6
    exact (Real.log_lt_log_iff (Real.rpow_pos_of_pos hTpos _) (Real.rpow_pos_of_pos hNpos _)).mp h6

end RiemannZeta.GuthMaynard
