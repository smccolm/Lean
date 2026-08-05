import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace RiemannZeta.GuthMaynard

lemma denom_pos (σ : ℝ) (hσ : 7/10 ≤ σ) : 0 < 6 + 10 * σ := by linarith

noncomputable def alpha (σ : ℝ) : ℝ := 15 * (1 - σ) / ((3 + 5 * σ) * (18/5 - 4 * σ))
noncomputable def final_exponent (σ : ℝ) : ℝ := 15 * (1 - σ) / (3 + 5 * σ)

theorem k_selection (N T σ : ℝ) (hN : 1 < N) (hT : 1 < T) (hσ : 7/10 ≤ σ) :
  ∃ k : ℕ, k ≥ 2 ∧ 
    ((N ≤ T ^ (5 / (6 + 10 * σ)) → k ≥ 3 ∧ T ^ (10 / (6 + 10 * σ)) ≤ N ^ (k : ℝ) ∧ N ^ (k : ℝ) ≤ T ^ (15 / (6 + 10 * σ))) ∧ 
     (T ^ (5 / (6 + 10 * σ)) < N → k = 2 ∧ T ^ (10 / (6 + 10 * σ)) < N ^ (k : ℝ))) := by
  set d := 6 + 10 * σ
  have hd : 0 < d := denom_pos σ hσ
  have hTpos : 0 < T := by linarith
  have hNpos : 0 < N := by linarith
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hlogT : 0 < Real.log T := Real.log_pos hT

  by_cases hNT : N ≤ T ^ (5 / d)
  · -- N <= T^(5/d) branch
    have h1 : Real.log N ≤ Real.log (T ^ (5 / d)) := (Real.log_le_log_iff hNpos (Real.rpow_pos_of_pos hTpos _)).mpr hNT
    have h2 : Real.log (T ^ (5 / d)) = (5 / d) * Real.log T := Real.log_rpow hTpos (5 / d)
    rw [h2] at h1
    set A := (15 / d) * Real.log T / Real.log N
    have hApos : 0 ≤ A := by positivity
    set k := Nat.floor A
    use k
    
    have hk_le : (k : ℝ) ≤ A := Nat.floor_le hApos
    have hk_gt : A - 1 < (k : ℝ) := sub_lt_iff_lt_add.mpr (Nat.lt_floor_add_one A)

    have hA_ge_3 : (3 : ℝ) ≤ A := by
      have h_mul : (3 : ℝ) * Real.log N ≤ (15 / d) * Real.log T := by linarith
      exact (le_div_iff₀ hlogN).mpr h_mul

    have hk_ge_3 : k ≥ 3 := Nat.le_floor.mp hA_ge_3
    have hk_ge_2 : k ≥ 2 := by linarith

    refine ⟨hk_ge_2, ?_, ?_⟩
    · intro _
      refine ⟨hk_ge_3, ?_, ?_⟩
      · have h_k_log : (10 / d) * Real.log T ≤ (k : ℝ) * Real.log N := by
          have h_mul2 : (A - 1) * Real.log N < (k : ℝ) * Real.log N := mul_lt_mul_of_pos_right hk_gt hlogN
          have hA_mul : A * Real.log N = (15 / d) * Real.log T := div_mul_cancel₀ _ (ne_of_gt hlogN)
          have h_eq : (A - 1) * Real.log N = (15 / d) * Real.log T - Real.log N := by
            calc (A - 1) * Real.log N = A * Real.log N - Real.log N := by ring
            _ = (15 / d) * Real.log T - Real.log N := by rw [hA_mul]
          linarith
        have h6 : Real.log (T ^ (10 / d)) = (10 / d) * Real.log T := Real.log_rpow hTpos (10 / d)
        have h7 : Real.log (N ^ (k : ℝ)) = (k : ℝ) * Real.log N := Real.log_rpow hNpos (k : ℝ)
        rw [←h6, ←h7] at h_k_log
        exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hTpos _) (Real.rpow_pos_of_pos hNpos _)).mp h_k_log
        
      · have h_k_log2 : (k : ℝ) * Real.log N ≤ (15 / d) * Real.log T := by
          have h_mul3 : (k : ℝ) * Real.log N ≤ A * Real.log N := mul_le_mul_of_nonneg_right hk_le (le_of_lt hlogN)
          have hA_mul2 : A * Real.log N = (15 / d) * Real.log T := div_mul_cancel₀ _ (ne_of_gt hlogN)
          linarith
        have h8 : Real.log (T ^ (15 / d)) = (15 / d) * Real.log T := Real.log_rpow hTpos (15 / d)
        have h9 : Real.log (N ^ (k : ℝ)) = (k : ℝ) * Real.log N := Real.log_rpow hNpos (k : ℝ)
        rw [←h8, ←h9] at h_k_log2
        exact (Real.log_le_log_iff (Real.rpow_pos_of_pos hNpos _) (Real.rpow_pos_of_pos hTpos _)).mp h_k_log2

    · intro hContra
      exfalso
      linarith

  · -- N > T^(5/d) branch
    use 2
    have hk_ge_2 : 2 ≥ 2 := by norm_num
    refine ⟨hk_ge_2, ?_, ?_⟩
    · intro hContra
      exfalso
      linarith
    · intro _
      refine ⟨rfl, ?_⟩
      push_neg at hNT
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
