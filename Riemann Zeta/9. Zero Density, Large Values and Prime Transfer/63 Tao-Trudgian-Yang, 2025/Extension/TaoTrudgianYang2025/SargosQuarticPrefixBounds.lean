import TaoTrudgianYang2025.SargosQuarticCompletion

/-! Uniform finite bounds for the literal prefix maximum. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticPrefixMaximum_attained (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    ∃ H : ℕ, H ≤ N ∧
      sargosQuarticPrefixMaximum N z α γ = ‖sargosQuarticPrefix N H z α γ‖ := by
  obtain ⟨H,hH,he⟩ := Finset.exists_mem_eq_sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero N))
    (fun H => ‖sargosQuarticPrefix N H z α γ‖)
  exact ⟨H,Nat.le_of_lt_succ (Finset.mem_range.mp hH),he⟩

theorem sargosQuarticPrefixMaximum_nonneg (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    0 ≤ sargosQuarticPrefixMaximum N z α γ := by
  obtain ⟨H,hH,he⟩ := sargosQuarticPrefixMaximum_attained N z α γ
  rw [he]
  exact norm_nonneg _

theorem norm_sargosQuarticPrefix_le_sum_norm {N H : ℕ} (hH : H ≤ N)
    (z : ℤ → ℂ) (α γ : ℝ) :
    ‖sargosQuarticPrefix N H z α γ‖ ≤ ∑ n ∈ sargosSourceInterval N, ‖z n‖ := by
  unfold sargosQuarticPrefix
  calc
    _ ≤ ∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+H),
        ‖z n*fordAdditiveCharacter ((n : ℝ)^2*α+(n : ℝ)^4*γ)‖ := norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+H), ‖z n‖ := by
      simp only [norm_mul,sargos_character_norm,mul_one]
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [Finset.mem_Ioc] at hn
        rw [sargosSourceInterval,Finset.mem_Ioc]
        constructor <;> omega
      · intro n hn hnot
        exact norm_nonneg _

theorem sargosQuarticPrefixMaximum_le_sum_norm (N : ℕ)
    (z : ℤ → ℂ) (α γ : ℝ) :
    sargosQuarticPrefixMaximum N z α γ ≤ ∑ n ∈ sargosSourceInterval N, ‖z n‖ := by
  obtain ⟨H,hH,he⟩ := sargosQuarticPrefixMaximum_attained N z α γ
  rw [he]
  exact norm_sargosQuarticPrefix_le_sum_norm hH z α γ

end TaoTrudgianYang2025
