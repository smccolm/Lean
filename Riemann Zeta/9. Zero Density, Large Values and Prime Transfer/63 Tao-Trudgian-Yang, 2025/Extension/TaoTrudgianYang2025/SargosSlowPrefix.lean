import TaoTrudgianYang2025.SargosSlowAbel

/-! The literal perturbed quartic prefixes and their pointwise Abel majorant. -/

noncomputable section

open GafniTao Set
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosSlowQuarticPrefix (N H : ℕ) (z : ℤ → ℂ) (α γ : ℝ) (φ : ℝ → ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (N : ℤ) ((N : ℤ)+H),
    z n*fordAdditiveCharacter ((n : ℝ)^2*α+(n : ℝ)^4*γ+φ n)

def sargosSlowQuarticMaximum (N : ℕ) (z : ℤ → ℂ) (α γ : ℝ) (φ : ℝ → ℝ) : ℝ :=
  (Finset.range (N+1)).sup' (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero N))
    (fun H => ‖sargosSlowQuarticPrefix N H z α γ φ‖)

theorem sargosSlowQuarticPrefix_eq_range (N H : ℕ) (z : ℤ → ℂ)
    (α γ : ℝ) (φ : ℝ → ℝ) :
    sargosSlowQuarticPrefix N H z α γ φ =
      ∑ j ∈ Finset.range H, fordAdditiveCharacter (φ ((N : ℝ)+j+1))*
        (z ((N : ℤ)+j+1)*
          fordAdditiveCharacter (((N : ℤ)+j+1 : ℤ)^2*α+((N : ℤ)+j+1 : ℤ)^4*γ)) := by
  rw [sargosSlowQuarticPrefix,sargos_sum_Ioc_eq_range]
  apply Finset.sum_congr rfl
  intro j hj
  rw [fordAdditiveCharacter_add]
  push_cast
  ring

theorem sargosSlowQuarticMaximum_attained (N : ℕ) (z : ℤ → ℂ)
    (α γ : ℝ) (φ : ℝ → ℝ) :
    ∃ H : ℕ, H ≤ N ∧
      sargosSlowQuarticMaximum N z α γ φ = ‖sargosSlowQuarticPrefix N H z α γ φ‖ := by
  obtain ⟨H,hH,he⟩ := Finset.exists_mem_eq_sup'
    (Finset.nonempty_range_iff.mpr (Nat.succ_ne_zero N))
    (fun H => ‖sargosSlowQuarticPrefix N H z α γ φ‖)
  exact ⟨H,Nat.le_of_lt_succ (Finset.mem_range.mp hH),he⟩

theorem sargosSlowQuarticMaximum_nonneg (N : ℕ) (z : ℤ → ℂ)
    (α γ : ℝ) (φ : ℝ → ℝ) :
    0 ≤ sargosSlowQuarticMaximum N z α γ φ := by
  obtain ⟨H,hH,he⟩ := sargosSlowQuarticMaximum_attained N z α γ φ
  rw [he]
  exact norm_nonneg _

theorem sargosSlowQuarticPrefix_norm_le {N H : ℕ} (hN : 1 ≤ N) (hH : H ≤ N)
    (z : ℤ → ℂ) (α γ : ℝ) {K : ℝ} (hK : 0 ≤ K) {φ φ' : ℝ → ℝ}
    (hφ : ∀ x ∈ Icc (N : ℝ) (2*N), HasDerivWithinAt φ (φ' x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' x‖ ≤ K/N) :
    ‖sargosSlowQuarticPrefix N H z α γ φ‖ ≤
      (1+2*Real.pi*K)*sargosQuarticPrefixMaximum N z α γ := by
  rw [sargosSlowQuarticPrefix_eq_range]
  apply sargos_norm_weighted_prefix_le hH
    (fun n => z n*fordAdditiveCharacter ((n : ℝ)^2*α+(n : ℝ)^4*γ))
    (fun j => fordAdditiveCharacter (φ ((N : ℝ)+j+1)))
    (sargosQuarticPrefixMaximum_nonneg N z α γ)
  · intro L hL
    exact norm_sargosQuarticPrefix_le_maximum z α γ hL
  · rw [sargos_character_norm]
  · simpa only [Nat.cast_add,Nat.cast_one] using sargos_slow_character_variation hN hH hK hφ hφ'

theorem sargosSlowQuarticMaximum_le {N : ℕ} (hN : 1 ≤ N)
    (z : ℤ → ℂ) (α γ : ℝ) {K : ℝ} (hK : 0 ≤ K) {φ φ' : ℝ → ℝ}
    (hφ : ∀ x ∈ Icc (N : ℝ) (2*N), HasDerivWithinAt φ (φ' x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' x‖ ≤ K/N) :
    sargosSlowQuarticMaximum N z α γ φ ≤
      (1+2*Real.pi*K)*sargosQuarticPrefixMaximum N z α γ := by
  obtain ⟨H,hH,he⟩ := sargosSlowQuarticMaximum_attained N z α γ φ
  rw [he]
  exact sargosSlowQuarticPrefix_norm_le hN hH z α γ hK hφ hφ'

theorem sargosSlowQuarticMaximum_pow_four_le {N : ℕ} (hN : 1 ≤ N)
    (z : ℤ → ℂ) (α γ : ℝ) {K : ℝ} (hK : 0 ≤ K) {φ φ' : ℝ → ℝ}
    (hφ : ∀ x ∈ Icc (N : ℝ) (2*N), HasDerivWithinAt φ (φ' x) (Icc (N : ℝ) (2*N)) x)
    (hφ' : ∀ x ∈ Icc (N : ℝ) (2*N), ‖φ' x‖ ≤ K/N) :
    (sargosSlowQuarticMaximum N z α γ φ)^4 ≤
      (1+2*Real.pi*K)^4*(sargosQuarticPrefixMaximum N z α γ)^4 := by
  simpa only [mul_pow] using pow_le_pow_left₀
    (sargosSlowQuarticMaximum_nonneg N z α γ φ)
    (sargosSlowQuarticMaximum_le hN z α γ hK hφ hφ') 4

end TaoTrudgianYang2025
