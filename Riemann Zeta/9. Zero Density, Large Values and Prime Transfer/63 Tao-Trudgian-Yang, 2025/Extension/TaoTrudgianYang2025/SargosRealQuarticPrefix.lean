import TaoTrudgianYang2025.SargosRealQuarticBlock

/-! Exact one-term extension of the literal natural prefix. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem sargosQuarticPrefix_succ (N H : ℕ) (z : ℤ → ℂ) (α γ : ℝ) :
    sargosQuarticPrefix N (H+1) z α γ =
      sargosQuarticPrefix N H z α γ+
        z ((N:ℤ)+H+1)*fordAdditiveCharacter
          ((((N:ℤ)+H+1:ℤ):ℝ)^2*α+(((N:ℤ)+H+1:ℤ):ℝ)^4*γ) := by
  have he : Finset.Ioc (N:ℤ) ((N:ℤ)+(H+1:ℕ)) =
      insert ((N:ℤ)+H+1) (Finset.Ioc (N:ℤ) ((N:ℤ)+H)) := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_insert]
    omega
  have hn : (N:ℤ)+H+1 ∉ Finset.Ioc (N:ℤ) ((N:ℤ)+H) := by
    simp only [Finset.mem_Ioc]
    omega
  unfold sargosQuarticPrefix
  rw [he,Finset.sum_insert hn,add_comm]

theorem sargosRealQuarticPrefix_norm_le {M : ℝ} (hM : 0 ≤ M) {H : ℕ}
    (hH : H ≤ sargosRealBlockLength M) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosRealSourceInterval M, ‖z n‖ ≤ 1) (α γ : ℝ) :
    ‖sargosRealQuarticPrefix M H z α γ‖ ≤ sargosQuarticPrefixMaximum ⌊M⌋₊ z α γ+1 := by
  let m := ⌊M⌋₊
  have hlength := sargosRealBlockLength_floor_bounds hM
  rw [sargosRealQuarticPrefix_eq_natural hM]
  by_cases hHm : H ≤ m
  · have hh := norm_sargosQuarticPrefix_le_maximum z α γ hHm
    linarith only [hh]
  · have hHe : H = m+1 := by omega
    have hf := Int.natCast_floor_eq_floor hM
    have hL := sargosRealBlockLength_cast hM
    have hn : (m:ℤ)+m+1 ∈ sargosRealSourceInterval M := by
      simp only [sargosRealSourceInterval,Finset.mem_Ioc]
      change (m:ℤ) = ⌊M⌋ at hf
      omega
    have hterm := hz _ hn
    change ‖sargosQuarticPrefix m H z α γ‖ ≤ _
    rw [hHe,sargosQuarticPrefix_succ]
    calc
      _ ≤ ‖sargosQuarticPrefix m m z α γ‖+
          ‖z ((m:ℤ)+m+1)*fordAdditiveCharacter
            ((((m:ℤ)+m+1:ℤ):ℝ)^2*α+(((m:ℤ)+m+1:ℤ):ℝ)^4*γ)‖ := norm_add_le _ _
      _ = ‖sargosQuarticPrefix m m z α γ‖+‖z ((m:ℤ)+m+1)‖ := by
        rw [norm_mul,sargos_character_norm,mul_one]
      _ ≤ _ := add_le_add (norm_sargosQuarticPrefix_le_maximum z α γ le_rfl) hterm

theorem sargosRealQuarticMaximum_nonneg (M : ℝ) (z : ℤ → ℂ) (α γ : ℝ) :
    0 ≤ sargosRealQuarticMaximum M z α γ := by
  apply le_trans (norm_nonneg (sargosRealQuarticPrefix M 0 z α γ))
  exact Finset.le_sup' (fun H => ‖sargosRealQuarticPrefix M H z α γ‖)
    (Finset.mem_range.mpr (Nat.succ_pos _))

theorem sargosRealQuarticMaximum_le_natural {M : ℝ} (hM : 0 ≤ M)
    (z : ℤ → ℂ) (hz : ∀ n ∈ sargosRealSourceInterval M, ‖z n‖ ≤ 1) (α γ : ℝ) :
    sargosRealQuarticMaximum M z α γ ≤ sargosQuarticPrefixMaximum ⌊M⌋₊ z α γ+1 := by
  apply Finset.sup'_le
  intro H hH
  exact sargosRealQuarticPrefix_norm_le hM
    (Nat.le_of_lt_succ (Finset.mem_range.mp hH)) z hz α γ

theorem sargosRealQuarticMaximum_sixth_le {M : ℝ} (hM : 0 ≤ M)
    (z : ℤ → ℂ) (hz : ∀ n ∈ sargosRealSourceInterval M, ‖z n‖ ≤ 1) (α γ : ℝ) :
    (sargosRealQuarticMaximum M z α γ)^6 ≤
      32*((sargosQuarticPrefixMaximum ⌊M⌋₊ z α γ)^6+1) := by
  apply (pow_le_pow_left₀ (sargosRealQuarticMaximum_nonneg M z α γ)
    (sargosRealQuarticMaximum_le_natural hM z hz α γ) 6).trans
  have hh := add_pow_le (sargosQuarticPrefixMaximum_nonneg ⌊M⌋₊ z α γ)
    (by norm_num : (0:ℝ) ≤ 1) 6
  norm_num at hh
  exact hh

end TaoTrudgianYang2025
