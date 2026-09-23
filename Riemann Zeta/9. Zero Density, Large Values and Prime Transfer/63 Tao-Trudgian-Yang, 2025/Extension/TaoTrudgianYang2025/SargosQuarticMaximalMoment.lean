import TaoTrudgianYang2025.SargosQuarticPrefixIntegral

/-!
# Robert--Sargos maximal-prefix fourth moment

The maximum is over every literal integer prefix of (N,2N].
Finite Fourier completion has a single endpoint-independent majorant.
Each completed mode uses the already proved, coefficient-uniform source
fourth moment. No maximal-moment estimate is a theorem parameter.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace TaoTrudgianYang2025

theorem norm_sargosQuarticPrefix_le_maximum {N H : ℕ}
    (z : ℤ → ℂ) (α γ : ℝ) (hH : H ≤ N) :
    ‖sargosQuarticPrefix N H z α γ‖ ≤ sargosQuarticPrefixMaximum N z α γ := by
  exact Finset.le_sup' (fun H => ‖sargosQuarticPrefix N H z α γ‖)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hH))

theorem sargosQuartic_maximal_fourth_moment {N : ℕ} (hN : 1 ≤ N) (z : ℤ → ℂ)
    (hz : ∀ n ∈ sargosSourceInterval N, ‖z n‖ ≤ 1)
    {Δ : ℝ} (hΔ : 1/(N : ℝ) ≤ Δ) :
    (∫ α in Icc (0 : ℝ) Δ,
      ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
        (sargosQuarticPrefixMaximum N z α γ)^4) ≤
          10616832*Δ/(N : ℝ)*(1+Real.log N)^5 := by
  letI : NeZero N := ⟨by omega⟩
  let B : ℝ := ∑ k : ZMod N, sargosPrefixMajorant k
  let C : ℝ := 131072*Δ/(N : ℝ)*(1+Real.log N)
  have hB : 0 ≤ B := Finset.sum_nonneg (fun k hk => sargosPrefixMajorant_nonneg k)
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hΔp : 0 < Δ := lt_of_lt_of_le (by positivity) hΔ
  have hlog := Real.log_nonneg hNr
  have hC : 0 ≤ C := by dsimp [C]; positivity
  calc
    _ ≤ B^3*(∑ k : ZMod N, sargosPrefixMajorant k*
        (∫ α in Icc (0 : ℝ) Δ,
          ∫ γ in Icc (-(1/(N : ℝ)^3)) (1/(N : ℝ)^3),
            ‖sargosQuarticSum N (sargosQuarticTwist z k) α γ‖^4)) :=
      sargosQuarticPrefix_rectangle_le_completed (N := N) z 0 Δ _ _
    _ ≤ B^3*(∑ k : ZMod N, sargosPrefixMajorant k*C) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB 3)
      apply Finset.sum_le_sum
      intro k hk
      apply mul_le_mul_of_nonneg_left _ (sargosPrefixMajorant_nonneg k)
      exact sargosQuartic_fourth_moment hN (sargosQuarticTwist z k)
        (sargosQuarticTwist_norm_le_one hz k) hΔ
    _ = B^4*C := by
      rw [← Finset.sum_mul]
      dsimp [B]
      ring
    _ ≤ (3*(1+Real.log N))^4*C :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB
        (sum_sargosPrefixMajorant_le_log (N := N)) 4) hC
    _ = _ := by dsimp [C]; ring

end TaoTrudgianYang2025
