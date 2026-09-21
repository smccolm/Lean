import TaoTrudgianYang2025.AtkinsonMaximalGram
import GuthMaynard.DFIErrorTerms

/-!
# Uniform arithmetic energy of the actual Atkinson coefficient block

The native divisor bound gives C_epsilon M^(1+epsilon) for every block
[M,M+N) with N<=M. This is an epsilon-power estimate, not an assertion
of a sharp logarithmic divisor-square asymptotic.
-/

noncomputable section

open Complex
open RiemannZeta.GuthMaynard

namespace TaoTrudgianYang2025

theorem exists_atkinsonBlockCoefficientEnergy_le {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m N : ℕ, 0 < m → N ≤ m →
      atkinsonBlockCoefficientEnergy m N ≤ C*(m:ℝ)^(1+ε) := by
  obtain ⟨D,hD,hdiv⟩ := exists_norm_divisorWeight_le_rpow (ε/2) (by linarith)
  refine ⟨D^2*(2:ℝ)^ε,by positivity,?_⟩
  intro m N hm hN
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have h2m : (0:ℝ) < 2*(m:ℝ) := by positivity
  have hterm (i : ℕ) (hi : i ∈ Finset.range N) :
      ‖divisorWeight (m+i)‖^2 ≤ D^2*(2:ℝ)^ε*(m:ℝ)^ε := by
    have hiN := Finset.mem_range.mp hi
    have hn : 0 < m+i := by omega
    have hnR : ((m+i:ℕ):ℝ) ≤ 2*(m:ℝ) := by
      exact_mod_cast (show m+i ≤ 2*m by omega)
    have hb := (hdiv (m+i) hn).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hnR (by linarith : 0 ≤ ε/2)) hD.le)
    apply (pow_le_pow_left₀ (norm_nonneg _) hb 2).trans_eq
    rw [mul_pow,sq ((2*(m:ℝ))^(ε/2)),← Real.rpow_add h2m,
      show ε/2+ε/2 = ε by ring,Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hmR.le]
    ring
  have hNR : (N:ℝ) ≤ m := by exact_mod_cast hN
  calc
    _ ≤ ∑ i ∈ Finset.range N, D^2*(2:ℝ)^ε*(m:ℝ)^ε := Finset.sum_le_sum hterm
    _ = (N:ℝ)*(D^2*(2:ℝ)^ε*(m:ℝ)^ε) := by simp
    _ ≤ (m:ℝ)*(D^2*(2:ℝ)^ε*(m:ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hNR (by positivity)
    _ = (D^2*(2:ℝ)^ε)*(m:ℝ)^(1+ε) := by
      rw [Real.rpow_add hmR,Real.rpow_one]
      ring

theorem exists_sum_atkinsonPhaseBlockMax_sq_le_arithmeticGram {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ m N : ℕ, 0 < m → N ≤ m → ∀ W : Finset ℝ,
      (∑ t ∈ W, atkinsonPhaseBlockMax t m N)^2 ≤
        C*(m:ℝ)^(1+ε)*∑ t ∈ W, ∑ u ∈ W, atkinsonPrefixGramMax m N t u := by
  obtain ⟨C,hC,henergy⟩ := exists_atkinsonBlockCoefficientEnergy_le hε
  refine ⟨C,hC,?_⟩
  intro m N hm hN W
  apply (sum_atkinsonPhaseBlockMax_sq_le_gramMax m N W).trans
  apply mul_le_mul_of_nonneg_right (henergy m N hm hN)
  exact Finset.sum_nonneg (fun t _ => Finset.sum_nonneg (fun u _ =>
    atkinsonPrefixGramMax_nonneg m N t u))

end TaoTrudgianYang2025
