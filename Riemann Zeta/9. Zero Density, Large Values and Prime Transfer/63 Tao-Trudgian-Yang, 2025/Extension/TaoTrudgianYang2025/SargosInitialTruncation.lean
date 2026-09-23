import TaoTrudgianYang2025.SargosInitialMomentTransfer
import Mathlib.Data.Nat.Log

/-! Exact zero-padding and power-of-two covers of initial integer intervals. -/

noncomputable section

open GafniTao
open scoped BigOperators

namespace TaoTrudgianYang2025

def sargosInitialCutoff (N : ℕ) (z : ℤ → ℂ) (n : ℤ) : ℂ :=
  if n ≤ (N:ℤ) then z n else 0

theorem sargosInitialCutoff_unit (N P : ℕ) (z : ℤ → ℂ)
    (hz : ∀ n ∈ Finset.Ioc (0:ℤ) N, ‖z n‖ ≤ 1) :
    ∀ n ∈ Finset.Ioc (0:ℤ) P, ‖sargosInitialCutoff N z n‖ ≤ 1 := by
  intro n hn
  by_cases h : n ≤ (N:ℤ)
  · rw [sargosInitialCutoff,if_pos h]
    exact hz n (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,h⟩)
  · simp [sargosInitialCutoff,h]

theorem sargosInitialQuarticSum_cutoff {N P : ℕ} (hNP : N ≤ P)
    (z : ℤ → ℂ) (α γ : ℝ) :
    sargosInitialQuarticSum P (sargosInitialCutoff N z) α γ =
      sargosInitialQuarticSum N z α γ := by
  classical
  have hs : Finset.Ioc (0:ℤ) N ⊆ Finset.Ioc (0:ℤ) P := by
    intro n hn
    have hnp : (N:ℤ) ≤ P := by exact_mod_cast hNP
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans hnp⟩
  unfold sargosInitialQuarticSum
  calc
    _ = ∑ n ∈ Finset.Ioc (0:ℤ) N,
        sargosInitialCutoff N z n*fordAdditiveCharacter ((n:ℝ)^2*α+(n:ℝ)^4*γ) := by
      symm
      apply Finset.sum_subset hs
      intro n hn hnot
      have hnN : ¬ n ≤ (N:ℤ) := by
        intro h
        exact hnot (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,h⟩)
      simp [sargosInitialCutoff,hnN]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sargosInitialCutoff,if_pos (Finset.mem_Ioc.mp hn).2]

theorem sargos_initial_dyadic_cover {N : ℕ} (hN : 1 ≤ N) :
    ∃ K : ℕ, N ≤ 2^(K+1) ∧ 2^(K+1) ≤ 2*N := by
  refine ⟨Nat.log 2 N,(Nat.lt_pow_succ_log_self (by norm_num) N).le,?_⟩
  have h := Nat.pow_log_le_self 2 (by omega : N ≠ 0)
  rw [pow_succ]
  omega

theorem sargos_dyadic_count_log (K : ℕ) :
    (K:ℝ)+1 = Real.log (((2^(K+1):ℕ):ℝ))/Real.log 2 := by
  rw [Nat.cast_pow,Nat.cast_ofNat,Real.log_pow]
  have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  field_simp
  push_cast
  ring

theorem sargos_dyadic_count_six_le_rpow (K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ((K:ℝ)+1)^6 ≤
      ((1/Real.log 2)*(1+6/ε))^6*((2^(K+1):ℕ):ℝ)^ε := by
  let P : ℝ := ((2^(K+1):ℕ):ℝ)
  have hP : 1 ≤ P := by
    dsimp [P]
    have hp : 0 < (2^(K+1):ℕ) := by positivity
    exact_mod_cast (show 1 ≤ (2^(K+1):ℕ) by omega)
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : (K:ℝ)+1 ≤ (1/Real.log 2)*(1+Real.log P) := by
    rw [sargos_dyadic_count_log]
    dsimp [P]
    apply (div_le_iff₀ hl).mpr
    field_simp
    linarith
  have hp := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ (K:ℝ)+1) hc 6
  have hr := sargos_log_six_le_rpow hP hε
  calc
    _ ≤ ((1/Real.log 2)*(1+Real.log P))^6 := hp
    _ = (1/Real.log 2)^6*(1+Real.log P)^6 := mul_pow _ _ _
    _ ≤ (1/Real.log 2)^6*((1+6/ε)^6*P^ε) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = _ := by ring

end TaoTrudgianYang2025
