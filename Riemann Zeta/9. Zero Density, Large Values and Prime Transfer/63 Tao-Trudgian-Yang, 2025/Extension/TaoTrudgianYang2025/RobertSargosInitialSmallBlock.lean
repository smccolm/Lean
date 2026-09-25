import TaoTrudgianYang2025.RobertSargosSmallBlock
import TaoTrudgianYang2025.RobertSargosInitialDyadicLog

/-! Source-faithful initial dichotomy: the small block closes, or the selected block is large. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_initial_small_or_large_block
    (f : ℝ → ℝ) (M H : ℕ) {C lam : ℝ}
    (hC : 1 ≤ C) (hH : 2 ≤ H) (hHM : H ≤ M)
    (hlam : 0 < lam) (hlamSmall : lam ≤ 1/16) (hM : lam^(-(8:ℝ)/13) ≤ M)
    (hf : ∀ y ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc (1:ℝ) M, iteratedDeriv 4 f y ≤ C*lam) :
    ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖^2 ≤
        930*C*(Real.log H/Real.log 2)*((M:ℝ)^2/H) ∨
      ∃ k : ℕ, 0 < k ∧ 2*k ≤ H ∧ lam^(-(1:ℝ)/7) < k ∧
        ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖^2 ≤
          15*(Real.log H/Real.log 2)*
            ((M:ℝ)^2/H+((M:ℝ)/H)*‖robertSargosSymmetricSum f M k‖) := by
  obtain ⟨k,hk,hkH,hbound⟩ := exists_robertSargos_initial_dyadic_log f M H hH hHM
  by_cases hsmall : (k:ℝ) ≤ lam^(-(1:ℝ)/7)
  · left
    have hblock := robertSargos_small_symmetric_block f M k hC hk hlam hlamSmall
      hsmall hM hf hlo hhi
    have hHr : (0:ℝ) < H := by exact_mod_cast (by omega : 0 < H)
    have hlog : 0 ≤ Real.log H/Real.log 2 :=
      div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ H)))
        (Real.log_nonneg (by norm_num))
    have hmul := mul_le_mul_of_nonneg_left hblock
      (show 0 ≤ (M:ℝ)/H by positivity)
    have hsum := mul_le_mul_of_nonneg_left
      (add_le_add_right hmul ((M:ℝ)^2/H))
      (show 0 ≤ 15*(Real.log H/Real.log 2) by positivity)
    have hC' : 1+61*C ≤ 62*C := by linarith
    have hscale := mul_le_mul_of_nonneg_right hC'
      (show 0 ≤ 15*(Real.log H/Real.log 2)*((M:ℝ)^2/H) by positivity)
    calc
      _ ≤ 15*(Real.log H/Real.log 2)*
          ((M:ℝ)^2/H+((M:ℝ)/H)*(61*C*M)) := hbound.trans hsum
      _ = (1+61*C)*(15*(Real.log H/Real.log 2)*((M:ℝ)^2/H)) := by ring
      _ ≤ (62*C)*(15*(Real.log H/Real.log 2)*((M:ℝ)^2/H)) := hscale
      _ = _ := by ring
  · exact Or.inr ⟨k,hk,hkH,lt_of_not_ge hsmall,hbound⟩

end TaoTrudgianYang2025
