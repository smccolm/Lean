import TaoTrudgianYang2025.RobertSargosInitialSmallBlock
import TaoTrudgianYang2025.RobertSargosInitialFloorBudget

/-! Physical initial reduction with the small-block branch fully discharged. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_physical_initial_reduction
    (f : ℝ → ℝ) (M : ℕ) {C lam : ℝ}
    (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M)
    (hf : ∀ y ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc (1:ℝ) M, iteratedDeriv 4 f y ≤ C*lam) :
    ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖^2 ≤
        1860*C*(Real.log M/Real.log 2)*(M:ℝ)^2*lam^((2:ℝ)/13) ∨
      ∃ k : ℕ, 0 < k ∧ 2*k ≤ ⌊lam^(-(2:ℝ)/13)⌋₊ ∧
        lam^(-(1:ℝ)/7) < k ∧ (k:ℝ) ≤ lam^(-(2:ℝ)/13)/2 ∧
        ‖∑ m ∈ Finset.Icc (1:ℤ) M, fordAdditiveCharacter (f m)‖^2 ≤
          15*(Real.log (⌊lam^(-(2:ℝ)/13)⌋₊:ℝ)/Real.log 2)*
            ((M:ℝ)^2/(⌊lam^(-(2:ℝ)/13)⌋₊:ℝ)+
              ((M:ℝ)/(⌊lam^(-(2:ℝ)/13)⌋₊:ℝ))*‖robertSargosSymmetricSum f M k‖) := by
  obtain ⟨hH,hHM,_,hupper⟩ := robertSargos_physical_floor_shift M hlam hsmall hM
  rcases robertSargos_initial_small_or_large_block f M ⌊lam^(-(2:ℝ)/13)⌋₊
      hC hH hHM hlam (by linarith) hM hf hlo hhi with hbound | ⟨k,hk,hkH,hklo,hbound⟩
  · exact Or.inl (hbound.trans
      (robertSargos_initial_floor_budget M (zero_le_one.trans hC) hlam hsmall hM))
  · refine Or.inr ⟨k,hk,hkH,hklo,?_,hbound⟩
    have hkHr : 2*(k:ℝ) ≤ (⌊lam^(-(2:ℝ)/13)⌋₊:ℝ) := by exact_mod_cast hkH
    linarith

end TaoTrudgianYang2025
