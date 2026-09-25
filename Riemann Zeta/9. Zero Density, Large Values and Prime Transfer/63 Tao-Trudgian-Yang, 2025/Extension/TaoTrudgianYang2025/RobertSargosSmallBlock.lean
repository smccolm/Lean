import TaoTrudgianYang2025.RobertSargosSymmetricBlockThirdDerivative
import TaoTrudgianYang2025.RobertSargosSmallBlockScale
import TaoTrudgianYang2025.RobertSargosSmallBlockParameters

/-! Actual small doubled blocks controlled from the source physical scales. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_small_symmetric_block
    (f : ℝ → ℝ) (M H : ℕ) {C lam : ℝ}
    (hC : 1 ≤ C) (hH : 0 < H) (hlam : 0 < lam) (hlamSmall : lam ≤ 1/16)
    (hHM : (H:ℝ) ≤ lam^(-(1:ℝ)/7)) (hM : lam^(-(8:ℝ)/13) ≤ M)
    (hf : ∀ y ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc (1:ℝ) M, iteratedDeriv 4 f y ≤ C*lam) :
    ‖robertSargosSymmetricSum f M H‖ ≤ 61*C*M := by
  obtain ⟨hHM',hscale,hfirst,hsecond⟩ :=
    robertSargos_small_block_parameters (Nat.cast_nonneg H) hlam hlamSmall hHM hM
  exact (robertSargos_symmetric_block_third_derivative_bound f M H hC hH hlam hscale
    hf hlo hhi).trans
      (small_block_third_derivative_budget (Nat.cast_nonneg M)
        (by exact_mod_cast hH) hHM' hC hlam hfirst hsecond)

end TaoTrudgianYang2025
