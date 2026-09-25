import TaoTrudgianYang2025.RobertSargosZeroRWeighted
import TaoTrudgianYang2025.RobertSargosZeroRRootBudget
import TaoTrudgianYang2025.RobertSargosZeroRFloorBudgets

/-! The zero-r row is absorbed at the actual source floor scales. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_r_physical_a_times_a
    (f : ℝ → ℝ) (M H : ℕ) {C lam : ℝ}
    (hC : 1 ≤ C) (hH : 0 < H) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hf : ∀ y ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc (1:ℝ) M, iteratedDeriv 4 f y ≤ C*lam) :
    (8*(M:ℝ)*H/
        ((⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)))*
      (∑ q ∈ (Finset.Ioo (-(⌊lam^(-(3:ℝ)/13)⌋₊:ℤ)) ⌊lam^(-(3:ℝ)/13)⌋₊).erase 0,
        (1-|(q:ℝ)|/(⌊lam^(-(3:ℝ)/13)⌋₊:ℝ))*
          (robertSargosTrimmedCorrelation f M H q 0).re) ≤ 1168*C*(M:ℝ)^2 := by
  obtain ⟨hQ,hR,hscale,hdiag,hpos,hinv⟩ :=
    robertSargos_zero_r_floor_budgets M H hH hlam hsmall hM hHmax
  have hrow := robertSargos_zero_r_weighted_row_bound
    f M H ⌊lam^(-(3:ℝ)/13)⌋₊ (zero_le_one.trans hC) hH hQ hlam hscale hf hlo hhi
  have hmul := mul_le_mul_of_nonneg_left hrow
    (show 0 ≤ 8*(M:ℝ)*H/
      ((⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)) by positivity)
  exact hmul.trans (zero_r_a_times_a_row_budget (Nat.cast_nonneg M)
    (by exact_mod_cast hH) (by exact_mod_cast hQ) (by exact_mod_cast hR)
    hC hlam hdiag hpos hinv)

end TaoTrudgianYang2025
