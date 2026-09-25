import TaoTrudgianYang2025.RobertSargosZeroQWeighted
import TaoTrudgianYang2025.RobertSargosZeroQColumnBudget
import TaoTrudgianYang2025.RobertSargosZeroQFloorBudgets

/-! The actual zero-q column is absorbed at the source floor scales. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_zero_q_physical_a_times_a
    (f : ℝ → ℝ) (M H : ℕ) {C lam : ℝ}
    (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M) (hH : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    (8*(M:ℝ)*H/
      ((⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)))*
      (∑ r ∈ (Finset.Ioo (-(⌊lam^(-(1:ℝ)/13)⌋₊:ℤ)) ⌊lam^(-(1:ℝ)/13)⌋₊).erase 0,
        (1-|(r:ℝ)|/(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ))*
          (robertSargosTrimmedCorrelation f M H 0 r).re) ≤
      1944*C*(1+2*Real.pi*C)*(M:ℝ)^2 := by
  obtain ⟨hQ,hR,hRmax,hdiag,herr,hroot⟩ :=
    robertSargos_zero_q_floor_budgets M H hlam hsmall hM hH
  have hrow := robertSargos_zero_q_weighted_column_bound
    f M H ⌊lam^(-(1:ℝ)/13)⌋₊ hR hC hlam hsmall hM hH hRmax hf hlo hhi
  have hm := mul_le_mul_of_nonneg_left hrow
    (show 0 ≤ 8*(M:ℝ)*H/
      ((⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)) by positivity)
  exact hm.trans (zero_q_a_times_a_column_budget
    (Nat.cast_nonneg M) (by exact_mod_cast hQ) (by exact_mod_cast hR) hC hdiag herr hroot)

end TaoTrudgianYang2025
