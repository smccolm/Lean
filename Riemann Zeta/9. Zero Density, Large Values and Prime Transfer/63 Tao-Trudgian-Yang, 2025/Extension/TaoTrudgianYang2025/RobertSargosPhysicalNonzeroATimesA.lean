import TaoTrudgianYang2025.RobertSargosWeightedZeroSplit
import TaoTrudgianYang2025.RobertSargosPhysicalATimesAParameters
import TaoTrudgianYang2025.RobertSargosZeroZero
import TaoTrudgianYang2025.RobertSargosZeroRPhysical
import TaoTrudgianYang2025.RobertSargosZeroQPhysical

/-! Zero shifts removed from the actual source A-times-A sum, at physical floor scales. -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_physical_nonzero_a_times_a
    (f : ℝ → ℝ) (M H : ℕ) {C lam : ℝ}
    (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M)
    (hHmin : lam^(-(1:ℝ)/7) ≤ H) (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    ‖robertSargosSymmetricSum f M H‖^2 ≤
      3124*C*(1+2*Real.pi*C)*(M:ℝ)^2+
        (8*(M:ℝ)*H/
          ((⌊lam^(-(3:ℝ)/13)⌋₊:ℝ)*(⌊lam^(-(1:ℝ)/13)⌋₊:ℝ)))*
          robertSargosNonzeroShiftSum f M H
            ⌊lam^(-(3:ℝ)/13)⌋₊ ⌊lam^(-(1:ℝ)/13)⌋₊ := by
  obtain ⟨hH,hQ,hR,hQM,hRH⟩ :=
    robertSargos_physical_a_times_a_ranges M H hlam hsmall hM hHmin hHmax
  have hz := robertSargos_zero_zero_physical_a_times_a f M H hlam hsmall hHmax
  have hzr := robertSargos_zero_r_physical_a_times_a f M H hC hH hlam hsmall hM hHmax hf hlo hhi
  have hzq := robertSargos_zero_q_physical_a_times_a f M H hC hlam hsmall hM hHmax hf hlo hhi
  have he := robertSargos_physical_endpoint_budget M H hlam hsmall hM hHmax
  have ht := robertSargos_trimmed_a_times_a f M H
    ⌊lam^(-(3:ℝ)/13)⌋₊ ⌊lam^(-(1:ℝ)/13)⌋₊ hQ hR hQM hRH
  rw [robertSargos_weighted_zero_shift_decomposition f M H _ _ hQ hR,
    mul_add,mul_add,mul_add] at ht
  have hCp : 0 ≤ C := zero_le_one.trans hC
  have hfactor : 1 ≤ 1+2*Real.pi*C := by
    have hp : 0 ≤ 2*Real.pi*C := by positivity
    linarith
  have hCF : C ≤ C*(1+2*Real.pi*C) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor hCp
  have h1F : 1 ≤ C*(1+2*Real.pi*C) := hC.trans hCF
  have hCM := mul_le_mul_of_nonneg_right hCF (sq_nonneg (M:ℝ))
  have h1M := mul_le_mul_of_nonneg_right h1F (sq_nonneg (M:ℝ))
  nlinarith

end TaoTrudgianYang2025
