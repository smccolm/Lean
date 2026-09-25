import TaoTrudgianYang2025.RobertSargosNonzeroShiftError
import TaoTrudgianYang2025.RobertSargosNonzeroShiftedBound
import TaoTrudgianYang2025.RobertSargosPhysicalCommonShiftBudget
import TaoTrudgianYang2025.RobertSargosPhysicalNonzeroATimesA

/-! The actual nonzero triple sum at N=Q=floor(lambda^(-3/13)). -/

noncomputable section
open Set
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_physical_nonzero_shifted_triple
    (f : ℝ → ℝ) (M H : ℕ) {C lam : ℝ}
    (hC : 1 ≤ C) (hlam : 0 < lam) (hsmall : lam ≤ 1/8192)
    (hM : lam^(-(8:ℝ)/13) ≤ M)
    (hHmin : lam^(-(1:ℝ)/7) ≤ H) (hHmax : (H:ℝ) ≤ lam^(-(2:ℝ)/13)/2)
    (hf : ∀ x ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f x)
    (hlo : ∀ x ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f x)
    (hhi : ∀ x ∈ Icc (1:ℝ) M, iteratedDeriv 4 f x ≤ C*lam) :
    let Q := ⌊lam^(-(3:ℝ)/13)⌋₊
    let R := ⌊lam^(-(1:ℝ)/13)⌋₊
    ‖robertSargosSymmetricSum f M H‖^2 ≤
      3140*C*(1+2*Real.pi*C)*(M:ℝ)^2+
        (8*(M:ℝ)*H/((Q:ℝ)*R*Q))*
          (∑ r ∈ (Finset.Ioo (-(R:ℤ)) R).erase 0,
            ∑ m ∈ robertSargosCommonMInterval M H Q Q,
              ‖robertSargosNonzeroShiftedTriple f H Q Q r m‖) := by
  dsimp only
  let Q := ⌊lam^(-(3:ℝ)/13)⌋₊
  let R := ⌊lam^(-(1:ℝ)/13)⌋₊
  obtain ⟨_,hQ,hR,_,_⟩ :=
    robertSargos_physical_a_times_a_ranges M H hlam hsmall hM hHmin hHmax
  have hs := robertSargos_physical_nonzero_a_times_a f M H hC hlam hsmall hM hHmin hHmax hf hlo hhi
  have hshift := robertSargos_nonzero_weighted_shift_error f M H Q R Q hQ hR hQ
  have hreal := robertSargos_nonzero_weighted_shifted_re_le f M H Q R Q hR
  have he := mul_le_mul_of_nonneg_left (hshift.trans (add_le_add_left hreal _))
    (show 0 ≤ 8*(M:ℝ)*H/((Q:ℝ)*R) by positivity)
  have hcancel : (8*(M:ℝ)*H/((Q:ℝ)*R))*
      ((H:ℝ)*(4*(H:ℝ)+4*Q+2*Q)*Q*R) =
      8*(M:ℝ)*(H:ℝ)^2*(4*(H:ℝ)+6*Q) := by
    have hq0 : (Q:ℝ) ≠ 0 := by dsimp only [Q]; exact_mod_cast hQ.ne'
    have hr0 : (R:ℝ) ≠ 0 := by dsimp only [R]; exact_mod_cast hR.ne'
    field_simp
    ring
  have halg (B : ℝ) : (8*(M:ℝ)*H/((Q:ℝ)*R))*((Q:ℝ)⁻¹*B) =
      (8*(M:ℝ)*H/((Q:ℝ)*R*Q))*B := by
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  rw [mul_add,hcancel,halg] at he
  have hb := robertSargos_physical_common_shift_budget M H hlam hsmall hM hHmax
  have hCp : 0 ≤ C := zero_le_one.trans hC
  have hfactor : 1 ≤ 1+2*Real.pi*C := by
    have hp : 0 ≤ 2*Real.pi*C := by positivity
    linarith
  have hCF : C ≤ C*(1+2*Real.pi*C) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hfactor hCp
  have h1M := mul_le_mul_of_nonneg_right (hC.trans hCF) (sq_nonneg (M:ℝ))
  dsimp only [Q,R] at he
  nlinarith

end TaoTrudgianYang2025
