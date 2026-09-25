import TaoTrudgianYang2025.RobertSargosSymmetricArray
import TaoTrudgianYang2025.RobertSargosSourceThirdDerivative

/-! The ordinary third-derivative estimate on the actual full doubled h-block. -/

noncomputable section
open Set GafniTao
open scoped ContDiff
namespace TaoTrudgianYang2025

theorem robertSargos_symmetric_block_third_derivative_bound
    (f : ℝ → ℝ) (M H : ℕ) {C lam : ℝ}
    (hC : 1 ≤ C) (hH : 0 < H) (hlam : 0 < lam)
    (hscale : 4*(H:ℝ)*lam ≤ 1)
    (hf : ∀ y ∈ Icc (1:ℝ) M, ContDiffAt ℝ 4 f y)
    (hlo : ∀ y ∈ Icc (1:ℝ) M, lam ≤ iteratedDeriv 4 f y)
    (hhi : ∀ y ∈ Icc (1:ℝ) M, iteratedDeriv 4 f y ≤ C*lam) :
    ‖robertSargosSymmetricSum f M H‖ ≤
      (H:ℝ)*(1+20*C*((M:ℝ)*(4*(H:ℝ)*lam)^((1:ℝ)/6)+
        Real.sqrt M*(2*(H:ℝ)*lam)^(-(1:ℝ)/6))) := by
  have hHr : (0:ℝ) < H := by exact_mod_cast hH
  have hb (h : ℤ) (hh : h ∈ Finset.Ico (H:ℤ) (2*H)) :
      ‖robertSargosSourceCenteredPhase f M h‖ ≤
        1+20*C*((M:ℝ)*(4*(H:ℝ)*lam)^((1:ℝ)/6)+
          Real.sqrt M*(2*(H:ℝ)*lam)^(-(1:ℝ)/6)) := by
    have hhiI := Finset.mem_Ico.mp hh
    have hHh : (H:ℝ) ≤ h := by exact_mod_cast hhiI.1
    have hhH : (h:ℝ) < 2*H := by exact_mod_cast hhiI.2
    have hhr : (0:ℝ) < h := hHr.trans_le hHh
    have hsmall : 2*(H:ℝ)*lam ≤ 2*(h:ℝ)*lam := by nlinarith
    have hlarge : 2*(h:ℝ)*lam ≤ 4*(H:ℝ)*lam := by nlinarith
    have hp := robertSargos_source_centered_third_derivative_bound f M h hC
      (by exact_mod_cast hhr) hlam (hlarge.trans hscale) hf hlo hhi
    have hpos := Real.rpow_le_rpow (by positivity : 0 ≤ 2*(h:ℝ)*lam)
      hlarge (by norm_num : 0 ≤ (1:ℝ)/6)
    have hneg := Real.rpow_le_rpow_of_nonpos
      (by positivity : 0 < 2*(H:ℝ)*lam) hsmall (by norm_num : -(1:ℝ)/6 ≤ 0)
    have hb1 := mul_le_mul_of_nonneg_left hpos (Nat.cast_nonneg (α := ℝ) M)
    have hb2 := mul_le_mul_of_nonneg_left hneg (Real.sqrt_nonneg (M:ℝ))
    have hb3 := mul_le_mul_of_nonneg_left (add_le_add hb1 hb2)
      (show 0 ≤ 20*C by positivity)
    linarith
  have hcard : (Finset.Ico (H:ℤ) (2*H)).card = H := by
    rw [Int.card_Ico]
    omega
  change ‖∑ h ∈ Finset.Ico (H:ℤ) (2*H), robertSargosSourceCenteredPhase f M h‖ ≤ _
  calc
    _ ≤ ∑ h ∈ Finset.Ico (H:ℤ) (2*H), ‖robertSargosSourceCenteredPhase f M h‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _h ∈ Finset.Ico (H:ℤ) (2*H),
        (1+20*C*((M:ℝ)*(4*(H:ℝ)*lam)^((1:ℝ)/6)+
          Real.sqrt M*(2*(H:ℝ)*lam)^(-(1:ℝ)/6))) := Finset.sum_le_sum hb
    _ = _ := by simp only [Finset.sum_const,hcard,nsmul_eq_mul]

end TaoTrudgianYang2025
