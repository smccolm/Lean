import TaoTrudgianYang2025.RobertSargosShiftBoundary

/-! Averaging preserves the explicit common-interval boundary budget. -/

noncomputable section
open scoped BigOperators
namespace TaoTrudgianYang2025

theorem norm_integer_average_le (v : ℤ → ℂ) (N : ℕ) (hN : 0 < N) (B : ℝ)
    (hv : ∀ n ∈ Finset.Icc (1:ℤ) N, ‖v n‖ ≤ B) :
    ‖(N:ℂ)⁻¹*∑ n ∈ Finset.Icc (1:ℤ) N, v n‖ ≤ B := by
  have hc : (Finset.Icc (1:ℤ) N).card = N := by rw [Int.card_Icc]; omega
  have hn : (N:ℝ) ≠ 0 := by positivity
  rw [norm_mul,norm_inv,Complex.norm_natCast]
  calc
    _ ≤ (N:ℝ)⁻¹*∑ n ∈ Finset.Icc (1:ℤ) N, ‖v n‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (N:ℝ)⁻¹*∑ _n ∈ Finset.Icc (1:ℤ) N, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hv) (by positivity)
    _ = B := by
      simp only [Finset.sum_const,hc,nsmul_eq_mul]
      rw [← mul_assoc,inv_mul_cancel₀ hn,one_mul]

theorem norm_robertSargos_common_shift_error (w : ℤ → ℂ) (M H Q N : ℕ) (h q : ℤ)
    (hN : 0 < N) (hh : h ∈ Finset.Ico (H:ℤ) (2*H))
    (hq : q ∈ Finset.Ioo (-(Q:ℤ)) Q) (hw : ∀ m, ‖w m‖ ≤ 1) :
    ‖(∑ m ∈ robertSargosMOverlap M h q 0, w m)-
      (N:ℂ)⁻¹*∑ n ∈ Finset.Icc (1:ℤ) N,
        ∑ m ∈ robertSargosCommonMInterval M H Q N, w (m+n)‖ ≤
      4*(H:ℝ)+4*Q+2*N := by
  rw [robertSargos_source_shift_average w M N h q hN,← mul_sub,← Finset.sum_sub_distrib]
  apply norm_integer_average_le _ N hN
  intro n hn
  exact norm_robertSargos_shifted_boundary w M H Q N h q n hh hq hn hw

end TaoTrudgianYang2025
