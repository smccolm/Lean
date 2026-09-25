import TaoTrudgianYang2025.ContinuousPhaseWeyl
import TaoTrudgianYang2025.ThirdDerivativeCorrelation
import TaoTrudgianYang2025.ThirdDerivativeCorrelationSum

/-! Unoptimized third-derivative test derived from the actual phase and correlations. -/

noncomputable section
open Set GafniTao
namespace TaoTrudgianYang2025

theorem continuous_third_derivative_weyl
    (F F' F'' F''' : ℝ → ℝ) (A : ℝ) (N H : ℕ) {C μ : ℝ}
    (hC : 0 ≤ C) (hμ : 0 < μ) (hHμ : (H:ℝ)*μ ≤ 1)
    (hF : ∀ x ∈ Icc A (A+N), HasDerivAt F (F' x) x)
    (hF' : ∀ x ∈ Icc A (A+N), HasDerivAt F' (F'' x) x)
    (hF'' : ∀ x ∈ Icc A (A+N), HasDerivAt F'' (F''' x) x)
    (hlo : ∀ x ∈ Icc A (A+N), μ ≤ F''' x)
    (hhi : ∀ x ∈ Icc A (A+N), F''' x ≤ C*μ) :
    (H:ℝ)^2*‖∑ n ∈ Finset.range N, fordAdditiveCharacter (F (A+n))‖^2 ≤
      ((N+H:ℕ):ℝ)*((H:ℝ)*N+
        24*H*(C*N*Real.sqrt μ*((H:ℝ)*Real.sqrt H)+
          4*Real.sqrt H/Real.sqrt μ)) := by
  have hc (r : ℕ) (hr : r ∈ Finset.Icc 1 (H-1)) :
      ‖continuousPhaseCorrelation F A N r‖ ≤
        12*(C*N*Real.sqrt ((r:ℝ)*μ)+2/Real.sqrt ((r:ℝ)*μ)) := by
    have hri := Finset.mem_Icc.mp hr
    have hrH : (r:ℝ) ≤ H := by exact_mod_cast (show r ≤ H by omega)
    exact continuous_third_derivative_correlation F F' F'' F''' A N r hC hμ
      (by omega) ((mul_le_mul_of_nonneg_right hrH hμ.le).trans hHμ)
      hF hF' hF'' hlo hhi
  have hs := (Finset.sum_le_sum hc).trans
    (sum_third_derivative_correlation_majorant N H hC hμ)
  have hb := continuous_phase_weyl F A N H
  calc
    _ ≤ ((N+H:ℕ):ℝ)*((H:ℝ)*N+
        2*H*∑ r ∈ Finset.Icc 1 (H-1), ‖continuousPhaseCorrelation F A N r‖) := hb
    _ ≤ ((N+H:ℕ):ℝ)*((H:ℝ)*N+
        2*H*(12*(C*N*Real.sqrt μ*((H:ℝ)*Real.sqrt H)+
          4*Real.sqrt H/Real.sqrt μ))) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_left hs (by positivity)) _)
        (Nat.cast_nonneg _)
    _ = _ := by ring

end TaoTrudgianYang2025
