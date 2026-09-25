import TaoTrudgianYang2025.SecondDerivativeScale

/-! Algebraic normalization of the summed-correlation third-derivative bound. -/

noncomputable section
namespace TaoTrudgianYang2025

theorem third_derivative_weyl_normalize {S N H C μ : ℝ}
    (hN : 0 ≤ N) (hH : 0 < H) (hHN : H ≤ N) (hC : 0 ≤ C) (hμ : 0 < μ)
    (hb : H^2*S^2 ≤ (N+H)*(H*N+
      24*H*(C*N*Real.sqrt μ*(H*Real.sqrt H)+4*Real.sqrt H/Real.sqrt μ))) :
    S^2 ≤ 2*N^2/H+48*C*N^2*Real.sqrt μ*Real.sqrt H+
      192*N/(Real.sqrt H*Real.sqrt μ) := by
  have hk : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have hm : 0 < Real.sqrt μ := Real.sqrt_pos.mpr hμ
  have hinner : 0 ≤ H*N+
      24*H*(C*N*Real.sqrt μ*(H*Real.sqrt H)+4*Real.sqrt H/Real.sqrt μ) := by positivity
  have hbound := hb.trans (mul_le_mul_of_nonneg_right
    (show N+H ≤ 2*N by linarith) hinner)
  have hd := (le_div_iff₀ (sq_pos_of_pos hH)).mpr
    (show S^2*H^2 ≤ _ by simpa only [mul_comm (H^2) (S^2)] using hbound)
  have hid :
      (2*N*(H*N+24*H*(C*N*Real.sqrt μ*(H*Real.sqrt H)+
        4*Real.sqrt H/Real.sqrt μ)))/H^2 =
      2*N^2/H+48*C*N^2*Real.sqrt μ*Real.sqrt H+
        192*N/(Real.sqrt H*Real.sqrt μ) := by
    generalize he : Real.sqrt H = k at *
    have hk2 : k^2 = H := by rw [← he,Real.sq_sqrt hH.le]
    rw [← hk2]
    field_simp
    ring
  exact hd.trans_eq hid

end TaoTrudgianYang2025
