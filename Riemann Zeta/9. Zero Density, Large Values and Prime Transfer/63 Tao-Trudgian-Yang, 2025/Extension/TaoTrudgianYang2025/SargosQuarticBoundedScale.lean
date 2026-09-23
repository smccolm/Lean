import TaoTrudgianYang2025.SargosQuarticLargeSourceMoment

/-! Source-linked rounded scales on the bounded range below the analytic threshold. -/

noncomputable section

namespace TaoTrudgianYang2025

theorem sargosQuartic_source_scale_sixteen {N Δ : ℝ}
    (hN : 16 ≤ N) (hΔ : 1/Real.sqrt N ≤ Δ) :
    0 < Δ ∧ 4 ≤ Δ*N ∧ 8 ≤ sargosQuarticRoundedDualScale N Δ := by
  have hNp : 0 < N := by linarith only [hN]
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hNp
  have hs4 : 4 ≤ Real.sqrt N := by
    nlinarith only [Real.sq_sqrt hNp.le,Real.sqrt_nonneg N,hN]
  have hΔp : 0 < Δ := (div_pos (by norm_num) hs).trans_le hΔ
  have hprod : 1 ≤ Δ*Real.sqrt N := (div_le_iff₀ hs).mp hΔ
  have hsN : Real.sqrt N ≤ Δ*N := by
    have hh := mul_le_mul_of_nonneg_right hprod hs.le
    have he : (Δ*Real.sqrt N)*Real.sqrt N = Δ*N := by
      rw [mul_assoc,← sq,Real.sq_sqrt hNp.le]
    simpa only [one_mul,he] using hh
  have hΔN : 4 ≤ Δ*N := hs4.trans hsN
  refine ⟨hΔp,hΔN,?_⟩
  exact Nat.le_floor (by nlinarith only [hΔN] : (8:ℝ) ≤ 2*Δ*N)

theorem sargosQuartic_bounded_source_delta {N Δ : ℝ}
    (hN : 0 < N) (hN₁ : N ≤ 9216) (hΔ : 1/Real.sqrt N ≤ Δ) :
    1/96 ≤ Δ := by
  have hs : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hs96 : Real.sqrt N ≤ 96 := by
    nlinarith only [Real.sq_sqrt hN.le,Real.sqrt_nonneg N,hN₁]
  exact (one_div_le_one_div_of_le hs hs96).trans hΔ

end TaoTrudgianYang2025
