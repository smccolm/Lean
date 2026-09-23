import TaoTrudgianYang2025.SargosRealQuarticRegularity

/-! The actual integrated one-term real-endpoint error. -/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

theorem sargos_unit_rectangle_integral_one {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (c d : ℝ) :
    (∫ _α in Icc c (c+1), ∫ _γ in Icc d (d+lambda), (1:ℝ)) = lambda := by
  simp [integral_const,measureReal_def,Real.volume_Icc,hlambda]

theorem sargosRealQuartic_sixth_rectangle_le_natural {M : ℝ} (hM : 0 ≤ M)
    (z : ℤ → ℂ) (hz : ∀ n ∈ sargosRealSourceInterval M, ‖z n‖ ≤ 1)
    {lambda : ℝ} (hlambda : 0 ≤ lambda) (c d : ℝ) :
    (∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
      (sargosRealQuarticMaximum M z α γ)^6) ≤
      32*((∫ α in Icc c (c+1), ∫ γ in Icc d (d+lambda),
        (sargosQuarticPrefixMaximum ⌊M⌋₊ z α γ)^6)+lambda) := by
  let μ := (volume.restrict (Icc c (c+1))).prod (volume.restrict (Icc d (d+lambda)))
  have hr := integrable_sargosRealQuarticPower_rectangle hM z hz 6 c (c+1) d (d+lambda)
  have hn := integrable_sargosQuarticMaximumPower_rectangle ⌊M⌋₊ 6 z c (c+1) d (d+lambda)
  have hconst : (∫ _t : ℝ × ℝ, (1:ℝ) ∂μ) = lambda := by
    rw [integral_prod _ (show Integrable (fun _t : ℝ × ℝ => (1:ℝ)) μ from integrable_const _)]
    exact sargos_unit_rectangle_integral_one hlambda c d
  calc
    _ = ∫ t : ℝ × ℝ, (sargosRealQuarticMaximum M z t.1 t.2)^6 ∂μ :=
      (integral_prod _ hr).symm
    _ ≤ ∫ t : ℝ × ℝ, 32*((sargosQuarticPrefixMaximum ⌊M⌋₊ z t.1 t.2)^6+1) ∂μ := by
      apply integral_mono hr ((hn.add (integrable_const (1:ℝ))).const_mul 32)
      intro t
      exact sargosRealQuarticMaximum_sixth_le hM z hz t.1 t.2
    _ = _ := by
      rw [integral_const_mul,integral_add hn (integrable_const (1:ℝ)),hconst,
        integral_prod _ hn]

end TaoTrudgianYang2025
