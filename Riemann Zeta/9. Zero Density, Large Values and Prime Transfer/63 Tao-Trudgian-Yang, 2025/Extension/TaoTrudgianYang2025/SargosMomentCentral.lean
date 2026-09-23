import TaoTrudgianYang2025.SargosDualTentWindow
import TaoTrudgianYang2025.SargosMomentCount

/-! The literal higher-moment count is bounded by the central unweighted moment. -/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

theorem sargosMomentNearCount_le_central {N : ℕ} (hN : 1 ≤ N) (p : ℕ)
    {Δ μ : ℝ} (hΔ : 0 < Δ) (hμ : 0 < μ) :
    (sargosMomentNearCount N p (1/(Δ*(N : ℝ)^2)) (1/(μ*(N : ℝ)^4)) : ℝ) ≤
      (64/(Δ*μ))*(∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
        ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*p)) := by
  rw [sargosMomentNearCount_physical hN p hΔ hμ]
  have hc : (sargosTupleCoefficient (fun _ => 1) : SargosMomentTuple N p → ℂ) =
      (fun _ => 1) := funext (fun t => sargosTupleCoefficient_one t)
  simp_rw [sargosQuarticSum_norm_even_eq_tuple_norm_sq,hc]
  exact sargosNearPairs_card_le_central
    (Finset.univ : Finset (SargosMomentTuple N p))
    sargosTupleSquareFrequency sargosTupleFourthFrequency hΔ hμ

theorem sargosMomentNearCount_window_le_central {N : ℕ} (hN : 1 ≤ N) (p : ℕ)
    {Δ δ μ lambda : ℝ} (hΔ : 0 < Δ) (hμ : 0 < μ)
    (hδ : Δ ≤ δ) (hlambda : μ ≤ lambda) :
    (sargosMomentNearCount N p (1/(δ*(N : ℝ)^2)) (1/(lambda*(N : ℝ)^4)) : ℝ) ≤
      (64/(Δ*μ))*(∫ α in Icc (-(Δ/2)) (Δ/2), ∫ γ in Icc (-(μ/2)) (μ/2),
        ‖sargosQuarticSum N (fun _ => 1) α γ‖^(2*p)) := by
  have h := sargosMomentNearCount_window_mono hN p hΔ hμ hδ hlambda
  exact (show (sargosMomentNearCount N p (1/(δ*(N : ℝ)^2))
      (1/(lambda*(N : ℝ)^4)) : ℝ) ≤
      (sargosMomentNearCount N p (1/(Δ*(N : ℝ)^2)) (1/(μ*(N : ℝ)^4)) : ℝ) by
    exact_mod_cast h).trans (sargosMomentNearCount_le_central hN p hΔ hμ)

end TaoTrudgianYang2025
