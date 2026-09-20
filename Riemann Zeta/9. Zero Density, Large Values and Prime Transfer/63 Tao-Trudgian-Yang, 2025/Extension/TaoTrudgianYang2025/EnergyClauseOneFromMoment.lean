import TaoTrudgianYang2025.ZetaTwelfthFromMoment
import TaoTrudgianYang2025.ZetaShortPatterns

/-!
# Add-est (i) reduced to the genuine twelfth moment

The short-zeta input is derived here: cancellation below height exponent
`3/2`, and the threshold-relative Perron estimate and cubic energy bound
from `3/2` to `2`. No short-zeta estimate is assumed in final assembly.
-/

noncomputable section

open MeasureTheory Set

namespace TaoTrudgianYang2025

theorem energyClauseOnePublicRate_ge_short_linear {σ : ℝ} (hσ : 3 / 4 ≤ σ) :
    15 - 18 * σ ≤ energyClauseOnePublicRate σ := by
  apply le_trans _ (le_max_left _ _)
  apply (le_div_iff₀ (by linarith : 0 < 2 * (3 * σ - 1))).2
  nlinarith [mul_nonneg (by linarith : 0 ≤ σ - 3 / 4)
    (by linarith : 0 ≤ 108 * σ - 64)]

theorem energyClauseOne_short_cubic_bound {σ τ : ℝ}
    (hσ : 3 / 4 ≤ σ) (hτ : 0 ≤ τ) (hτhi : τ ≤ 2) :
    3 * (2 * τ - 12 * (σ - 1 / 2)) ≤ energyClauseOnePublicRate σ * τ := by
  have hB := mul_le_mul_of_nonneg_right (energyClauseOnePublicRate_ge_short_linear hσ) hτ
  nlinarith [mul_nonneg (by linarith : 0 ≤ 18 * σ - 9) (by linarith : 0 ≤ 2 - τ)]

/-- Every short-zeta height needed by the endpoint-one transfer is supplied
by the genuine moment, with no independent energy or cardinality premise. -/
theorem energyClauseOne_short_zeta_of_dyadic
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    {σ τ : ℝ} (hσ : 3 / 4 ≤ σ) (hτ : 1 ≤ τ) (hτhi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseOnePublicRate σ * τ) := by
  by_cases hshort : τ < 3 / 2
  · exact zetaShort_energyBound_any hσ hτ hshort _
  · have hbound := (zetaTwelfth_short_largeValueBound_of_dyadic hDyadic hσ
      (le_of_not_gt hshort)).toEnergyBound_three_mul
    intro ε hε
    obtain ⟨C, hC, δ, hδ, h⟩ := hbound ε hε
    refine ⟨C, hC, δ, hδ, ?_⟩
    intro P hN hTl hTu hVl hVu
    apply (h P hN hTl hTu hVl hVu).trans
    apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
    apply Real.rpow_le_rpow_of_exponent_le P.one_lt_N.le
    have := energyClauseOne_short_cubic_bound hσ (by linarith : 0 ≤ τ) hτhi
    linarith

/-- Full source-domain clause-(i) deduction. The only mathematical theorem
parameter is the explicit dyadic critical-line twelfth moment. -/
theorem energyClauseOne_of_dyadic_moment
    (hDyadic : ∀ η : ℝ, 0 < η → ∃ C T₀ : ℝ, 0 ≤ C ∧
      ∀ H : ℝ, T₀ ≤ H → 0 < H →
        (∫ u in H..2 * H, zetaMomentCriticalNorm u ^ 12) ≤ C * H ^ (2 + η))
    {σ : ℝ} (hlo : 3 / 4 ≤ σ) (hhi : σ ≤ 5 / 6) :
    IsZeroDensityEnergyBound σ (energyClauseOnePublicRate σ / (1 - σ)) :=
  energyClauseOne_of_dyadic_moment_and_short_zeta hDyadic hlo hhi
    (fun _ hτ => energyClauseOne_short_zeta_of_dyadic hDyadic hlo hτ.1 hτ.2.le)

end TaoTrudgianYang2025
