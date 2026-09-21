import TaoTrudgianYang2025.ZetaFourthMoment
import TaoTrudgianYang2025.PointValueLowMoment
import TaoTrudgianYang2025.EnergyClauseOneFromMoment

/-!
# Full twelfth moment and its actual large-values and energy consumers

The genuine unweighted fourth moment discharges the remaining moment
input in the high/low-value decomposition. Both Perron large-values
transfers and Add-est (i) then consume this proved twelfth moment.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace TaoTrudgianYang2025

theorem zeta_twelfth_dyadic :
    ∀ ε : ℝ, 0 < ε → ∃ D H₀ : ℝ, 0 ≤ D ∧
      ∀ H : ℝ, H₀ ≤ H → 0 < H →
        (∫ t in H..2*H, zetaMomentCriticalNorm t^12) ≤ D*H^(2+ε) :=
  zeta_twelfth_dyadic_of_fourth zeta_fourth_dyadic

theorem zetaTwelfth_largeValueBound {σ τ : ℝ}
    (hσ : 1/2 ≤ σ) (hτ : 2 ≤ τ) :
    IsZetaLargeValueBound σ τ (2*τ-12*(σ-1/2)) :=
  zetaTwelfth_largeValueBound_of_dyadic zeta_twelfth_dyadic hσ hτ

theorem zetaTwelfth_short_largeValueBound {σ τ : ℝ}
    (hσ : 3/4 ≤ σ) (hτ : 3/2 ≤ τ) :
    IsZetaLargeValueBound σ τ (2*τ-12*(σ-1/2)) :=
  zetaTwelfth_short_largeValueBound_of_dyadic zeta_twelfth_dyadic hσ hτ

theorem energyClauseOne_short_zeta {σ τ : ℝ}
    (hσ : 3/4 ≤ σ) (hτ : 1 ≤ τ) (hτhi : τ ≤ 2) :
    IsZetaLargeValueEnergyBound σ τ (energyClauseOnePublicRate σ*τ) :=
  energyClauseOne_short_zeta_of_dyadic zeta_twelfth_dyadic hσ hτ hτhi

/-- Add-est (i), on its full closed source interval and with no
analytic theorem supplied as a parameter. -/
theorem energyClauseOne {σ : ℝ} (hlo : 3/4 ≤ σ) (hhi : σ ≤ 5/6) :
    IsZeroDensityEnergyBound σ (energyClauseOnePublicRate σ/(1-σ)) :=
  energyClauseOne_of_dyadic_moment zeta_twelfth_dyadic hlo hhi

end TaoTrudgianYang2025

