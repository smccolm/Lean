import Dubon2026.SourceOriginalWeilCoverOneFormAt
import Dubon2026.SourceOriginalWeilCoverRegularNeighborhood

/-! DUB-17/18 -> cover reciprocity -> coordinate differential coefficients.
The already proved regular-at-a-place change law and actual chart inverse
identities give the one-form law at every regular point in a cover chart.
This avoids rebuilding the local Kaehler expression calculation. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders


theorem cover_one_form_law (Q : Place ℂ EE) (θ : Ω[EE⁄ℂ])
    (hθ : Q.differentialCoeff θ ∈ Q.toValuationSubring) :
    ∀ᶠ y in 𝓝 (0 : ℂ),
      AnalyticAt ℂ (readDifferential N n radicand baseDivisor hRadicand hOrders Q θ) y ∧
      readDifferential N n radicand baseDivisor hRadicand hOrders Q θ y =
        readDifferential N n radicand baseDivisor hRadicand hOrders
          (placeFamily N n radicand baseDivisor hRadicand hOrders Q y) θ 0 *
        deriv (placeChart N n radicand baseDivisor hRadicand hOrders
          (placeFamily N n radicand baseDivisor hRadicand hOrders Q y) ∘
            placeFamily N n radicand baseDivisor hRadicand hOrders Q) y := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have hr : ∀ᶠ y in 𝓝 (0 : ℂ),
      (placeFamily N n radicand baseDivisor hRadicand hOrders Q y).differentialCoeff θ ∈
        (placeFamily N n radicand baseDivisor hRadicand hOrders Q y).toValuationSubring := by
    have hc := placeFamily_continuousAt_zero N n radicand baseDivisor hRadicand hOrders Q
    rw [ContinuousAt, (place_spec N n radicand baseDivisor hRadicand hOrders Q).2.1] at hc
    exact hc.eventually (cover_eventually_differentialCoeff_mem N n radicand baseDivisor hRadicand hOrders Q θ hθ)
  filter_upwards [hr,
    (analyticAt_readDifferential_of_coeff_mem N n radicand baseDivisor hRadicand hOrders Q θ hθ).eventually_analyticAt,
    ball_mem_nhds (0 : ℂ) (place_spec N n radicand baseDivisor hRadicand hOrders Q).1] with y hyr hya hy
  exact ⟨hya, cover_one_form_law_at N n radicand baseDivisor hRadicand hOrders Q θ hy hyr⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
