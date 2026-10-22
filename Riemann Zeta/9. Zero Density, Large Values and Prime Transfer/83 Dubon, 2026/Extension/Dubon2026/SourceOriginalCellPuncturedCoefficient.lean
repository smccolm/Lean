import Dubon2026.SourceOriginalCellCoordinateInverse
import Dubon2026.SourceOriginalPuncturedOneFormLaw

/-! DUB-17/18 -> raw reciprocity -> residue transport to a genuine cell.
The coefficient's fixed-chart pullback identity holds on a punctured
neighborhood for every original differential. Native nonzero-derivative
transport gives the punctured inverse limit; finite actual differential
support supplies regularity off the center.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Manifold Topology ContDiff
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem AnalyticCoord.inverse_tendsto_punctured (A : AnalyticCoord N)
    {Q : Place ℂ (modularFunctionFieldOver N ℂ)} (hQ : Q ∈ A.ζ.source) :
    Tendsto (extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) (𝓝[≠] (A.ζ Q))
      (𝓝[≠] (extChartAt 𝓘(ℂ, ℂ) Q Q)) := by
  have h := A.local_inverse hQ
  have hd := h.2.1.self_of_nhds
  have ht := hd.2.2.tendsto_nhdsNE (inv_ne_zero hd.2.1)
  rwa [h.2.2.2] at ht

theorem AnalyticCoord.coeff_eq_near_punctured (A : AnalyticCoord N)
    {Q : Place ℂ (modularFunctionFieldOver N ℂ)} (hQ : Q ∈ A.ζ.source)
    (θ : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) :
    ∀ᶠ w in 𝓝[≠] (A.ζ Q), coeffIn A.ζ θ w =
      OriginalChart.readDifferential N Q θ ((extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) w) *
        deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) w := by
  letI := OriginalChart.place_isManifold N
  set σ : ℂ → ℂ := extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm
  have h12 := (A.local_inverse hQ).1
  have hσd := (A.local_inverse hQ).2.1.mono fun _ h => h.2.2
  have hlaw := (A.inverse_tendsto_punctured hQ).eventually
    (OriginalChart.one_form_law_punctured N Q θ)
  have hkey : ∀ᶠ w in 𝓝[≠] (A.ζ Q), coeffIn A.ζ θ w = OriginalChart.readDifferential N Q θ (σ w) * deriv σ w := by
    filter_upwards [hlaw, h12.filter_mono nhdsWithin_le_nhds,
      h12.eventually_nhds.filter_mono nhdsWithin_le_nhds, hσd.filter_mono nhdsWithin_le_nhds]
      with w hw h12w h12w' hσdw
    have hlaw_w := hw

    have hback : (extChartAt 𝓘(ℂ, ℂ) Q).symm (σ w) = A.ζ.symm w := by
      show (extChartAt 𝓘(ℂ, ℂ) Q).symm (extChartAt 𝓘(ℂ, ℂ) Q (A.ζ.symm w)) = A.ζ.symm w
      rw [(extChartAt 𝓘(ℂ, ℂ) Q).left_inv h12w.2]
    rw [hback] at hlaw_w
    set Qw := A.ζ.symm w with hQw

    have hT : AnalyticAt ℂ (extChartAt 𝓘(ℂ, ℂ) Qw ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (σ w) := by
      apply MeromorphicCompact.analyticAt_transition Qw Q
      · exact (extChartAt 𝓘(ℂ, ℂ) Q).map_source h12w.2
      · change (extChartAt 𝓘(ℂ, ℂ) Q).symm (extChartAt 𝓘(ℂ, ℂ) Q (A.ζ.symm w)) ∈ _
        rw [(extChartAt 𝓘(ℂ, ℂ) Q).left_inv h12w.2]
        exact mem_extChartAt_source Qw

    have hchain : deriv (extChartAt 𝓘(ℂ, ℂ) Qw ∘ A.ζ.symm) w =
        deriv (extChartAt 𝓘(ℂ, ℂ) Qw ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (σ w) * deriv σ w := by
      have hev : (extChartAt 𝓘(ℂ, ℂ) Qw ∘ A.ζ.symm) =ᶠ[𝓝 w]
          (extChartAt 𝓘(ℂ, ℂ) Qw ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) ∘ σ := by
        filter_upwards [h12w'] with w' hw'
        show extChartAt 𝓘(ℂ, ℂ) Qw (A.ζ.symm w') =
          extChartAt 𝓘(ℂ, ℂ) Qw ((extChartAt 𝓘(ℂ, ℂ) Q).symm (extChartAt 𝓘(ℂ, ℂ) Q (A.ζ.symm w')))
        rw [(extChartAt 𝓘(ℂ, ℂ) Q).left_inv hw'.2]
      rw [hev.deriv_eq, hσdw.deriv]
      exact ((hT.differentiableAt.hasDerivAt).comp w hσdw).deriv
    show OriginalChart.readDifferential N Qw θ (extChartAt 𝓘(ℂ, ℂ) Qw Qw) *
        deriv (extChartAt 𝓘(ℂ, ℂ) Qw ∘ A.ζ.symm) w = OriginalChart.readDifferential N Q θ (σ w) * deriv σ w
    rw [hlaw_w, hchain]
    ring
  exact hkey

end
end Dubon2026.SourceFunctionField.CellGeometry
