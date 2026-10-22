import Dubon2026.SourceOriginalCellCoordinateInverse
import Dubon2026.SourceOriginalChartOneFormLaw

/-! DUB-17/18 -> raw reciprocity -> actual cell coefficient calculus.
The coefficient defined with the moving centered chart equals the fixed-chart
pullback locally, and is analytic wherever the original differential is regular.
Adapted from S_AlgebraicCurve_coeffIn_local_calculus, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, using the already proved
original chart laws and native analyticity of inverse coordinates.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Manifold Topology ContDiff
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem AnalyticCoord.coeff_eq_near (A : AnalyticCoord N)
    {Q : Place ℂ (modularFunctionFieldOver N ℂ)} (hQ : Q ∈ A.ζ.source)
    {θ : Ω[modularFunctionFieldOver N ℂ⁄ℂ]}
    (hθ : Q.differentialCoeff θ ∈ Q.toValuationSubring) :
    (∀ᶠ w in 𝓝 (A.ζ Q), coeffIn A.ζ θ w =
      OriginalChart.readDifferential N Q θ ((extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) w) *
        deriv (extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) w) ∧
    AnalyticAt ℂ (coeffIn A.ζ θ) (A.ζ Q) := by
  letI := OriginalChart.place_isManifold N
  set σ : ℂ → ℂ := extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm with hσ
  obtain ⟨h12, hστ, hσcont₀, hσc⟩ := A.local_inverse hQ
  have hσc' : σ (A.ζ Q) = extChartAt 𝓘(ℂ, ℂ) Q Q := hσc
  have hσnear : Tendsto σ (𝓝 (A.ζ Q)) (𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q)) := by
    rw [← hσc']; exact hσcont₀
  have hσd : ∀ᶠ w in 𝓝 (A.ζ Q), HasDerivAt σ
      (deriv (A.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (σ w))⁻¹ w := hστ.mono fun w hw => hw.2.2

  have hσa : AnalyticAt ℂ σ (A.ζ Q) := A.analyticAt_inverse hQ

  have hlaw := hσnear.eventually (OriginalChart.one_form_law N Q θ hθ)
  have hkey : ∀ᶠ w in 𝓝 (A.ζ Q), coeffIn A.ζ θ w = OriginalChart.readDifferential N Q θ (σ w) * deriv σ w := by
    filter_upwards [hlaw, h12, h12.eventually_nhds, hσd]
      with w hw h12w h12w' hσdw
    obtain ⟨-, hlaw_w⟩ := hw

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
  refine ⟨hkey, ?_⟩

  have hRa : ∀ᶠ w in 𝓝 (A.ζ Q), AnalyticAt ℂ (OriginalChart.readDifferential N Q θ) (σ w) :=
    hlaw.mono fun w hw => hw.1
  have h1 : AnalyticAt ℂ (fun w => OriginalChart.readDifferential N Q θ (σ w) * deriv σ w) (A.ζ Q) :=
    (hRa.self_of_nhds.comp hσa).mul hσa.deriv
  exact h1.congr (hkey.mono fun w hw => hw.symm)

end
end Dubon2026.SourceFunctionField.CellGeometry
