import Dubon2026.SourceOriginalBoundaryArcPaths

/-! DUB-17/18 -> original Abel-Jacobi -> edge path-integral identity.
The existing original coefficient/inverse-coordinate laws give the derivative
of a local path primitive along an actual cell-coordinate curve. This is the
chain-rule input for the affine boundary-arc fundamental theorem of calculus.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Manifold Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem AnalyticCoord.hasDerivAt_path_primitive (A : AnalyticCoord N)
    {Q : Place ℂ F} (hQ : Q ∈ A.ζ.source) {θ : Ω[F⁄ℂ]}
    (hθ : Q.differentialCoeff θ ∈ Q.toValuationSubring)
    {Φ : ℂ → ℂ}
    (hΦ : HasDerivAt Φ (OriginalChart.readDifferential N Q θ (extChartAt 𝓘(ℂ, ℂ) Q Q))
      (extChartAt 𝓘(ℂ, ℂ) Q Q))
    {z : ℝ → ℂ} {v : ℂ} {t : ℝ} (hz : HasDerivAt z v t) (hzt : z t = A.ζ Q) :
    HasDerivAt (Φ ∘ extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm ∘ z)
      (coeffIn A.ζ θ (z t) * v) t := by
  let σ : ℂ → ℂ := extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm
  have hσ : HasDerivAt σ (deriv σ (A.ζ Q)) (A.ζ Q) :=
    (A.analyticAt_inverse hQ).differentiableAt.hasDerivAt
  have hσQ : σ (A.ζ Q) = extChartAt 𝓘(ℂ, ℂ) Q Q := (A.local_inverse hQ).2.2.2
  have hcoeff := (A.coeff_eq_near hQ hθ).1.self_of_nhds
  change coeffIn A.ζ θ (A.ζ Q) = OriginalChart.readDifferential N Q θ (σ (A.ζ Q)) *
    deriv σ (A.ζ Q) at hcoeff
  rw [hσQ] at hcoeff
  have hσz : HasDerivAt (σ ∘ z) (deriv σ (A.ζ Q) * v) t := by
    apply HasDerivAt.comp t _ hz
    rwa [hzt]
  have hΦz : HasDerivAt Φ (OriginalChart.readDifferential N Q θ (extChartAt 𝓘(ℂ, ℂ) Q Q))
      ((σ ∘ z) t) := by
    simpa only [Function.comp_apply, hzt, hσQ] using hΦ
  convert hΦz.comp t hσz using 1
  rw [hzt, hcoeff, mul_assoc]

end
end Dubon2026.SourceFunctionField.CellGeometry
