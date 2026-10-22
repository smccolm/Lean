import Dubon2026.SourceOriginalLocalChartPathIntegral
import Dubon2026.SourceOriginalPeriodExponentialConsumer

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
meromorphic gluing of the path exponential. Its exact path transport gives
the local formula g(z)=g(z0) exp(Phi(z)-Phi(z0)) on every open path-connected
chart region avoiding the actual divisor support.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem original_exponential_local_transport (D : Divisor ℂ F) (η : Ω[F⁄ℂ])
    (hη : ∀ v : Place ℂ F, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (g : Place ℂ F → ℂ)
    (htrans : ∀ (P Q : Place ℂ F) (σ : Path P Q), D P = 0 → D Q = 0 →
      (∀ t, D (σ t) = 0) → g Q = g P * Complex.exp (pathIntegral N η σ))
    (v : Place ℂ F) {W : Set ℂ} (hW : IsOpen W) (hpath : IsPathConnected W)
    (hsub : W ⊆ ball (0 : ℂ) (placeRadius N v))
    (hD : ∀ z ∈ W, D (placeFamily N v z) = 0) (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ W, HasDerivAt Φ (readDifferential N v η z) z)
    {z₀ z₁ : ℂ} (hz₀ : z₀ ∈ W) (hz₁ : z₁ ∈ W) :
    g (placeFamily N v z₁) = g (placeFamily N v z₀) * Complex.exp (Φ z₁ - Φ z₀) := by
  obtain ⟨σ, hσ, hint⟩ := exists_original_local_chart_path_integral N η v hW hpath hsub Φ hΦ
    (fun z hz => original_coeff_regular_off_divisor N D η hη hres _ (hD z hz)) hz₀ hz₁
  have hσD : ∀ t, D (σ t) = 0 := by
    intro t
    obtain ⟨z, hz, he⟩ := hσ t
    rw [← he]
    exact hD z hz
  rw [htrans _ _ σ (hD _ hz₀) (hD _ hz₁) hσD, hint]

end
end Dubon2026.SourceFunctionField.OriginalChart
