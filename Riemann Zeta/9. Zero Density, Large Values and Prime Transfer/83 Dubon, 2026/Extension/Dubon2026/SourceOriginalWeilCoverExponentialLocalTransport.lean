import Dubon2026.SourceOriginalWeilCoverLocalChartPathIntegral
import Dubon2026.SourceOriginalWeilCoverPeriodExponentialConsumer

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse -> integral-period principality. The native exponential argument is applied to the actual cover with constructed residue data, paths and local models. Integral loop periods remain an explicit upstream hypothesis; their correction and the full Abel converse are not asserted here. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n] (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (A : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * A v)
include A hRadicand hOrders
local notation "CoverPath" => @Path (Place ℂ EE) (placeTopology N n radicand A hRadicand hOrders)


theorem cover_exponential_local_transport (D : Divisor ℂ EE) (η : Ω[EE⁄ℂ])
    (hη : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential η)
    (hres : ∀ v, v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff η) = (D v : ℂ))
    (g : Place ℂ EE → ℂ)
    (htrans : ∀ (P Q : Place ℂ EE) (σ : CoverPath P Q), D P = 0 → D Q = 0 →
      (∀ t, D (σ t) = 0) → g Q = g P * Complex.exp (pathIntegral N n radicand A hRadicand hOrders η σ))
    (v : Place ℂ EE) {W : Set ℂ} (hW : IsOpen W) (hpath : IsPathConnected W)
    (hsub : W ⊆ ball (0 : ℂ) (placeRadius N n radicand A hRadicand hOrders v))
    (hD : ∀ z ∈ W, D (placeFamily N n radicand A hRadicand hOrders v z) = 0) (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ W, HasDerivAt Φ (readDifferential N n radicand A hRadicand hOrders v η z) z)
    {z₀ z₁ : ℂ} (hz₀ : z₀ ∈ W) (hz₁ : z₁ ∈ W) :
    g (placeFamily N n radicand A hRadicand hOrders v z₁) = g (placeFamily N n radicand A hRadicand hOrders v z₀) * Complex.exp (Φ z₁ - Φ z₀) := by
  letI := placeTopology N n radicand A hRadicand hOrders
  obtain ⟨σ, hσ, hint⟩ := exists_cover_local_chart_path_integral N n radicand A hRadicand hOrders η v hW hpath hsub Φ hΦ
    (fun z hz => cover_coeff_regular_off_divisor N n radicand D η hη hres _ (hD z hz)) hz₀ hz₁
  have hσD : ∀ t, D (σ t) = 0 := by
    intro t
    obtain ⟨z, hz, he⟩ := hσ t
    rw [← he]
    exact hD z hz
  rw [htrans _ _ σ (hD _ hz₀) (hD _ hz₁) hσD, hint]


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
