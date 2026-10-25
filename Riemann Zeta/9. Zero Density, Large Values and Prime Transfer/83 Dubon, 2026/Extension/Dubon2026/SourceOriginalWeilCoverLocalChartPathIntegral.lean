import Dubon2026.SourceOriginalWeilCoverLocalChartPathPrimitive

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


theorem exists_cover_local_chart_path_integral (ω : Ω[EE⁄ℂ])
    (v : Place ℂ EE) {W : Set ℂ} (hW : IsOpen W) (hpath : IsPathConnected W)
    (hsub : W ⊆ ball (0 : ℂ) (placeRadius N n radicand A hRadicand hOrders v)) (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ W, HasDerivAt Φ (readDifferential N n radicand A hRadicand hOrders v ω z) z)
    (hω : ∀ z ∈ W, (placeFamily N n radicand A hRadicand hOrders v z).differentialCoeff ω ∈
      (placeFamily N n radicand A hRadicand hOrders v z).toValuationSubring)
    {z₀ z₁ : ℂ} (hz₀ : z₀ ∈ W) (hz₁ : z₁ ∈ W) :
    ∃ γ : CoverPath (placeFamily N n radicand A hRadicand hOrders v z₀) (placeFamily N n radicand A hRadicand hOrders v z₁),
      (∀ t, γ t ∈ placeFamily N n radicand A hRadicand hOrders v '' W) ∧ pathIntegral N n radicand A hRadicand hOrders ω γ = Φ z₁ - Φ z₀ := by
  letI := placeTopology N n radicand A hRadicand hOrders
  obtain ⟨δ, hδ⟩ := hpath.joinedIn z₀ hz₀ z₁ hz₁
  have hc : ContinuousOn (placeFamily N n radicand A hRadicand hOrders v) (range δ) :=
    (continuousOn_placeFamily N n radicand A hRadicand hOrders v).mono (by rintro _ ⟨t, rfl⟩; exact hsub (hδ t))
  let γ := δ.map' hc
  have hγ : ∀ t, γ t ∈ (placeChart N n radicand A hRadicand hOrders v).source := fun t => ⟨δ t, hsub (hδ t), rfl⟩
  have hγW : ∀ t, placeChart N n radicand A hRadicand hOrders v (γ t) ∈ W := by
    intro t
    change placeChart N n radicand A hRadicand hOrders v (placeFamily N n radicand A hRadicand hOrders v (δ t)) ∈ W
    rw [show placeChart N n radicand A hRadicand hOrders v (placeFamily N n radicand A hRadicand hOrders v (δ t)) = δ t from
      place_eval_uniformizer N n radicand A hRadicand hOrders v (hsub (hδ t))]
    exact hδ t
  refine ⟨γ, fun t => ⟨δ t, hδ t, rfl⟩, ?_⟩
  rw [pathIntegral_eq_of_isPrimitiveAlong N n radicand A hRadicand hOrders
    (isPrimitiveAlong_of_local_chart_primitive N n radicand A hRadicand hOrders ω v hW Φ hΦ γ hγ hγW
      (fun t => hω (δ t) (hδ t))), γ.target, γ.source]
  rw [show placeChart N n radicand A hRadicand hOrders v (placeFamily N n radicand A hRadicand hOrders v z₁) = z₁ from place_eval_uniformizer N n radicand A hRadicand hOrders v (hsub hz₁),
    show placeChart N n radicand A hRadicand hOrders v (placeFamily N n radicand A hRadicand hOrders v z₀) = z₀ from place_eval_uniformizer N n radicand A hRadicand hOrders v (hsub hz₀)]


end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
