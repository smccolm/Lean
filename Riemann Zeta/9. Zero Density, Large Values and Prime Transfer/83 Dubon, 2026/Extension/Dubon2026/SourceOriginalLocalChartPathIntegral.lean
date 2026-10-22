import Dubon2026.SourceOriginalLocalChartPathPrimitive

/-! DUB-17/18 -> original torsion cardinality -> Abel-Jacobi converse ->
global meromorphic exponential -> local transport. Native path connectedness
of an open chart region constructs actual original paths whose integrals
are the endpoint differences of its local primitive.
-/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve Filter Set Metric KaehlerDifferential
open scoped Topology
variable (N : ℕ) [NeZero N]
attribute [local instance] placeTopology
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_local_chart_path_integral (ω : Ω[F⁄ℂ])
    (v : Place ℂ F) {W : Set ℂ} (hW : IsOpen W) (hpath : IsPathConnected W)
    (hsub : W ⊆ ball (0 : ℂ) (placeRadius N v)) (Φ : ℂ → ℂ)
    (hΦ : ∀ z ∈ W, HasDerivAt Φ (readDifferential N v ω z) z)
    (hω : ∀ z ∈ W, (placeFamily N v z).differentialCoeff ω ∈
      (placeFamily N v z).toValuationSubring)
    {z₀ z₁ : ℂ} (hz₀ : z₀ ∈ W) (hz₁ : z₁ ∈ W) :
    ∃ γ : Path (placeFamily N v z₀) (placeFamily N v z₁),
      (∀ t, γ t ∈ placeFamily N v '' W) ∧ pathIntegral N ω γ = Φ z₁ - Φ z₀ := by
  obtain ⟨δ, hδ⟩ := hpath.joinedIn z₀ hz₀ z₁ hz₁
  have hc : ContinuousOn (placeFamily N v) (range δ) :=
    (continuousOn_placeFamily N v).mono (by rintro _ ⟨t, rfl⟩; exact hsub (hδ t))
  let γ := δ.map' hc
  have hγ : ∀ t, γ t ∈ (placeChart N v).source := fun t => ⟨δ t, hsub (hδ t), rfl⟩
  have hγW : ∀ t, placeChart N v (γ t) ∈ W := by
    intro t
    change placeChart N v (placeFamily N v (δ t)) ∈ W
    rw [show placeChart N v (placeFamily N v (δ t)) = δ t from
      place_eval_uniformizer N v (hsub (hδ t))]
    exact hδ t
  refine ⟨γ, fun t => ⟨δ t, hδ t, rfl⟩, ?_⟩
  rw [pathIntegral_eq_of_isPrimitiveAlong N
    (isPrimitiveAlong_of_local_chart_primitive N ω v hW Φ hΦ γ hγ hγW
      (fun t => hω (δ t) (hδ t))), γ.target, γ.source]
  rw [show placeChart N v (placeFamily N v z₁) = z₁ from place_eval_uniformizer N v (hsub hz₁),
    show placeChart N v (placeFamily N v z₀) = z₀ from place_eval_uniformizer N v (hsub hz₀)]

end
end Dubon2026.SourceFunctionField.OriginalChart
