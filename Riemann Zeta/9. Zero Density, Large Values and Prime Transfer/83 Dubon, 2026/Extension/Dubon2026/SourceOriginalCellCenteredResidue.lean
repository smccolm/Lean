import Dubon2026.SourceCellCenteredResidue
import Dubon2026.SourceOriginalCellResidues
import Dubon2026.SourceOriginalCellPrimitives

/-! DUB-17/18 -> raw reciprocity -> actual pole-centered cell residue identity.
Apply the planar centered contour theorem to the actual original coefficient,
including multiplication by a holomorphic primitive. The residue is the literal
original algebraic residue, with the exact positive 2*pi*I normalization.
The source dissection supplies pole-centered cells; constructing that dissection
and assembling edge jumps remain separate obligations.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter MeasureTheory KaehlerDifferential
open scoped Real Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem Cell.analyticAt_coeff_off_center (C : Cell N) (v : Place ℂ F) (θ : Ω[F⁄ℂ])
    (hcenter : C.ζ v = C.R.q)
    (hθreg : ∀ Q ∈ C.carrier, Q ≠ v → 0 ≤ Q.ordDifferential θ)
    {z : ℂ} (hz : z ∈ C.R.K) (hn : z ≠ C.R.q) : AnalyticAt ℂ (coeffIn C.ζ θ) z := by
  apply C.toAnalyticCoord.analyticAt_coeff θ (C.hKt hz)
  apply (C.ζ.symm z).mem_of_ord_nonneg
  apply hθreg _ ⟨z, hz, rfl⟩
  intro he
  apply hn
  rw [← C.ζ.right_inv (C.hKt hz), he, hcenter]

theorem Cell.centered_residue (C : Cell N) (v : Place ℂ F) (hv : v ∈ C.ζ.source)
    (hcenter : C.ζ v = C.R.q) (θ : Ω[F⁄ℂ]) (hθ : -1 ≤ v.ordDifferential θ)
    (hθreg : ∀ Q ∈ C.carrier, Q ≠ v → 0 ≤ Q.ordDifferential θ) :
    IntervalIntegrable (C.bdryIntegrand θ) volume 0 (2 * π) ∧
      (∫ φ in (0 : ℝ)..(2 * π), C.bdryIntegrand θ φ) =
        2 * π * Complex.I * originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) := by
  apply C.R.centered_residue (coeffIn C.ζ θ)
  · exact fun z hz hn => C.analyticAt_coeff_off_center v θ hcenter hθreg hz hn
  · simpa only [hcenter] using C.toAnalyticCoord.coeff_simple_pole hv θ hθ

theorem Cell.centered_weighted_residue (C : Cell N) (v : Place ℂ F) (hv : v ∈ C.ζ.source)
    (hcenter : C.ζ v = C.R.q) (θ : Ω[F⁄ℂ]) (hθ : -1 ≤ v.ordDifferential θ)
    (hθreg : ∀ Q ∈ C.carrier, Q ≠ v → 0 ≤ Q.ordDifferential θ)
    (Ψ : ℂ → ℂ) (hΨ : ∀ z ∈ C.R.K, AnalyticAt ℂ Ψ z) :
    IntervalIntegrable (fun φ => (coeffIn C.ζ θ (C.R.loop φ) * Ψ (C.R.loop φ)) * C.R.loop' φ)
      volume 0 (2 * π) ∧
      (∫ φ in (0 : ℝ)..(2 * π),
        (coeffIn C.ζ θ (C.R.loop φ) * Ψ (C.R.loop φ)) * C.R.loop' φ) =
        2 * π * Complex.I *
          (originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) * Ψ C.R.q) := by
  let r := originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ)
  apply C.R.centered_residue (fun z => coeffIn C.ζ θ z * Ψ z) (r * Ψ C.R.q)
  · exact fun z hz hn => (C.analyticAt_coeff_off_center v θ hcenter hθreg hz hn).mul (hΨ z hz)
  · obtain ⟨g, hga, hge⟩ := C.toAnalyticCoord.coeff_simple_pole hv θ hθ
    rw [hcenter] at hga hge
    have hΨ0 := hΨ C.R.q C.R.center_mem_K
    refine ⟨fun z => r * dslope Ψ C.R.q z + g z * Ψ z,
      (analyticAt_const.mul (analyticAt_dslope hΨ0)).add (hga.mul hΨ0), ?_⟩
    filter_upwards [hge, self_mem_nhdsWithin] with z hz hne
    have hn : z - C.R.q ≠ 0 := sub_ne_zero.mpr hne
    have hs := sub_smul_dslope Ψ C.R.q z
    rw [smul_eq_mul] at hs
    have he : Ψ z = Ψ C.R.q + (z - C.R.q) * dslope Ψ C.R.q z := by
      rw [hs]
      ring
    rw [hz]
    change (r / (z - C.R.q) + g z) * Ψ z = _
    rw [he]
    field_simp
    ring

end
end Dubon2026.SourceFunctionField.CellGeometry
