import Dubon2026.SourceOriginalPairedBoundarySum
import Dubon2026.SourceOriginalDissectionSkeletonRegularity
import Dubon2026.SourceOriginalDissectionCellResidues

/-! DUB-17/18 -> raw reciprocity -> global weighted residue-jump identity.
Actual centered per-cell residue formulas and actual paired-edge cancellation
assemble to the full finite identity. Pole-free skeleton regularity and all
arc integrability conditions are derived from the source dissection outputs.
The following consumer will supply the primitives and edge identities as well.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set MeasureTheory KaehlerDifferential
open scoped Real
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

open scoped Classical in
theorem CellDissection.weighted_residue_jump_sum (𝒟 : CellDissection N)
    (S : Finset (Place ℂ F))
    (hsep : ∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (hcent : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧
      (𝒟.cell C).ζ v = (𝒟.cell C).R.q)
    (θ : Ω[F⁄ℂ]) (hθpol : ∀ v ∈ S, -1 ≤ v.ordDifferential θ)
    (hθreg : ∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ)
    (Ψ : 𝒟.ιC → ℂ → ℂ) (hΨ : ∀ C z, z ∈ (𝒟.cell C).R.K → AnalyticAt ℂ (Ψ C) z)
    (J : 𝒟.ιE → ℂ)
    (hedge : ∀ e,
      𝒟.arcInt (fun C s => Ψ C ((𝒟.cell C).R.loop s) * (𝒟.cell C).bdryIntegrand θ s)
        (𝒟.arcOf (e, true)) +
      𝒟.arcInt (fun C s => Ψ C ((𝒟.cell C).R.loop s) * (𝒟.cell C).bdryIntegrand θ s)
        (𝒟.arcOf (e, false)) = J e * 𝒟.edgeInt θ e) :
    2 * π * Complex.I * ∑ C : 𝒟.ιC, ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell C).carrier),
      originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) * Ψ C ((𝒟.cell C).ζ v) =
        ∑ e : 𝒟.ιE, J e * 𝒟.edgeInt θ e := by
  classical
  let H : 𝒟.ιC → ℝ → ℂ := fun C s => Ψ C ((𝒟.cell C).R.loop s) * (𝒟.cell C).bdryIntegrand θ s
  have hskel := 𝒟.regular_on_skeleton S
    (fun v hv => let ⟨C, hi, _⟩ := hcent v hv; ⟨C, hi⟩) θ hθreg
  have hint : ∀ C (k : Fin (𝒟.cell C).R.N), IntervalIntegrable (H C) volume
      ((𝒟.cell C).R.φs k.castSucc) ((𝒟.cell C).R.φs k.succ) := by
    intro C k
    apply ((𝒟.cell C).weighted_arc_integral_extension k θ
      (fun s hs => hskel _ (𝒟.bdry_mem_skeleton C k hs)) _ ?_).1
    intro s _
    exact ((hΨ C _ ((𝒟.cell C).R.loop_mem_K s)).continuousAt.comp
      (𝒟.cell C).R.continuous_loop.continuousAt).continuousWithinAt
  have hcell : ∀ C, (∫ s in (0 : ℝ)..(2 * π), H C s) =
      2 * π * Complex.I * ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell C).carrier),
        originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) * Ψ C ((𝒟.cell C).ζ v) := by
    intro C
    have hr := (𝒟.weighted_cell_residue S hsep hcent θ hθpol hθreg C (Ψ C) (hΨ C)).2
    rw [← hr]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [H, Cell.bdryIntegrand]
    ring
  calc
    _ = ∑ C : 𝒟.ιC, ∫ s in (0 : ℝ)..(2 * π), H C s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun C _ => (hcell C).symm
    _ = ∑ e : 𝒟.ιE, (𝒟.arcInt H (𝒟.arcOf (e, true)) + 𝒟.arcInt H (𝒟.arcOf (e, false))) :=
      𝒟.sum_cell_integrals_eq_sum_paired H hint
    _ = _ := Finset.sum_congr rfl fun e _ => hedge e

end
end Dubon2026.SourceFunctionField.CellGeometry
