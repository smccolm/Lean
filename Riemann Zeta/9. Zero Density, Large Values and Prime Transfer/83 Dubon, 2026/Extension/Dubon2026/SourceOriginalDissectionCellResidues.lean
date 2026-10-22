import Dubon2026.SourceOriginalCellDissectionInteriors
import Dubon2026.SourceOriginalCellCenteredResidue

/-! DUB-17/18 -> raw reciprocity -> per-cell weighted residue sums.
The exact source dissection outputs (one pole per carrier and a centered cell
for each pole) imply the centered-contour hypotheses for every cell. Thus the
shorter centered route proves the full per-cell residue sum required downstream.
Existence of the dissection, edge pairing and the global jump formula remain.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter MeasureTheory KaehlerDifferential
open scoped Real Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

open scoped Classical in
theorem CellDissection.weighted_cell_residue (𝒟 : CellDissection N)
    (S : Finset (Place ℂ F))
    (hsep : ∀ C : 𝒟.ιC, ((𝒟.cell C).carrier ∩ (S : Set (Place ℂ F))).Subsingleton)
    (hcent : ∀ v ∈ S, ∃ C : 𝒟.ιC, v ∈ (𝒟.cell C).interior' ∧
      (𝒟.cell C).ζ v = (𝒟.cell C).R.q)
    (θ : Ω[F⁄ℂ]) (hθpol : ∀ v ∈ S, -1 ≤ v.ordDifferential θ)
    (hθreg : ∀ v : Place ℂ F, v ∉ S → 0 ≤ v.ordDifferential θ)
    (C : 𝒟.ιC) (Ψ : ℂ → ℂ) (hΨ : ∀ z ∈ (𝒟.cell C).R.K, AnalyticAt ℂ Ψ z) :
    IntervalIntegrable
      (fun φ => (coeffIn (𝒟.cell C).ζ θ ((𝒟.cell C).R.loop φ) * Ψ ((𝒟.cell C).R.loop φ)) *
        (𝒟.cell C).R.loop' φ) volume 0 (2 * π) ∧
      (∫ φ in (0 : ℝ)..(2 * π),
        (coeffIn (𝒟.cell C).ζ θ ((𝒟.cell C).R.loop φ) * Ψ ((𝒟.cell C).R.loop φ)) *
          (𝒟.cell C).R.loop' φ) =
        2 * π * Complex.I * ∑ v ∈ S.filter (fun v => v ∈ (𝒟.cell C).carrier),
          originalPlaceEval N ℂ v (v.uniformizer * v.differentialCoeff θ) * Ψ ((𝒟.cell C).ζ v) := by
  classical
  let T := S.filter (fun v => v ∈ (𝒟.cell C).carrier)
  by_cases hT : T.Nonempty
  · obtain ⟨v, hvT⟩ := hT
    have hv := Finset.mem_filter.mp hvT
    obtain ⟨hvs, hvc⟩ := 𝒟.pole_center_on_carrier S hcent C v hv.1 hv.2
    have hreg : ∀ Q ∈ (𝒟.cell C).carrier, Q ≠ v → 0 ≤ Q.ordDifferential θ := by
      intro Q hQC hQv
      apply hθreg Q
      intro hQS
      exact hQv (hsep C ⟨hQC, hQS⟩ ⟨hv.2, hv.1⟩)
    have hsingle : T = {v} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hvT, ?_⟩
      intro Q hQT
      have hQ := Finset.mem_filter.mp hQT
      exact hsep C ⟨hQ.2, hQ.1⟩ ⟨hv.2, hv.1⟩
    have hcalc := (𝒟.cell C).centered_weighted_residue v hvs hvc θ (hθpol v hv.1) hreg Ψ hΨ
    change _ ∧ _ = 2 * π * Complex.I * ∑ v ∈ T, _
    simpa only [hsingle, Finset.sum_singleton, hvc] using hcalc
  · have hTempty : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
    have hreg : ∀ Q ∈ (𝒟.cell C).carrier, 0 ≤ Q.ordDifferential θ := by
      intro Q hQC
      apply hθreg Q
      intro hQS
      have hQT : Q ∈ T := Finset.mem_filter.mpr ⟨hQS, hQC⟩
      rw [hTempty] at hQT
      exact Finset.notMem_empty Q hQT
    have ha : ∀ z ∈ (𝒟.cell C).R.K,
        AnalyticAt ℂ (fun z => coeffIn (𝒟.cell C).ζ θ z * Ψ z) z := by
      intro z hz
      exact ((𝒟.cell C).toAnalyticCoord.analyticAt_coeff θ ((𝒟.cell C).hKt hz)
        (((𝒟.cell C).ζ.symm z).mem_of_ord_nonneg (hreg _ ⟨z, hz, rfl⟩))).mul (hΨ z hz)
    have hcalc := (𝒟.cell C).R.integral_eq_zero_of_analyticOnNhd _ ha
    change _ ∧ _ = 2 * π * Complex.I * ∑ v ∈ T, _
    simpa only [hTempty, Finset.sum_empty, mul_zero] using hcalc

end
end Dubon2026.SourceFunctionField.CellGeometry
