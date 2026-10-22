import Dubon2026.SourceOriginalConstructedRawReciprocity
import Dubon2026.SourceOriginalReciprocityReindexData

/-! DUB-17/18 -> original Abel-Jacobi -> original Abel converse.
Construct every geometric clause of the existing Abel-converse consumer from
the actual original dissection, including the original residues and Abel map.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential OriginalChart
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N]
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_original_reindexed_reciprocity {n : ℕ}
    (b : Module.Basis (Fin n) ℂ (regularDifferentials ℂ F)) (P₀ : Place ℂ F)
    (S : Finset (Place ℂ F)) :
    OriginalRawReciprocityData (fun i => (b i : Ω[F⁄ℂ])) P₀ S := by
  classical
  obtain ⟨Marked, A, T, Ts, _, hcent, _, _, _, _, hc, _, _, _, _, _, _, γ, hγs, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, hR, _, _, _, _, _, _, _, _, _, _, _, _, _, hG, hB⟩ :=
    exists_original_raw_period_reciprocity.{0} P₀ S b
  have hn : Module.finrank ℂ (regularDifferentials ℂ F) = n := by
    simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
  have hinter : ∀ v ∈ insert P₀ (S : Set (Place ℂ F)),
      ∃ C : A.dissection.ιC, v ∈ (A.dissection.cell C).interior' := by
    intro v hv
    obtain ⟨C, hC, _⟩ := hcent v hv
    exact ⟨C, hC⟩
  exact reindex_original_reciprocity A.dissection (fun i => (b i : Ω[F⁄ℂ])) P₀ S T Ts γ
    (hc.trans (congrArg (fun z => 2 * z) hn)) hinter hγs hR hG hB

end
end Dubon2026.SourceFunctionField.CellGeometry
