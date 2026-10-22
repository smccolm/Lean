import Dubon2026.SourceOriginalPoweredArcMatching
import Dubon2026.SourceOriginalGridCellFamilies

/-! DUB-17/18 -> original Abel-Jacobi -> actual exterior arc matching.
Reuse the proved original inverse-j reciprocal-region equivalence to obtain
exact carrier coverage. Connected power-arc matching then identifies the
unique pole-cell boundary arc over each inverse-j base arc.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalPoleRegionFamily
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {W : RadialRegion} (B : OriginalPoleRegionFamily N W)
local notation "F" => modularFunctionFieldOver N ℂ

theorem inverse_carrier_coverage (hW : W.q = 0) (P : Place ℂ F) :
    ((jOver N ℂ)⁻¹ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ ∈ B.R.K) ↔ ∃ v, P ∈ (B.C v).carrier :=
  (original_inverse_j_mem_reciprocal_iff N W B.R hW B.reciprocal.1
    B.reciprocal.2.2.2.1 P).trans (B.coverage P)

theorem exists_unique_inverse_arc_over (hW : W.q = 0) (k : Fin B.R.N) {L : Set (Place ℂ F)}
    (hL : IsPreconnected L) (hne : L.Nonempty)
    (hover : ∀ P ∈ L, (jOver N ℂ)⁻¹ ∈ P.toValuationSubring ∧
      originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ ∈ B.R.arcSet k)
    (honto : B.R.arcSet k ⊆ (fun P => originalPlaceEval N ℂ P (jOver N ℂ)⁻¹) '' L) :
    ∃! a : Σ v, Fin (B.C v).R.N, L = (B.C a.1).arc a.2 := by
  have hcov : L ⊆ ⋃ v, (B.C v).carrier := by
    intro P hP
    obtain ⟨v, hv⟩ := (B.inverse_carrier_coverage hW P).mp
      ⟨(hover P hP).1, B.R.arcSet_subset_K k (hover P hP).2⟩
    exact mem_iUnion.mpr ⟨v, hv⟩
  obtain ⟨v, hLv⟩ := ArcSelection.exists_subset_of_finite_closed hL hne
    (fun v => (B.C v).carrier_isClosed) B.disjoint hcov
  have hread (P : Place ℂ F) (hP : P ∈ (B.C v).ζ.source) :
      originalPlaceEval N ℂ P (jOver N ℂ)⁻¹ = B.R.q + (B.C v).ζ P ^
        ((v : Place ℂ F).ord (jOver N ℂ)⁻¹).toNat := by
    rw [B.reciprocal.1, zero_add]
    exact ((B.geometry v).2.2.2 P hP).2
  obtain ⟨a, ha, _, _⟩ := (B.C v).exists_powered_arc_over (B.geometry v).2.2.1 k
    (fun P => originalPlaceEval N ℂ P (jOver N ℂ)⁻¹) hread hL hne hLv
    (fun P hP => (hover P hP).2) honto
  refine ⟨⟨v, a⟩, ha, ?_⟩
  intro a' ha'
  exact eq_arc_index_of_disjoint_carriers B.C B.disjoint a' ⟨v, a⟩ (ha'.symm.trans ha)

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalPoleRegionFamily
