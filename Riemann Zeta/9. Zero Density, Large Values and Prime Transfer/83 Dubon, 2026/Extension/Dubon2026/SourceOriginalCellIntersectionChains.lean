import Dubon2026.SourceOriginalPairedIntersectionStep

/-! DUB-17/18 -> original Abel-Jacobi -> full actual cell intersection chains.
Lift the proved planar star chain through a common original place. Regional
carrier uniqueness identifies the final cell. Nonregular j places are
handled immediately by exterior-region uniqueness, without a pole-center lemma.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)
local notation "F" => modularFunctionFieldOver N ℂ

theorem intersection_chain (i j : A.Index) {P : Place ℂ F}
    (hi : P ∈ (A.cell i).carrier) (hj : P ∈ (A.cell j).carrier) :
    Relation.ReflTransGen (A.PairStep P) i j := by
  by_cases hx : jOver N ℂ ∈ P.toValuationSubring
  · have hchain := StarProperty.star A.planarData _ _ _
      (A.contains_of_mem_carrier i hx hi) (A.contains_of_mem_carrier j hx hj)
    have key : ∀ ρ : Option (ℤ × ℤ),
        Relation.ReflTransGen (A.Adj (originalPlaceEval N ℂ P (jOver N ℂ))) (A.regionOf i) ρ →
        ∃ k : A.Index, A.regionOf k = ρ ∧ P ∈ (A.cell k).carrier ∧
          Relation.ReflTransGen (A.PairStep P) i k := by
      intro ρ hρ
      induction hρ with
      | refl => exact ⟨i, rfl, hi, .refl⟩
      | tail _ hadj ih =>
        obtain ⟨k, hkρ, hk, hik⟩ := ih
        rw [← hkρ] at hadj
        obtain ⟨l, hlρ, hl, hkl⟩ := A.exists_intersection_step k hk hadj
        exact ⟨l, hlρ, hl, hik.trans hkl⟩
    obtain ⟨k, hkρ, hk, hik⟩ := key _ hchain
    exact (A.cell_eq_of_common_place k j hk hj hkρ) ▸ hik
  · have he : i = j := A.cell_eq_of_common_place i j hi hj
      ((A.region_eq_none_of_not_regular i hx hi).trans (A.region_eq_none_of_not_regular j hx hj).symm)
    subst j
    exact .refl

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
