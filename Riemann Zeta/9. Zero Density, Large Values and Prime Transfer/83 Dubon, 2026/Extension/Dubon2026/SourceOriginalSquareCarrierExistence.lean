import Dubon2026.SourceOriginalDissectionEndpointImages

/-! DUB-17/18 -> original Abel-Jacobi -> surjectivity of the vertex-fiber description.
Every regular original place over a specified square lies in one of that
square's actual cells. Reuse exact family coverage and the existing unique
branch-square assignment, without reconstructing sheet or branch charts.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)
local notation "F" => modularFunctionFieldOver N ℂ

theorem exists_cell_over_square {p : ℤ × ℤ}
    (hp : p ∈ Icc A.G.D.lo A.G.D.hi ×ˢ Icc A.G.D.lo A.G.D.hi) {P : Place ℂ F}
    (hx : jOver N ℂ ∈ P.toValuationSubring)
    (hv : originalPlaceEval N ℂ P (jOver N ℂ) ∈ (A.G.region p).K) :
    ∃ i : A.Index, A.regionOf i = some p ∧ P ∈ (A.cell i).carrier := by
  have hp' : p ∈ A.G.squares := Finset.mem_product.mpr
    ⟨Finset.mem_Icc.mpr hp.1, Finset.mem_Icc.mpr hp.2⟩
  cases hc : A.G.D.capAt p with
  | none =>
    obtain ⟨i, hi⟩ := ((A.G.ordinary p hc).coverage P).mp ⟨hx, hv⟩
    exact ⟨.inl (.inl (⟨⟨p, hp'⟩, hc⟩, i)), rfl, hi⟩
  | some b =>
    obtain ⟨hb, hj, hk⟩ := (A.G.D.cap_exact p b).mp hc
    let b' : ({0, 1728} : Finset ℂ) := ⟨b, hb⟩
    have he : A.G.branchSquare b' = p := Prod.ext hj hk
    subst p
    obtain ⟨v, hv⟩ := ((A.G.branch (A.G.branchSquare b') b' (A.G.branch_cap b')).coverage P).mp ⟨hx, hv⟩
    exact ⟨.inl (.inr ⟨b', v⟩), rfl, hv⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
