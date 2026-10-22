import Dubon2026.SourceOriginalGridCellIndex

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite cell cover.
The finite family covers exactly the full original j preimage of the closed
grid window. This consumes the constructed sheet and branch families, not
an independently supplied cell cover.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalJFiniteGrid
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (G : OriginalJFiniteGrid N Marked)
local notation "F" => modularFunctionFieldOver N ℂ

theorem interiorCell_coverage (P : Place ℂ F) :
    (jOver N ℂ ∈ P.toValuationSubring ∧ originalPlaceEval N ℂ P (jOver N ℂ) ∈ G.window) ↔
    ∃ i : G.InteriorIndex, P ∈ (G.interiorCell i).carrier := by
  classical
  constructor
  · rintro ⟨hreg, hwindow⟩
    obtain ⟨j, hj, k, hk, hsquare⟩ := G.D.window_covered hwindow
    let p : ℤ × ℤ := (j, k)
    have hp : p ∈ G.squares := Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr hj, Finset.mem_Icc.mpr hk⟩
    have hregion : originalPlaceEval N ℂ P (jOver N ℂ) ∈ (G.region p).K := by
      rw [(G.rectangle p).2.2.1]
      exact hsquare
    cases hc : G.D.capAt p with
    | none =>
      obtain ⟨i, hi⟩ := ((G.ordinary p hc).coverage P).mp ⟨hreg, hregion⟩
      exact ⟨.inl (⟨⟨p, hp⟩, hc⟩, i), hi⟩
    | some b =>
      obtain ⟨hb, hx, hy⟩ := (G.D.cap_exact p b).mp hc
      let b' : ({0, 1728} : Finset ℂ) := ⟨b, hb⟩
      have he : G.branchSquare b' = p := Prod.ext hx hy
      have hregion' : originalPlaceEval N ℂ P (jOver N ℂ) ∈ (G.region (G.branchSquare b')).K :=
        he.symm ▸ hregion
      obtain ⟨v, hv⟩ := ((G.branch (G.branchSquare b') b' (G.branch_cap b')).coverage P).mp
        ⟨hreg, hregion'⟩
      exact ⟨.inr ⟨b', v⟩, hv⟩
  · rintro ⟨i, hi⟩
    cases i with
    | inl p =>
      obtain ⟨hreg, hregion⟩ := ((G.ordinary p.1.1 p.1.2).coverage P).mpr ⟨p.2, hi⟩
      refine ⟨hreg, G.square_subset_window p.1.1.2 ?_⟩
      rw [(G.rectangle p.1.1).2.2.1] at hregion
      exact hregion
    | inr p =>
      obtain ⟨hreg, hregion⟩ :=
        ((G.branch (G.branchSquare p.1) p.1 (G.branch_cap p.1)).coverage P).mpr ⟨p.2, hi⟩
      refine ⟨hreg, G.square_subset_window (G.branchSquare_mem p.1) ?_⟩
      rw [(G.rectangle (G.branchSquare p.1)).2.2.1] at hregion
      exact hregion

theorem exists_original_finite_window_cell_cover (N : ℕ) [NeZero N] (Marked : Finset ℂ) :
    ∃ G : OriginalJFiniteGrid N Marked, ∀ P : Place ℂ (modularFunctionFieldOver N ℂ),
      (jOver N ℂ ∈ P.toValuationSubring ∧ originalPlaceEval N ℂ P (jOver N ℂ) ∈ G.window) ↔
      ∃ i : G.InteriorIndex, P ∈ (G.interiorCell i).carrier := by
  obtain ⟨G⟩ := exists_original_j_finite_grid N Marked
  exact ⟨G, G.interiorCell_coverage⟩

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalJFiniteGrid
