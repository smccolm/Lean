import Dubon2026.SourceOriginalGridWindow

/-! DUB-17/18 -> original Abel-Jacobi -> actual finite cell dissection.
Join the constructed interior grid cells and the actual pole cells over the
same refined outer window. This gives a finite analytic cell cover of every
original place. Pairing, intersection chains, marked-point separation and
Euler counting are still required for the source dissection theorem.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable (N : ℕ) [NeZero N]

/-- The actual grid and exterior cells on a common refined window. -/
structure OriginalGlobalCellCover (Marked : Finset ℂ) where
  /-- Constructed original grid and all its interior cells. -/
  G : OriginalJFiniteGrid N Marked
  /-- Constructed outer perimeter with all grid side subdivisions. -/
  W : GridWindow.WinData.Win G.windowData
  /-- Actual exterior pole cells for that same outer region. -/
  poles : OriginalPoleRegionFamily N W.R

namespace OriginalGlobalCellCover
variable {N} {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

/-- The finite index set combining interior and original pole cells. -/
def Index := A.G.InteriorIndex ⊕ ↥(originalPositiveFiber N (jOver N ℂ)⁻¹ 0)

instance : Fintype A.Index := by
  classical
  unfold Index
  infer_instance

/-- The actual analytic cell at each index of the global cover. -/
def cell : A.Index → Cell N
  | .inl i => A.G.interiorCell i
  | .inr v => A.poles.C v

theorem covers (P : Place ℂ (modularFunctionFieldOver N ℂ)) :
    ∃ i : A.Index, P ∈ (A.cell i).carrier := by
  by_cases hr : jOver N ℂ ∈ P.toValuationSubring
  · by_cases hw : originalPlaceEval N ℂ P (jOver N ℂ) ∈ A.G.window
    · obtain ⟨i, hi⟩ := (A.G.interiorCell_coverage P).mp ⟨hr, hw⟩
      exact ⟨.inl i, hi⟩
    · have hn : originalPlaceEval N ℂ P (jOver N ℂ) ∉ A.W.R.Kint := by
        intro h
        have hK : originalPlaceEval N ℂ P (jOver N ℂ) ∈ A.W.R.K := by
          change ‖originalPlaceEval N ℂ P (jOver N ℂ) - A.W.R.q‖ ≤
            A.W.R.r (Complex.arg (originalPlaceEval N ℂ P (jOver N ℂ) - A.W.R.q))
          exact (show ‖originalPlaceEval N ℂ P (jOver N ℂ) - A.W.R.q‖ <
            A.W.R.r (Complex.arg (originalPlaceEval N ℂ P (jOver N ℂ) - A.W.R.q)) from h).le
        rw [A.G.window_K_eq A.W] at hK
        exact hw hK
      obtain ⟨v, hv⟩ := (A.poles.coverage P).mp (Or.inr ⟨hr, hn⟩)
      exact ⟨.inr v, hv⟩
  · obtain ⟨v, hv⟩ := (A.poles.coverage P).mp (Or.inl hr)
    exact ⟨.inr v, hv⟩

end OriginalGlobalCellCover

theorem exists_original_global_cell_cover (Marked : Finset ℂ) :
    ∃ A : OriginalGlobalCellCover N Marked, ∀ P : Place ℂ (modularFunctionFieldOver N ℂ),
      ∃ i : A.Index, P ∈ (A.cell i).carrier := by
  obtain ⟨G⟩ := exists_original_j_finite_grid N Marked
  obtain ⟨W, ⟨poles⟩⟩ := G.exists_original_refined_window
  let A : OriginalGlobalCellCover N Marked := ⟨G, W, poles⟩
  exact ⟨A, A.covers⟩

end
end Dubon2026.SourceFunctionField.CellGeometry
