import Dubon2026.SourceCellGridSeparation
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Complex.Basic

/-! The literal closed grid squares used by the source dissection.
Compactness and convexity allow the proved simply connected covering route.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
open Set

/-- The closed square with integer grid index `(j,k)`. -/
def gridSquare (o h : ℝ) (j k : ℤ) : Set ℂ :=
  {z | z.re ∈ Icc (o + j * h) (o + (j + 1) * h) ∧
    z.im ∈ Icc (o + k * h) (o + (k + 1) * h)}

theorem corner_mem {o h : ℝ} (hh : 0 < h) (j k : ℤ) :
    (⟨o + j * h, o + k * h⟩ : ℂ) ∈ gridSquare o h j k := by
  refine ⟨⟨le_rfl, ?_⟩, ⟨le_rfl, ?_⟩⟩ <;> dsimp <;> nlinarith

theorem isCompact_gridSquare (o h : ℝ) (j k : ℤ) : IsCompact (gridSquare o h j k) :=
  isCompact_Icc.reProdIm isCompact_Icc

theorem convex_gridSquare (o h : ℝ) (j k : ℤ) : Convex ℝ (gridSquare o h j k) := by
  exact ((convex_Icc _ _).linear_preimage Complex.reLm).inter
    ((convex_Icc _ _).linear_preimage Complex.imLm)

end Dubon2026.SourceFunctionField.CellGeometry.SquareGrid
