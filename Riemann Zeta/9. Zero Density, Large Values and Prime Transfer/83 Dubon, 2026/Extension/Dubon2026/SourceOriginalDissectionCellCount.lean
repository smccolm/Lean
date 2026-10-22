import Dubon2026.SourceOriginalGridCellCount
import Dubon2026.SourceOriginalDissectionGenusCount

/-! DUB-17/18 -> original Abel-Jacobi -> the exact original cell count.
The actual sum/product index types count ordinary sheets and the three
exceptional fibers. The already proved original genus identity eliminates
the exceptional cardinalities in the Euler calculation.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open SourceCurve Set
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

theorem card_cells_eq_fibers :
    Fintype.card A.Index = Fintype.card A.G.PlainIndex * SourceLevelProjective.dedekindPsi N +
      (originalPositiveFiber N (jOver N ℂ) 0).card +
      (originalPositiveFiber N (jOver N ℂ) 1728).card +
      (originalPositiveFiber N (jOver N ℂ)⁻¹ 0).card := by
  classical
  change Fintype.card (((A.G.PlainIndex × Fin (SourceLevelProjective.dedekindPsi N)) ⊕
    (Σ b : ({0, 1728} : Finset ℂ), ↥(originalPositiveFiber N (jOver N ℂ) b))) ⊕
    ↥(originalPositiveFiber N (jOver N ℂ)⁻¹ 0)) = _
  rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_sigma]
  simp only [Fintype.card_coe]
  rw [Finset.sum_coe_sort _ (fun b : ℂ => (originalPositiveFiber N (jOver N ℂ) b).card)]
  norm_num [Finset.sum_insert, add_assoc]

theorem dissection_cell_count :
    (Fintype.card A.dissection.ιC : ℤ) =
      (SourceLevelProjective.dedekindPsi N : ℤ) * (A.G.D.hi - A.G.D.lo + 1).toNat ^ 2 -
      SourceLevelProjective.dedekindPsi N + 2 -
      2 * (Module.finrank ℂ (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)) : ℤ) := by
  change (Fintype.card A.Index : ℤ) = _
  rw [A.card_cells_eq_fibers]
  push_cast
  have hplain : (Fintype.card A.G.PlainIndex : ℤ) + 2 =
      ((A.G.D.hi - A.G.D.lo + 1).toNat : ℤ) ^ 2 := by
    exact_mod_cast A.G.plain_card_add_two
  have hgen := original_exceptional_fiber_card_euler N
  nlinarith

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
