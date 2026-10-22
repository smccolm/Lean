import Dubon2026.SourceOriginalDissectionCellCount
import Dubon2026.SourceOriginalRamifiedArcCounts

/-! DUB-17/18 -> original Abel-Jacobi -> the exact edge term of Euler.
Ordinary squares contribute six arcs per j sheet; each branch square has the
same total by the original degree sum. The exterior contributes the degree
times the actual refined window perimeter. No unproved count is supplied.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ}

theorem OriginalJFiniteGrid.sum_interior_arcs (G : OriginalJFiniteGrid N Marked) :
    (∑ i : G.InteriorIndex, ((G.interiorCell i).R.N : ℤ)) =
      6 * (SourceLevelProjective.dedekindPsi N : ℤ) * (G.D.hi - G.D.lo + 1).toNat ^ 2 := by
  classical
  have ho (p : G.PlainIndex) (i : Fin (SourceLevelProjective.dedekindPsi N)) :
      ((G.ordinary p.1 p.2).C i).R.N = 6 := by
    rw [(G.ordinary p.1 p.2).region_eq]
    exact (G.rectangle p.1).2.1
  have hb (b : ({0, 1728} : Finset ℂ)) :
      (∑ v, (((G.branch (G.branchSquare b) b (G.branch_cap b)).C v).R.N : ℤ)) =
        (SourceLevelProjective.dedekindPsi N : ℤ) * 6 := by
    rw [OriginalBranchRegionFamily.sum_arcs, (G.rectangle (G.branchSquare b)).2.1]
    norm_num
  change (∑ i : (G.PlainIndex × Fin (SourceLevelProjective.dedekindPsi N)) ⊕
    (Σ b : ({0, 1728} : Finset ℂ), ↥(originalPositiveFiber N (jOver N ℂ) b)),
      ((G.interiorCell i).R.N : ℤ)) = _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_sigma]
  change (∑ p : G.PlainIndex, ∑ i, (((G.ordinary p.1 p.2).C i).R.N : ℤ)) +
    (∑ b : ({0, 1728} : Finset ℂ), ∑ v,
      (((G.branch (G.branchSquare b) b (G.branch_cap b)).C v).R.N : ℤ)) = _
  simp only [ho, hb, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hc : Fintype.card ({0, 1728} : Finset ℂ) = 2 := by simp
  rw [hc]
  have hplain : (Fintype.card G.PlainIndex : ℤ) + 2 =
      ((G.D.hi - G.D.lo + 1).toNat : ℤ) ^ 2 := by exact_mod_cast G.plain_card_add_two
  push_cast
  nlinarith

namespace OriginalGlobalCellCover
variable (A : OriginalGlobalCellCover N Marked)

theorem window_arc_count : A.W.R.N = 6 * (A.G.D.hi - A.G.D.lo + 1).toNat := by
  rw [A.W.N_eq]
  change 2 * (A.G.D.hi - A.G.D.lo + 1).toNat +
    4 * (A.G.D.hi - A.G.D.lo + 1).toNat = _
  omega

theorem sum_cell_arcs :
    (∑ i : A.Index, ((A.cell i).R.N : ℤ)) =
      6 * (SourceLevelProjective.dedekindPsi N : ℤ) * (A.G.D.hi - A.G.D.lo + 1).toNat ^ 2 +
      6 * (SourceLevelProjective.dedekindPsi N : ℤ) * (A.G.D.hi - A.G.D.lo + 1).toNat := by
  change (∑ i : A.G.InteriorIndex ⊕ ↥(originalPositiveFiber N (jOver N ℂ)⁻¹ 0),
    ((A.cell i).R.N : ℤ)) = _
  rw [Fintype.sum_sum_type]
  change (∑ i : A.G.InteriorIndex, ((A.G.interiorCell i).R.N : ℤ)) +
    (∑ v, ((A.poles.C v).R.N : ℤ)) = _
  rw [A.G.sum_interior_arcs, A.poles.sum_arcs, A.window_arc_count]
  push_cast
  ring

end OriginalGlobalCellCover
end
end Dubon2026.SourceFunctionField.CellGeometry
