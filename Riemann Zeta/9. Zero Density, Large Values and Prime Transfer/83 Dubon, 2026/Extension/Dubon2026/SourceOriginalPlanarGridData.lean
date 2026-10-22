import Dubon2026.SourceCellPlanarGridData
import Dubon2026.SourceOriginalCenteredGlobalCover

/-! DUB-17/18 -> original Abel-Jacobi -> actual geometric arc pairing.
The constructed original-cell cover supplies the source planar grid object,
including the exact square and refined outer-boundary formulas. No planar
geometry input is assumed separately from that actual cover.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
noncomputable section
open Set
variable {N : ℕ} [NeZero N] {Marked : Finset ℂ} (A : OriginalGlobalCellCover N Marked)

/-- Source planar pairing data extracted from the constructed original cover. -/
def planarData : PlanarRegions.GridData where
  o := A.G.D.o
  hm := A.G.D.h
  hhm := A.G.D.mesh_pos
  jlo := A.G.D.lo
  jhi := A.G.D.hi
  klo := A.G.D.lo
  khi := A.G.D.hi
  hjlt := A.G.D.window_nontrivial
  hklt := A.G.D.window_nontrivial
  ctr := A.G.D.center
  hctr := A.G.D.center_inside
  hzero := ⟨⟨A.G.windowData.hx₀, A.G.windowData.hx₁⟩, A.G.windowData.hy₀, A.G.windowData.hy₁⟩
  hcy0 := A.G.windowData.hcy0
  base := A.G.region
  hbase := A.G.rectangle
  winReg := A.W.R
  hwin := ⟨A.W.q_eq, A.W.K_eq, A.W.Kint_eq, A.W.N_eq, A.W.arcSet_inj, A.W.arc_cases,
    A.W.exists_arc_bot, A.W.exists_arc_top, A.W.exists_arc_leftUp, A.W.exists_arc_leftLow,
    A.W.exists_arc_rightLow, A.W.exists_arc_rightUp⟩

theorem planarData_base (p : ℤ × ℤ) : A.planarData.base p = A.G.region p := rfl

theorem planarData_window : A.planarData.winReg = A.W.R := rfl

end
end Dubon2026.SourceFunctionField.CellGeometry.OriginalGlobalCellCover
