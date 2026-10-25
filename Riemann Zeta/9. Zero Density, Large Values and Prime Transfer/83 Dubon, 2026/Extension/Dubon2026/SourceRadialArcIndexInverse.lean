import Dubon2026.SourceRadialDissectionArcPaths

/-! DUB-17/18 -> cover period generation -> primitive-jump circulation.
The actual side bijection identifies its chosen arc index in both directions,
as required to reindex the endpoint cancellation sum. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
variable {X : Type*} [TopologicalSpace X]

theorem RadialCellDissection.arcOf_side (D : RadialCellDissection X)
    (p : Σ C : D.ιC, Fin (D.cell C).R.N) : D.arcOf (D.side p.1 p.2) = p :=
  Function.leftInverse_surjInv D.side_bij p

end Dubon2026.SourceFunctionField.CellGeometry
