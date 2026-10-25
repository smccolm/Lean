import Dubon2026.SourceRadialCellDissection

/-! DUB-17/18 -> cover Abel converse -> regular loop generation -> path-to-jump
comparison. Compact radial carriers give the finite closed-carrier neighborhoods
used by the existing path-atlas argument. No compactness premise is assumed. -/
namespace Dubon2026.SourceFunctionField.CellGeometry
open Set
variable {X : Type*} [TopologicalSpace X]

theorem RadialCell.carrier_isCompact (C : RadialCell X) : IsCompact C.carrier :=
  C.R.isCompact_K.image_of_continuousOn (C.ζ.continuousOn_symm.mono C.hKt)

theorem RadialCell.carrier_isClosed [T2Space X] (C : RadialCell X) : IsClosed C.carrier :=
  C.carrier_isCompact.isClosed

end Dubon2026.SourceFunctionField.CellGeometry
