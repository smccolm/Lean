import Dubon2026.SourceRadialCellCarrierNeighborhoods
import Dubon2026.SourceRadialPolygonPrimitiveData

/-! DUB-17/18 -> cover Abel converse -> regular loop generation. The actual
cell primitive readings define the atlas used by the existing path argument. -/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
noncomputable section
variable {X : Type*} [TopologicalSpace X] {κ : Type*}

/-- A cell primitive chart corrected by its center value. -/
def Gchart (D : RadialCellDissection X) (Ψ : κ → D.ιC → ℂ → ℂ) (x y : X) : κ → ℂ :=
  gvec D Ψ y (cellOf D y) - gvec D Ψ x (cellOf D y) + gvec D Ψ x (cellOf D x)

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
