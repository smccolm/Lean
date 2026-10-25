import Dubon2026.SourceRadialCellClosedCarriers

/-! DUB-17/18 -> cover Abel converse -> regular loop-period generation.
This is a necessary step in converting arbitrary actual path integrals into
the subgroup of the constructed primitive jumps. Adapted from
S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Reuse original cell compactness, coefficient pullback and primitive uniqueness;
no new ambient curve, manifold, compactness or primitive existence is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
noncomputable section
open Set Filter RadialCellDissection
open scoped Topology
variable {X : Type*} [TopologicalSpace X] {κ : Type*}

/-- Closed carriers not containing the chosen point. Their complement is a useful neighborhood. -/
def badCarrierSet (D : RadialCellDissection X) (x : X) : Set (X) :=
  ⋃ C ∈ {C : D.ιC | x ∉ (D.cell C).carrier}, (D.cell C).carrier

theorem isClosed_badCarrierSet [T2Space X] (D : RadialCellDissection X) (x : X) :
    IsClosed (badCarrierSet D x) :=
  (Set.toFinite _).isClosed_biUnion fun C _ => (D.cell C).carrier_isClosed

theorem not_mem_badCarrierSet_self (D : RadialCellDissection X) (x : X) :
    x ∉ badCarrierSet D x := by
  rintro hx
  obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
  exact hC hxC

theorem mem_carrier_of_not_mem_badCarrierSet (D : RadialCellDissection X) {x y : X}
    (hy : y ∉ badCarrierSet D x) {C : D.ιC} (hyC : y ∈ (D.cell C).carrier) :
    x ∈ (D.cell C).carrier := by
  by_contra h
  exact hy (mem_iUnion₂.mpr ⟨C, h, hyC⟩)

theorem exists_mem_carrier (D : RadialCellDissection X) (y : X) :
    ∃ C : D.ιC, y ∈ (D.cell C).carrier := by
  have : y ∈ ⋃ C, (D.cell C).carrier := by rw [D.cover]; exact mem_univ y
  exact mem_iUnion.mp this

/-- A cell containing the specified actual cover place. -/
def cellOf (D : RadialCellDissection X) (y : X) : D.ιC :=
  (exists_mem_carrier D y).choose

theorem mem_cellOf (D : RadialCellDissection X) (y : X) :
    y ∈ (D.cell (cellOf D y)).carrier :=
  (exists_mem_carrier D y).choose_spec

end
end Dubon2026.SourceFunctionField.CellGeometry.RadialDissectionPeriods
