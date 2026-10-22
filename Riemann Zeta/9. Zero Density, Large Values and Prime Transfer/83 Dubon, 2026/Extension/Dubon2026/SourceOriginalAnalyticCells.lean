import Dubon2026.SourceOriginalAnalyticCellCoordinates

/-! DUB-17/18 -> raw geometric reciprocity -> actual analytic cells.
The source radial domain inside an actual original-place coordinate has a
compact carrier and an open interior. Its surrounding star-convex domain is
derived from the planar theorem, giving the domain needed for cell primitives.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace

/-- A source radial cell in a genuine coordinate on the original curve. -/
structure Cell (N : ℕ) [NeZero N] extends AnalyticCoord N where
  /-- The exact source radial region defining the cell. -/
  R : RadialRegion
  hKt : R.K ⊆ ζ.target

namespace Cell
variable {N : ℕ} [NeZero N]

/-- The actual compact set of original places covered by the cell. -/
def carrier (C : Cell N) : Set (Place ℂ (modularFunctionFieldOver N ℂ)) := C.ζ.symm '' C.R.K
/-- The actual open set of original places inside the radial boundary. -/
def interior' (C : Cell N) : Set (Place ℂ (modularFunctionFieldOver N ℂ)) := C.ζ.symm '' C.R.Kint
/-- The actual radial boundary lifted to original places. -/
def bdry (C : Cell N) (φ : ℝ) : Place ℂ (modularFunctionFieldOver N ℂ) := C.ζ.symm (C.R.loop φ)
/-- The actual original-place image of a smooth radial boundary arc. -/
def arc (C : Cell N) (k : Fin C.R.N) : Set (Place ℂ (modularFunctionFieldOver N ℂ)) :=
  C.ζ.symm '' C.R.arcSet k
/-- The genuine original differential evaluated along the radial boundary. -/
def bdryIntegrand (C : Cell N) (θ : Ω[modularFunctionFieldOver N ℂ⁄ℂ]) (s : ℝ) : ℂ :=
  coeffIn C.ζ θ (C.R.loop s) * C.R.loop' s

theorem carrier_isCompact (C : Cell N) : IsCompact C.carrier :=
  C.R.isCompact_K.image_of_continuousOn (C.ζ.continuousOn_symm.mono C.hKt)

theorem interior_isOpen (C : Cell N) : IsOpen C.interior' := by
  apply (C.ζ.symm.isOpen_image_iff_of_subset_source ?_).mpr C.R.isOpen_Kint
  intro z hz
  apply C.hKt
  change ‖z - C.R.q‖ ≤ C.R.r (Complex.arg (z - C.R.q))
  exact (show ‖z - C.R.q‖ < C.R.r (Complex.arg (z - C.R.q)) from hz).le

theorem exists_primitive_domain (C : Cell N) :
    ∃ V : Set ℂ, IsOpen V ∧ C.R.q ∈ V ∧ StarConvex ℝ C.R.q V ∧
      C.R.K ⊆ V ∧ V ⊆ C.ζ.target :=
  C.R.exists_open_starConvex_neighborhood C.ζ.target C.ζ.open_target C.hKt

end Cell
end
end Dubon2026.SourceFunctionField.CellGeometry
