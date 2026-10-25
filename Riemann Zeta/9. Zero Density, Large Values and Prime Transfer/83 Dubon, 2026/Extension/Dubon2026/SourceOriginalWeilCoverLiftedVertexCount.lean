import Dubon2026.SourceOriginalLiftedVertexFibers
import Dubon2026.SourceFiniteFiberPreimageCard
import Dubon2026.SourceOriginalWeilCoverCenteredDissection

/-! DUB-17/18 -> cover Euler/cycle count -> exact actual vertex multiplicity.
The literal lifted vertices are exactly the inverse image of the base vertices.
The proved finite unramified restriction fibers and native fiber-cardinality
sum give the exact cover-degree factor without a vertex-count premise. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Topology CellGeometry
attribute [local instance] OriginalChart.placeTopology restrictionIntegral
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders




theorem cover_lifted_vertex_count (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
    ∀ (ζ : (i : A.Index) → J i → OpenPartialHomeomorph (Place ℂ EE) ℂ),
      (∀ i j z, z ∈ (A.cell i).R.K → ((ζ i j).symm z).restrict FF = (A.cell i).ζ.symm z) →
      (∀ i (w : Place ℂ EE), w.restrict FF ∈ (A.cell i).carrier →
        ∃ j, w ∈ (ζ i j).symm '' (A.cell i).R.K) →
      Nat.card (CellPairing.LiftedVertex (cell := A.cell) J (fun i j => (ζ i j).symm)) =
        Nat.card (CellPairing.Vertex (cell := A.cell)) * Module.finrank FF EE := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI : FiniteDimensional FF EE := Place.kummerFinite n radicand
  let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
  dsimp only
  intro ζ hp hx
  have he := CellPairing.lifted_vertices_eq_preimage (fun w : Place ℂ EE => w.restrict FF) J ζ hp hx
  rw [he]
  exact SheetCover.card_preimage_of_constant_fibers (fun w : Place ℂ EE => w.restrict FF)
    (CellPairing.Vertex (cell := A.cell)) (Module.finrank FF EE)
    (fun v => Place.finite_placeFiber (E := EE) v.1)
    (fun v => card_restriction_fiber N n radicand baseDivisor hRadicand hOrders v.1)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
