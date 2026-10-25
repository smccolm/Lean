import Dubon2026.SourceOriginalWeilCoverLiftedVertexCount
import Dubon2026.SourceOriginalConstructedPolygonWord

/-! DUB-17/18 -> actual reciprocity polygon -> nonempty cotree complement.
Reuse the proved base two-vertex bound and the exact lifted-vertex count.
The actual finite field degree is positive, so the lifted dissection has
at least two vertices even in genus zero. No positive-genus premise is added. -/
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




theorem cover_lifted_vertex_count_ge_two (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
    ∀ (ζ : (i : A.Index) → J i → OpenPartialHomeomorph (Place ℂ EE) ℂ),
      (∀ i j z, z ∈ (A.cell i).R.K → ((ζ i j).symm z).restrict FF = (A.cell i).ζ.symm z) →
      (∀ i (w : Place ℂ EE), w.restrict FF ∈ (A.cell i).carrier →
        ∃ j, w ∈ (ζ i j).symm '' (A.cell i).R.K) →
      2 ≤ Nat.card (CellPairing.LiftedVertex (cell := A.cell) J (fun i j => (ζ i j).symm)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI : FiniteDimensional FF EE := Place.kummerFinite n radicand
  dsimp only
  intro ζ hp hx
  have hv := cover_lifted_vertex_count N n radicand baseDivisor hRadicand hOrders Marked A ζ hp hx
  rw [hv]
  have hb := A.two_le_vertex_count
  change 2 ≤ Fintype.card (CellPairing.Vertex (cell := A.cell)) at hb
  have hbn : 2 ≤ Nat.card (CellPairing.Vertex (cell := A.cell)) := by
    simpa only [Nat.card_eq_fintype_card] using hb
  have hd : 1 ≤ Module.finrank FF EE := Module.finrank_pos
  calc
    2 ≤ Nat.card (CellPairing.Vertex (cell := A.cell)) * 1 := by simpa only [Nat.mul_one] using hbn
    _ ≤ Nat.card (CellPairing.Vertex (cell := A.cell)) * Module.finrank FF EE := Nat.mul_le_mul_left _ hd

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
