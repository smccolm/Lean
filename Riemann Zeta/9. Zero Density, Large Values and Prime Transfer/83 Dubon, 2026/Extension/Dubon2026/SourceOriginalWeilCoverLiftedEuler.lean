import Dubon2026.SourceOriginalWeilCoverLiftedVertexCount
import Dubon2026.SourceOriginalLiftedEulerMultiplicity
import Dubon2026.SourceOriginalWeilCoverUnramifiedGenus
import Dubon2026.SourceOriginalDissectionEulerIdentity

/-! DUB-17/18 -> cover reciprocity -> exact Euler genus identity.
The actual finite cell, edge and vertex counts multiply the proved base Euler
identity by the cover degree. The independently proved unramified canonical-
degree/genus formula identifies this with the actual regular-differential genus.
No cover Euler or cycle-count premise is supplied. -/
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





theorem cover_lifted_euler_identity (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
    ∀ (ζ : (i : A.Index) → J i → OpenPartialHomeomorph (Place ℂ EE) ℂ),
      (∀ i j z, z ∈ (A.cell i).R.K → ((ζ i j).symm z).restrict FF = (A.cell i).ζ.symm z) →
      (∀ i (w : Place ℂ EE), w.restrict FF ∈ (A.cell i).carrier →
        ∃ j, w ∈ (ζ i j).symm '' (A.cell i).R.K) →
      (Nat.card (CellPairing.LiftedVertex (cell := A.cell) J (fun i j => (ζ i j).symm)) : ℤ) -
          (Nat.card (Σ e : A.pairing.Edge, J e.1.1) : ℤ) + (Nat.card (Σ i : A.Index, J i) : ℤ) =
        2 - 2 * (Module.finrank ℂ (regularDifferentials ℂ EE) : ℤ) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI : FiniteDimensional FF EE := Place.kummerFinite n radicand
  let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
  letI : ∀ i, Finite (J i) := fun i => Place.finite_placeFiber (E := EE) ((A.cell i).ζ.symm (A.cell i).R.q)
  letI : ∀ i, Fintype (J i) := fun i => Fintype.ofFinite (J i)
  dsimp only
  intro ζ hp hx
  have hv := cover_lifted_vertex_count N n radicand baseDivisor hRadicand hOrders Marked A ζ hp hx
  have hmul := A.pairing.lifted_euler_multiplicity J (fun i j => (ζ i j).symm) (Module.finrank FF EE)
    (fun i => card_restriction_fiber N n radicand baseDivisor hRadicand hOrders ((A.cell i).ζ.symm (A.cell i).R.q)) hv
  have hbase := A.dissection_euler_identity
  change (Fintype.card (CellPairing.Vertex (cell := A.cell)) : ℤ) -
      (Fintype.card A.pairing.Edge : ℤ) + (Fintype.card A.Index : ℤ) = _ at hbase
  rw [hbase] at hmul
  have hgenus := cover_euler_genus_multiplicity N n radicand baseDivisor hRadicand hOrders
  rw [hgenus]
  simpa only [Nat.card_eq_fintype_card] using hmul

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
