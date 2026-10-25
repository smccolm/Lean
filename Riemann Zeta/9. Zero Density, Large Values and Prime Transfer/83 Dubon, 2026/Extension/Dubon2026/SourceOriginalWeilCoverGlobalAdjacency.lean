import Dubon2026.SourceOriginalLiftedCoverAdjacency
import Dubon2026.SourceOriginalWeilCoverGlobalIntersection
import Dubon2026.SourceOriginalWeilCoverConnected

/-! DUB-17/18 -> actual cover dissection -> global adjacency.
The literal cover is connected and Hausdorff, its lifted radial carriers
are compact and nonempty, and its cell index is finite by the actual fiber
finiteness theorem. Pointwise intersection chains therefore connect all cells. -/
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


theorem cover_global_adjacency (Marked : Finset ℂ) (A : OriginalGlobalCellCover N Marked) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
    ∀ (ζ : (i : A.Index) → J i → OpenPartialHomeomorph (Place ℂ EE) ℂ)
      (T : (e : A.pairing.Edge) → J e.1.1 ≃ J (A.pairing.pair e.1).1),
      (∀ i j, (A.cell i).R.K ⊆ (ζ i j).target) →
      (∀ w : Place ℂ EE, ∃ i : Σ c : A.Index, J c, w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K) →
      (∀ (i j : Σ c : A.Index, J c) (w : Place ℂ EE),
        w ∈ (ζ i.1 i.2).symm '' (A.cell i.1).R.K →
        w ∈ (ζ j.1 j.2).symm '' (A.cell j.1).R.K →
        Relation.ReflTransGen (A.LiftedPointStep J (fun c s => (ζ c s).symm) T w) i j) →
      ∀ i j : Σ c : A.Index, J c,
        Relation.ReflTransGen
          (fun a b : Σ c : A.Index, J c =>
            ∃ (k : Fin (A.cell a.1).R.N) (l : Fin (A.cell b.1).R.N),
              A.pairing.liftedPair J T ⟨⟨a.1, k⟩, a.2⟩ = ⟨⟨b.1, l⟩, b.2⟩) i j := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI := place_connectedSpace N n radicand baseDivisor hRadicand hOrders
  letI := place_t2Space N n radicand baseDivisor hRadicand hOrders
  letI : FiniteDimensional FF EE := Place.kummerFinite n radicand
  let J := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
  letI : ∀ i, Finite (J i) := fun i => Place.finite_placeFiber (E := EE) ((A.cell i).ζ.symm (A.cell i).R.q)
  dsimp only
  intro ζ T hK hcover hinter i j
  exact A.lifted_cover_adjacency J ζ T hK hcover hinter i j

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
