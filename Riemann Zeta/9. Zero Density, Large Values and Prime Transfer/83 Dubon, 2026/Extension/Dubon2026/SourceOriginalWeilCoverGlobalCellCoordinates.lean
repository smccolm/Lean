import Dubon2026.SourceOriginalWeilCoverCellLiftFamily
import Dubon2026.SourceOriginalGlobalCellCover

/-! DUB-17/18 -> actual lifted dissection -> finite global radial cell cover.
Lift every cell of the already constructed original grid and pole cover.
The actual finite fibers give a finite total index and every cover place lies
in a lifted compact radial carrier. All coordinates retain their exact maps
and nonsingular analytic transitions. Boundary pairing remains separate. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Topology
attribute [local instance] OriginalChart.placeTopology restrictionIntegral
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders

theorem exists_cover_global_cell_coordinates (Marked : Finset ℂ)
    (A : CellGeometry.OriginalGlobalCellCover N Marked) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
      let I := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
      Finite (Σ i, I i) ∧
      ∃ (V : A.Index → Set ℂ) (ζ : (i : A.Index) → I i → OpenPartialHomeomorph (Place ℂ EE) ℂ),
        (∀ i, IsOpen (V i) ∧ (A.cell i).R.q ∈ V i ∧ StarConvex ℝ (A.cell i).R.q (V i) ∧
          (A.cell i).R.K ⊆ V i ∧ V i ⊆ (A.cell i).ζ.target) ∧
        (∀ i j, (ζ i j).target = V i ∧ j.1 ∈ (ζ i j).source ∧ ζ i j j.1 = (A.cell i).R.q) ∧
        (∀ i j z, z ∈ V i → ((ζ i j).symm z).restrict FF = (A.cell i).ζ.symm z) ∧
        (∀ i, Pairwise fun j k => Disjoint (ζ i j).source (ζ i k).source) ∧
        (∀ w, ∃ i j, w ∈ (ζ i j).symm '' (A.cell i).R.K) ∧
        (∀ i j P, P ∈ (ζ i j).source →
          AnalyticAt ℂ (ζ i j ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
            deriv (ζ i j ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) := by
  classical
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  letI : FiniteDimensional FF EE := Place.kummerFinite n radicand
  let I := fun i : A.Index => {w : Place ℂ EE // w.restrict FF = (A.cell i).ζ.symm (A.cell i).R.q}
  letI : ∀ i, Finite (I i) := fun i => Place.finite_placeFiber (E := EE) ((A.cell i).ζ.symm (A.cell i).R.q)
  have hcell (i : A.Index) := exists_cover_cell_lift_family N n radicand baseDivisor hRadicand hOrders (A.cell i)
  choose V ζ hV hq hc hK hVe hcard hcenter hres hmap hd hx han using hcell
  refine ⟨inferInstance, V, ζ, fun i => ⟨hV i, hq i, hc i, hK i, hVe i⟩,
    hcenter, hres, hd, ?_, han⟩
  intro w
  obtain ⟨i, hi⟩ := A.covers (w.restrict FF)
  obtain ⟨j, hj⟩ := hx i w hi
  exact ⟨i, j, hj⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
