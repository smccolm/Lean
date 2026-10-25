import Dubon2026.SourceCoverLiftedCoordinateFamily
import Dubon2026.SourceOriginalWeilCoverCellLift

/-! DUB-17/18 -> cover raw reciprocity -> actual finite lifted cell family.
All lifts of an original radial cell are indexed by the actual finite fiber
above its center. They are disjoint analytic coordinate sheets and their
compact radial carriers exhaust the literal restriction preimage of the cell.
No assumed covering, lift, sheet count or analyticity premise remains. -/
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

theorem exists_cover_cell_lift_family (C : CellGeometry.Cell N) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    let I := {w : Place ℂ EE // w.restrict FF = C.ζ.symm C.R.q}
    ∃ (V : Set ℂ) (ζ : I → OpenPartialHomeomorph (Place ℂ EE) ℂ),
      IsOpen V ∧ C.R.q ∈ V ∧ StarConvex ℝ C.R.q V ∧ C.R.K ⊆ V ∧ V ⊆ C.ζ.target ∧
      Nat.card I = Module.finrank FF EE ∧
      (∀ i, (ζ i).target = V ∧ i.1 ∈ (ζ i).source ∧ ζ i i.1 = C.R.q) ∧
      (∀ i z, z ∈ V → ((ζ i).symm z).restrict FF = C.ζ.symm z) ∧
      (∀ i P, P ∈ (ζ i).source → P.restrict FF ∈ C.ζ.source ∧ ζ i P = C.ζ (P.restrict FF)) ∧
      (Pairwise fun i j => Disjoint (ζ i).source (ζ j).source) ∧
      (∀ w, w.restrict FF ∈ C.carrier → ∃ i, w ∈ (ζ i).symm '' C.R.K) ∧
      (∀ i P, P ∈ (ζ i).source →
        AnalyticAt ℂ (ζ i ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv (ζ i ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) := by
  classical
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  obtain ⟨V, hV, hq, hc, hK, hVe⟩ := C.exists_primitive_domain
  have hl := SheetCover.exists_coordinate_family_of_starConvex (fun P : Place ℂ EE => P.restrict FF)
    (isCoveringMap_restriction N n radicand baseDivisor hRadicand hOrders) C.ζ hV hq hc hVe
  obtain ⟨ζ, hcenter, hinverse, hmap, hd, hx⟩ := hl
  refine ⟨V, ζ, hV, hq, hc, hK, hVe,
    card_restriction_fiber N n radicand baseDivisor hRadicand hOrders _,
    hcenter, hinverse, hmap, hd, ?_, ?_⟩
  · intro w hw
    obtain ⟨z, hz, he⟩ := hw
    obtain ⟨i, hi⟩ := hx w z (hK hz) he.symm
    exact ⟨i, z, hz, hi⟩
  · intro i
    exact analytic_lifted_coordinate N n radicand baseDivisor hRadicand hOrders C.toAnalyticCoord (ζ i) (hmap i)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
