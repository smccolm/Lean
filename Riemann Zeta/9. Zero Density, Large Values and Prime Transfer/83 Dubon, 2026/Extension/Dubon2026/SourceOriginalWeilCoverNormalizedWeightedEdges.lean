import Dubon2026.SourceOriginalWeilCoverWeightedEdgeCancellation
import Dubon2026.SourceOriginalWeilCoverPathPrimitiveData
import Dubon2026.SourceOriginalWeilCoverEdgePathIntegral
import Dubon2026.SourceRadialPairedArcOverlap

/-! DUB-17/18 -> cover Abel converse -> weighted residue reciprocity.
Use the existing C1 reversed-arc substitution on the actual coefficient.
The actual dissection supplies the overlap and geometry; its constructed
primitive derivatives and constant jumps give the weighted cancellation. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
open scoped Topology
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders
local notation "PC" => placeChart N n radicand baseDivisor hRadicand hOrders
local notation "PF" => placeFamily N n radicand baseDivisor hRadicand hOrders
local notation "RD" => readDifferential N n radicand baseDivisor hRadicand hOrders
local notation "CF" => coverCoeffIn N n radicand baseDivisor hRadicand hOrders

local notation "BI" => coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders

open MeasureTheory

open RadialDissectionPeriods

theorem cover_normalized_weighted_edge_cancellation {κ : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ])
      (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ),
      CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ → IsJump D Ψ J →
      ∀ (θ : Ω[EE⁄ℂ]), (∀ x ∈ D.skeleton, 0 ≤ x.ordDifferential θ) → ∀ (e : D.ιE) (i : κ),
      let p := D.arcOf (e, true)
      let q := D.arcOf (e, false)
      (∫ s in ((D.cell p.1).R.φs p.2.castSucc)..((D.cell p.1).R.φs p.2.succ),
        Ψ i p.1 ((D.cell p.1).R.loop s) * BI (D.cell p.1) θ s) +
      (∫ s in ((D.cell q.1).R.φs q.2.castSucc)..((D.cell q.1).R.φs q.2.succ),
        Ψ i q.1 ((D.cell q.1).R.loop s) * BI (D.cell q.1) θ s) =
        J e i * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ J hP hJ θ hθ e i
  dsimp only
  let p := D.arcOf (e, true)
  let q := D.arcOf (e, false)
  have hp : D.side p.1 p.2 = (e, true) := D.side_arcOf _
  have hq : D.side q.1 q.2 = (e, false) := D.side_arcOf _
  obtain ⟨ψ, hanti, hc, ha, hb, hbd⟩ := D.arc_rev p.1 p.2 q.1 q.2
    (by rw [hp, hq]) (by rw [hp]) (by rw [hq])
  have hreg : ∀ s ∈ (D.cell p.1).R.arcIcc p.2, 0 ≤ ((D.cell p.1).bdry s).ordDifferential θ := by
    intro s hs
    apply hθ
    exact mem_iUnion.2 ⟨p, _, ⟨s, hs, rfl⟩, rfl⟩
  exact cover_weighted_edge_cancellation N n radicand baseDivisor hRadicand hOrders
    (D.cell p.1) (D.cell q.1) (hP.1 p.1) (hP.1 q.1) p.2 q.2 ψ hanti hc ha hb hbd
    (D.paired_arc_overlap e) θ hreg (Ψ i p.1) (Ψ i q.1)
    (fun w hw => (hP.2.2.2.1 i p.1 w (hP.2.2.1 p.1 hw)).continuousAt)
    (fun w hw => (hP.2.2.2.1 i q.1 w (hP.2.2.1 q.1 hw)).continuousAt) (J e i) (hJ i e)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
