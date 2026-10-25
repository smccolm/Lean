import Dubon2026.SourceOriginalWeilCoverWeightedResidueJumpSum
import Dubon2026.SourceRadialPoleCarrierSum

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel converse ->
weighted residue reciprocity. Reuse the centered planar residue theorem,
finite interval partition and exact constructed primitive jumps. These prove
the global identity with the actual algebraic residues and cell coordinates. -/
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

open scoped Real

open RadialDissectionPeriods
variable {κ : Type*}

theorem cover_normalized_primitive_analytic :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (_ : CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ)
    (i : κ) (C : D.ιC) {z : ℂ} (_ : z ∈ (D.cell C).R.K),
    AnalyticAt ℂ (Ψ i C) z := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ hP i C z hz
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [(hP.2.1 C).mem_nhds (hP.2.2.1 C hz)] with w hw
  exact (hP.2.2.2.1 i C w hw).differentiableAt


theorem cover_normalized_weighted_residue_sum :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ)
    (_ : CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ) (_ : IsJump D Ψ J) (S : Finset (Place ℂ EE))
    (_ : ∀ C : D.ιC, ((D.cell C).carrier ∩ (S : Set (Place ℂ EE))).Subsingleton)
    (_ : ∀ v ∈ S, ∃ C : D.ιC, v ∈ (D.cell C).interior' ∧
      (D.cell C).ζ v = (D.cell C).R.q)
    (c : Place ℂ EE → D.ιC) (_ : ∀ v ∈ S, v ∈ (D.cell (c v)).interior')
    (θ : Ω[EE⁄ℂ]) (_ : ∀ v ∈ S, -1 ≤ v.ordDifferential θ)
    (_ : ∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential θ) (i : κ),
    2 * π * Complex.I * ∑ v ∈ S,
      v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ) *
        Ψ i (c v) ((D.cell (c v)).ζ v) = ∑ e, J e i * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ J hP hJ S hsep hcent c hc θ hpol hreg i
  have hskel := cover_regular_on_skeleton N n radicand baseDivisor hRadicand hOrders D S (fun v hv => ⟨c v, hc v hv⟩) θ hreg
  have hsum := cover_weighted_residue_jump_sum N n radicand baseDivisor hRadicand hOrders D hP.1 S hsep hcent θ hpol hreg (Ψ i)
    (fun C z hz => cover_normalized_primitive_analytic N n radicand baseDivisor hRadicand hOrders D η V Ψ hP i C hz)
    (fun e => J e i) (fun e => cover_normalized_weighted_edge_cancellation N n radicand baseDivisor hRadicand hOrders D η V Ψ J hP hJ θ hskel e i)
  rw [D.sum_pole_carriers S c hc] at hsum
  exact hsum

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
