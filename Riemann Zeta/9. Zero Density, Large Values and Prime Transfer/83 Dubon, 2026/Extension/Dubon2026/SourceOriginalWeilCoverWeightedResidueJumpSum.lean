import Dubon2026.SourceOriginalWeilCoverDissectionCellResidues
import Dubon2026.SourceOriginalWeilCoverNormalizedWeightedEdges
import Dubon2026.SourceRadialPairedBoundarySum
import Dubon2026.SourceRadialPoleSkeleton

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

theorem cover_regular_on_skeleton :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE))
    (S : Finset (Place ℂ EE))
    (_ : ∀ v ∈ S, ∃ C : D.ιC, v ∈ (D.cell C).interior')
    (θ : Ω[EE⁄ℂ]) (_ : ∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential θ),
    ∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential θ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D S hinter θ hθ v hv
  exact hθ v fun hS => D.pole_not_mem_skeleton S hinter hS hv

open scoped Classical in
theorem cover_weighted_residue_jump_sum :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE))
    (_ : ∀ C P, P ∈ (D.cell C).ζ.source →
      AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0)
    (S : Finset (Place ℂ EE))
    (_ : ∀ C : D.ιC, ((D.cell C).carrier ∩ (S : Set (Place ℂ EE))).Subsingleton)
    (_ : ∀ v ∈ S, ∃ C : D.ιC, v ∈ (D.cell C).interior' ∧
      (D.cell C).ζ v = (D.cell C).R.q)
    (θ : Ω[EE⁄ℂ]) (_ : ∀ v ∈ S, -1 ≤ v.ordDifferential θ)
    (_ : ∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential θ)
    (Ψ : D.ιC → ℂ → ℂ) (_ : ∀ C z, z ∈ (D.cell C).R.K → AnalyticAt ℂ (Ψ C) z)
    (J : D.ιE → ℂ)
    (_ : ∀ e,
      D.arcInt (fun C s => Ψ C ((D.cell C).R.loop s) * BI (D.cell C) θ s)
        (D.arcOf (e, true)) +
      D.arcInt (fun C s => Ψ C ((D.cell C).R.loop s) * BI (D.cell C) θ s)
        (D.arcOf (e, false)) = J e * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e),
    2 * π * Complex.I * ∑ C : D.ιC, ∑ v ∈ S.filter (fun v => v ∈ (D.cell C).carrier),
      v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ) * Ψ C ((D.cell C).ζ v) =
        ∑ e : D.ιE, J e * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S hsep hcent θ hθpol hθreg Ψ hΨ J hedge
  classical
  let H : D.ιC → ℝ → ℂ := fun C s => Ψ C ((D.cell C).R.loop s) * BI (D.cell C) θ s
  have hskel := cover_regular_on_skeleton N n radicand baseDivisor hRadicand hOrders D S
    (fun v hv => let ⟨C, hi, _⟩ := hcent v hv; ⟨C, hi⟩) θ hθreg
  have hint : ∀ C (k : Fin (D.cell C).R.N), IntervalIntegrable (H C) volume
      ((D.cell C).R.φs k.castSucc) ((D.cell C).R.φs k.succ) := by
    intro C k
    apply (cover_weighted_arc_integral_extension N n radicand baseDivisor hRadicand hOrders (D.cell C) (hD C) k θ
      (fun s hs => hskel _ (D.bdry_mem_skeleton C k hs)) _ ?_).1
    intro s _
    exact ((hΨ C _ ((D.cell C).R.loop_mem_K s)).continuousAt.comp
      (D.cell C).R.continuous_loop.continuousAt).continuousWithinAt
  have hcell : ∀ C, (∫ s in (0 : ℝ)..(2 * π), H C s) =
      2 * π * Complex.I * ∑ v ∈ S.filter (fun v => v ∈ (D.cell C).carrier),
        v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ) * Ψ C ((D.cell C).ζ v) := by
    intro C
    have hr := (cover_weighted_cell_residue N n radicand baseDivisor hRadicand hOrders D hD S hsep hcent θ hθpol hθreg C (Ψ C) (hΨ C)).2
    rw [← hr]
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only [H, coverBoundaryIntegrand]
    ring
  calc
    _ = ∑ C : D.ιC, ∫ s in (0 : ℝ)..(2 * π), H C s := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun C _ => (hcell C).symm
    _ = ∑ e : D.ιE, (D.arcInt H (D.arcOf (e, true)) + D.arcInt H (D.arcOf (e, false))) :=
      D.sum_cell_integrals_eq_sum_paired H hint
    _ = _ := Finset.sum_congr rfl fun e _ => hedge e

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
