import Dubon2026.SourceOriginalWeilRestrictionCovering
import Dubon2026.SourceOriginalAnalyticCells
import Dubon2026.SourceCellBoundaryGeometry

/-! DUB-17/18 -> lifted dissection -> pairing actual lifted boundary arcs.
The original arc reparameterization lifts unchanged: equality at one endpoint
and the literal restriction formulas force equality along the entire connected
arc, by the pinned covering uniqueness theorem. -/
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

theorem lifted_boundary_arcs_eq_of_endpoint (C C' : CellGeometry.Cell N) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ ζ' : OpenPartialHomeomorph (Place ℂ EE) ℂ),
      C.R.K ⊆ ζ.target → C'.R.K ⊆ ζ'.target →
      (∀ z ∈ ζ.target, (ζ.symm z).restrict FF = C.ζ.symm z) →
      (∀ z ∈ ζ'.target, (ζ'.symm z).restrict FF = C'.ζ.symm z) →
      ∀ (a b t₀ : ℝ) (ψ : ℝ → ℝ), ContinuousOn ψ (Icc a b) →
        (∀ t ∈ Icc a b, C'.bdry t = C.bdry (ψ t)) → t₀ ∈ Icc a b →
        ζ'.symm (C'.R.loop t₀) = ζ.symm (C.R.loop (ψ t₀)) →
        ∀ t ∈ Icc a b, ζ'.symm (C'.R.loop t) = ζ.symm (C.R.loop (ψ t)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ ζ' hK hK' hp hp' a b t₀ ψ hψ hbase ht₀ h₀
  have hc : Continuous (fun t => ζ.symm (C.R.loop t)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (ζ.continuousAt_symm (hK (C.R.loop_mem_K t))).comp C.R.continuous_loop.continuousAt
  have hc' : Continuous (fun t => ζ'.symm (C'.R.loop t)) :=
    continuous_iff_continuousAt.mpr fun t =>
      (ζ'.continuousAt_symm (hK' (C'.R.loop_mem_K t))).comp C'.R.continuous_loop.continuousAt
  apply (isCoveringMap_restriction N n radicand baseDivisor hRadicand hOrders).eqOn_of_comp_eqOn
    isPreconnected_Icc hc'.continuousOn (hc.comp_continuousOn hψ) ?_ ht₀ h₀
  intro t ht
  change (ζ'.symm (C'.R.loop t)).restrict FF = (ζ.symm (C.R.loop (ψ t))).restrict FF
  rw [hp' _ (hK' (C'.R.loop_mem_K t)), hp _ (hK (C.R.loop_mem_K (ψ t)))]
  exact hbase t ht

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
