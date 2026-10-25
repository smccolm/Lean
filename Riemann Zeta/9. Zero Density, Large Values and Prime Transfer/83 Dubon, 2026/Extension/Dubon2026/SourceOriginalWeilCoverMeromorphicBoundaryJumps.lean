import Dubon2026.SourceOriginalWeilCoverMeromorphicBoundaryValues
import Dubon2026.SourceOriginalWeilCoverReversedArcIntegrand
import Dubon2026.SourceRadialMeromorphicBoundaryJumps

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
The actual coordinate reversal law supplies the integrand identity. Apply
the boundary-constant theorem to construct the logarithmic primitive jumps
on every actual paired edge, with the exact reversed parameterization. -/
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



theorem exists_cover_meromorphic_boundary_jumps {R : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ PF P) 0 ∧ deriv ((D.cell C).ζ ∘ PF P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (θ : R → Ω[EE⁄ℂ])
      {V : D.ιC → Set ℂ} {Ψ : R → D.ιC → ℂ → ℂ},
      RadialMeromorphicPeriods.RegPrimData D S
        (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S θ) V Ψ →
      ∃ J : D.ιE → R → ℂ, RadialMeromorphicPeriods.IsJumpH D
        (coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ) J := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S θ V Ψ hP
  let H := coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S θ Ψ
  let B : R → D.ιC → ℝ → ℂ := fun r C =>
    coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders (D.cell C) (θ r)
  have hHc : ∀ r C, Continuous (fun s => H C s r) :=
    cover_continuous_meromorphicBoundary N n radicand baseDivisor hRadicand hOrders D S θ hP
  have hHd : ∀ r C (k : Fin (D.cell C).R.N) {s : ℝ},
      s ∈ Ioo ((D.cell C).R.φs k.castSucc) ((D.cell C).R.φs k.succ) →
      HasDerivAt (fun s => H C s r) (B r C s) s :=
    cover_hasDerivAt_meromorphicBoundary N n radicand baseDivisor hRadicand hOrders D S θ hP
  have key : ∀ e : D.ιE, ∃ (Je : R → ℂ) (ψ : ℝ → ℝ),
      StrictAntiOn ψ ((D.cell (D.arcOf (e, false)).1).R.arcIcc (D.arcOf (e, false)).2) ∧
      ψ ((D.cell (D.arcOf (e, false)).1).R.φs (D.arcOf (e, false)).2.castSucc) =
        (D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.succ ∧
      ψ ((D.cell (D.arcOf (e, false)).1).R.φs (D.arcOf (e, false)).2.succ) =
        (D.cell (D.arcOf (e, true)).1).R.φs (D.arcOf (e, true)).2.castSucc ∧
      (∀ t ∈ (D.cell (D.arcOf (e, false)).1).R.arcIcc (D.arcOf (e, false)).2,
        (D.cell (D.arcOf (e, false)).1).bdry t = (D.cell (D.arcOf (e, true)).1).bdry (ψ t)) ∧
      ∀ t ∈ (D.cell (D.arcOf (e, false)).1).R.arcIcc (D.arcOf (e, false)).2,
        H (D.arcOf (e, true)).1 (ψ t) - H (D.arcOf (e, false)).1 t = Je := by
    intro e
    obtain ⟨ψ, hanti, hC1, ha, hb, hbd⟩ := D.arc_rev (D.arcOf (e, true)).1 (D.arcOf (e, true)).2
      (D.arcOf (e, false)).1 (D.arcOf (e, false)).2
      (by rw [RadialCellDissection.side_arcOf, RadialCellDissection.side_arcOf]) (by rw [RadialCellDissection.side_arcOf]) (by rw [RadialCellDissection.side_arcOf])
    obtain ⟨Je, hJe⟩ := RadialMeromorphicPeriods.edge_pair_boundary H B hHc hHd _ _ _ _ ψ hanti hC1 ha hb (by
      intro r t d ht hder
      exact cover_reversed_arc_integrand N n radicand baseDivisor hRadicand hOrders
        (D.cell (D.arcOf (e, true)).1) (D.cell (D.arcOf (e, false)).1)
        (hD _) (hD _) _ _ ψ hanti ha hb hbd (θ r) ht hder)
    exact ⟨Je, ψ, hanti, ha, hb, hbd, hJe⟩
  choose J ψ h1 h2 h3 h4 h5 using key
  exact ⟨J, fun e => ⟨ψ e, h1 e, h2 e, h3 e, h4 e, h5 e⟩⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
