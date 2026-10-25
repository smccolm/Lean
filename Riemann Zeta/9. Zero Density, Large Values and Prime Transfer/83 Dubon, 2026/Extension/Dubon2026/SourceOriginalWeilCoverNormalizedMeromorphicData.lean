import Dubon2026.SourceOriginalWeilCoverMeromorphicPrimitiveData
import Dubon2026.SourceOriginalWeilCoverMeromorphicNormalizedJumps
import Dubon2026.SourceOriginalWeilCoverMeromorphicBoundaryPeriod
import Dubon2026.SourceOriginalWeilCoverMeromorphicBoundaryFTC

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
The actual finite simple-pole basis has normalized logarithmic primitives
with exact arc integrals, residue increments and zero dual-tree jumps. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Topology CellGeometry KaehlerDifferential
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders





open IntegerEdgeChains RadialDissectionTrees
open scoped Real
/-- An actual spanning basis and its common residue-subtracted cell primitives. -/
def CoverNormalizedMeromorphicPrimitives :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → Finset (Place ℂ EE) → Finset D.ιE → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D S Ts =>
        ∃ (d : ℕ) (bθ : Module.Basis (Fin d) ℂ (coverSimplePoleSpace N n radicand S))
          (Vθ : D.ιC → Set ℂ) (Ψθ : Fin d → D.ιC → ℂ → ℂ) (Jθ : D.ιE → Fin d → ℂ),
          (∀ θ : coverSimplePoleSpace N n radicand S, ∃ a : Fin d → ℂ,
            (θ : Ω[EE⁄ℂ]) = ∑ i, a i • (bθ i : Ω[EE⁄ℂ])) ∧
          RadialMeromorphicPeriods.PolePos D S ∧
          RadialMeromorphicPeriods.RegPrimData D S
            (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S
              (fun i : Fin d => (bθ i : Ω[EE⁄ℂ]))) Vθ Ψθ ∧
          RadialMeromorphicPeriods.IsJumpH D
            (coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S
              (fun i : Fin d => (bθ i : Ω[EE⁄ℂ])) Ψθ) Jθ ∧
          (∀ e ∈ Ts, Jθ e = 0) ∧
          (∀ (r : Fin d) (C : D.ιC) (k : Fin (D.cell C).R.N),
            (∫ s in ((D.cell C).R.φs k.castSucc)..((D.cell C).R.φs k.succ),
              coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders (D.cell C) (bθ r : Ω[EE⁄ℂ]) s) =
            coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S
              (fun i : Fin d => (bθ i : Ω[EE⁄ℂ])) Ψθ C ((D.cell C).R.φs k.succ) r -
            coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S
              (fun i : Fin d => (bθ i : Ω[EE⁄ℂ])) Ψθ C ((D.cell C).R.φs k.castSucc) r) ∧
          ∀ (C : D.ιC) (s : ℝ),
            coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S
              (fun i : Fin d => (bθ i : Ω[EE⁄ℂ])) Ψθ C (s + 2 * π) =
            coverMeromorphicBoundaryValue N n radicand baseDivisor hRadicand hOrders D S
              (fun i : Fin d => (bθ i : Ω[EE⁄ℂ])) Ψθ C s +
              (2 * π * Complex.I) • RadialMeromorphicPeriods.ρ D S (fun v r =>
                v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
                  (v.uniformizer * v.differentialCoeff (bθ r : Ω[EE⁄ℂ]))) C

theorem cover_normalized_meromorphic_primitives_of_data :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)) (Ts : Finset D.ιE),
        IsTree (fun e => Cside D e true) (fun e => Cside D e false) Ts →
      ∀ (_ : D.ιC), CoverMeromorphicPrimitives N n radicand baseDivisor hRadicand hOrders D S →
        CoverNormalizedMeromorphicPrimitives N n radicand baseDivisor hRadicand hOrders D S Ts := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD S Ts hTs C₀ hmer
  obtain ⟨d, bθ, V, Ψ, hspan, hS, hP⟩ := hmer
  let θ : Fin d → Ω[EE⁄ℂ] := fun i => bθ i
  have hθ : ∀ i v, v ∉ S → 0 ≤ v.ordDifferential (θ i) := fun i v => ((bθ i).property v).2
  obtain ⟨Ψ', J, hP', hJ, hJ0⟩ := cover_normalize_meromorphic_primitives N n radicand baseDivisor hRadicand hOrders
    D hD S θ hP Ts hTs C₀
  refine ⟨d, bθ, V, Ψ', J, hspan, hS, hP', hJ, hJ0, ?_, ?_⟩
  · exact cover_meromorphic_boundary_ftc N n radicand baseDivisor hRadicand hOrders D hD S θ hθ hS hP'
  · exact cover_meromorphic_boundary_period N n radicand baseDivisor hRadicand hOrders D S θ Ψ'

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
