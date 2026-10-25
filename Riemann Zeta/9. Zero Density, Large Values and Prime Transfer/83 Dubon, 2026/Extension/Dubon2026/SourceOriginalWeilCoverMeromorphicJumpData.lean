import Dubon2026.SourceOriginalWeilCoverNormalizedMeromorphicData
import Dubon2026.SourceOriginalWeilCoverMeromorphicJumpPeriodClosure

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Apply the exact quotient-polygon argument to the actual normalized finite
simple-pole basis. Its actual jumps now belong to complementary cycle
integrals plus literal residue periods; the same primitives are retained. -/
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
def CoverMeromorphicJumpData :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → Finset (Place ℂ EE) → Finset D.ιE → Finset D.ιE → (D.ιE → D.ιE → ℤ) → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D S T Ts Z =>
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
          ∀ e, Jθ e ∈ AddSubgroup.closure
            ((RadialDissectionPeriods.zv Z (fun e r =>
              coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (bθ r : Ω[EE⁄ℂ]) e)) ''
                ((T ∪ Ts)ᶜ : Finset D.ιE)) ⊔
              RadialMeromorphicPeriods.Λres D S (fun v r =>
                v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v)
                  (v.uniformizer * v.differentialCoeff (bθ r : Ω[EE⁄ℂ])))

theorem cover_meromorphic_jump_data_of_normalized :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) →
      Function.Injective D.vert → ∀ (S : Finset (Place ℂ EE)) (T Ts : Finset D.ιE)
        (Z : D.ιE → D.ιE → ℤ),
      FundamentalCycleSystem D T Z → RadialDissectionPolygon.PolygonWordConclusion D Ts →
      CoverNormalizedMeromorphicPrimitives N n radicand baseDivisor hRadicand hOrders D S Ts →
      CoverMeromorphicJumpData N n radicand baseDivisor hRadicand hOrders D S T Ts Z := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D hD hinj S T Ts Z hZ hW hnorm
  obtain ⟨d, bθ, V, Ψ, J, hspan, hS, hP, hJ, hJ0, _, _⟩ := hnorm
  let θ : Fin d → Ω[EE⁄ℂ] := fun i => bθ i
  have hθ : ∀ i v, v ∉ S → 0 ≤ v.ordDifferential (θ i) := fun i v => ((bθ i).property v).2
  have hmem := cover_meromorphic_jump_mem_sup N n radicand baseDivisor hRadicand hOrders
    D hD hinj S θ hθ hS hP hJ T Ts Z hJ0 hZ hW
  exact ⟨d, bθ, V, Ψ, J, hspan, hS, hP, hJ, hJ0, hmem⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
