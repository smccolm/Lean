import Dubon2026.SourceOriginalWeilCoverSimplePoleBasis
import Dubon2026.SourceOriginalWeilCoverMeromorphicCellPrimitives

/-! DUB-17/18 -> cover Abel converse -> meromorphic loop generation.
Construct the actual finite basis and its common residue-subtracted primitives.
The transparent proposition retains the full data while keeping actual-field
elaboration separate from the large existing cycle-existence theorem. -/
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





/-- An actual spanning basis and its common residue-subtracted cell primitives. -/
def CoverMeromorphicPrimitives :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → Finset (Place ℂ EE) → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D S =>
        ∃ (d : ℕ) (bθ : Module.Basis (Fin d) ℂ (coverSimplePoleSpace N n radicand S))
          (Vθ : D.ιC → Set ℂ) (Ψθ : Fin d → D.ιC → ℂ → ℂ),
          (∀ θ : coverSimplePoleSpace N n radicand S, ∃ a : Fin d → ℂ,
            (θ : Ω[EE⁄ℂ]) = ∑ i, a i • (bθ i : Ω[EE⁄ℂ])) ∧
          RadialMeromorphicPeriods.PolePos D S ∧
          RadialMeromorphicPeriods.RegPrimData D S
            (coverRegCoeff N n radicand baseDivisor hRadicand hOrders D S
              (fun i : Fin d => (bθ i : Ω[EE⁄ℂ]))) Vθ Ψθ

theorem exists_cover_meromorphic_primitives :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)),
      (∀ C P, P ∈ (D.cell C).ζ.source →
        AnalyticAt ℂ ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv ((D.cell C).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) →
      ∀ (S : Finset (Place ℂ EE)), RadialMeromorphicPeriods.PolePos D S →
        CoverMeromorphicPrimitives N n radicand baseDivisor hRadicand hOrders D S := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D ha S hS
  obtain ⟨d, bθ, hspan⟩ := exists_cover_simple_pole_basis N n radicand S
  have hθ : ∀ i v, -1 ≤ v.ordDifferential (bθ i : Ω[EE⁄ℂ]) ∧
      (v ∉ S → 0 ≤ v.ordDifferential (bθ i : Ω[EE⁄ℂ])) := fun i => (bθ i).property
  obtain ⟨Vθ, Ψθ, hPθ⟩ := exists_cover_regPrimData N n radicand baseDivisor hRadicand hOrders
    D ha S (fun i : Fin d => (bθ i : Ω[EE⁄ℂ])) hθ hS
  exact ⟨d, bθ, Vθ, Ψθ, hspan, hS, hPθ⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
