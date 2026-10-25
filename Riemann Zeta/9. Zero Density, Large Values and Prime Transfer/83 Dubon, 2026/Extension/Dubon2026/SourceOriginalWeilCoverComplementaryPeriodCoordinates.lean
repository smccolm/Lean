import Dubon2026.SourceOriginalWeilCoverRegularLoopGeneration
import Dubon2026.SourceOriginalWeilCoverAbelJacobiPeriods
import Dubon2026.SourcePeriodGeneratorsRealSpan

/-! DUB-17/18 -> cover Abel converse -> unimodular integer word matrix.
Convert the proved common complementary-cycle coefficients into coordinates
for the integer period span, using the existing actual-cover span induction. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
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



open CellGeometry

theorem cover_complementary_period_coordinates {kDim : ℕ}
    (b : Fin kDim → Ω[EE⁄ℂ]) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (T Ts : Finset D.ιE)
      (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)),
      CoverRegularCycleGeneration N n radicand baseDivisor hRadicand hOrders D b T Ts γ →
      ∀ u ∈ pathPeriodLattice N n radicand baseDivisor hRadicand hOrders b,
      ∃ a : {l // l ∈ (T ∪ Ts)ᶜ} → ℤ,
        u = ∑ l, a l • (fun i => pathIntegral N n radicand baseDivisor hRadicand hOrders (b i) (γ l.1)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D T Ts γ hR
  apply PeriodRealDual.integer_coordinates_of_finset_generators (T ∪ Ts)ᶜ
    (fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (b i) (γ l))
  rintro u ⟨P, δ, rfl⟩
  exact hR P δ

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
