import Dubon2026.SourceOriginalWeilCoverRegularLoopGeneration
import Dubon2026.SourceOriginalWeilCoverPeriodAnnihilator
import Dubon2026.SourceOriginalWeilCoverComplementaryPeriodCoordinates
import Dubon2026.SourcePeriodGeneratorsRealSpan

/-! DUB-17/18 -> cover Abel converse -> integer matrix unimodularity.
The existing actual-cover maximum principle kills every annihilator of the
constructed complementary periods. Use the proved regular-loop generation
and existing integer period coordinates directly. No separate real basis,
period freeness or lattice discreteness is constructed. -/
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

theorem cover_complementary_periods_span_real {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE)) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (T Ts : Finset D.ιE)
      (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)),
      CoverRegularCycleGeneration N n radicand baseDivisor hRadicand hOrders D
        (fun i => (b i : Ω[EE⁄ℂ])) T Ts γ →
      ⊤ ≤ Submodule.span ℝ (range (fun l : {l // l ∈ (T ∪ Ts)ᶜ} =>
        fun i => pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (γ l.1))) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D T Ts γ hR
  apply PeriodRealDual.span_top_of_integer_coordinates
    (pathPeriodLattice N n radicand baseDivisor hRadicand hOrders (fun i => (b i : Ω[EE⁄ℂ])))
  · exact cover_complementary_period_coordinates N n radicand baseDivisor hRadicand hOrders
      (fun i => (b i : Ω[EE⁄ℂ])) D T Ts γ hR
  · intro ℓ hℓ
    exact eq_zero_of_annihilates_periods N n radicand baseDivisor hRadicand hOrders
      (fun i => (b i : Ω[EE⁄ℂ])) (fun i => (b i).2)
      (b.linearIndependent.map' (regularDifferentials ℂ EE).subtype (Submodule.ker_subtype _)) ℓ hℓ

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
