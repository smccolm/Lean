import Dubon2026.SourceOriginalWeilCoverNormalizedMeromorphicCycleData
import Dubon2026.SourceOriginalWeilCoverMeromorphicJumpData

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel converse.
The same actual 2g cycle/dissection witnesses now carry normalized meromorphic
primitives whose jumps reduce to complementary cycle and residue periods.
The actual regular-loop generation, unimodular matrix and both reciprocity
identities remain on those witnesses. A pole-avoiding path atlas is still
required to obtain meromorphic loop generation. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Topology CellGeometry KaehlerDifferential
attribute [local instance] OriginalChart.placeTopology restrictionIntegral
variable (N : ℕ) [NeZero N] (n : ℕ) [NeZero n]
variable (radicand : modularFunctionFieldOver N ℂ)
local notation "FF" => modularFunctionFieldOver N ℂ
local notation "EE" => Polynomial.SplittingField (Polynomial.X ^ n - Polynomial.C radicand : Polynomial FF)
variable (baseDivisor : Divisor ℂ (modularFunctionFieldOver N ℂ)) (hRadicand : radicand ≠ 0)
variable (hOrders : ∀ v : Place ℂ (modularFunctionFieldOver N ℂ), v.ord radicand = (n : ℤ) * baseDivisor v)
include baseDivisor hRadicand hOrders




open IntegerEdgeChains RadialDissectionTrees RadialDissectionPolygon

theorem exists_cover_meromorphic_jump_cycle_data {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE))
    (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE)) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∃ D : RadialCellDissection (Place ℂ EE),
      Function.Injective D.vert ∧
      (∀ i P, P ∈ (D.cell i).ζ.source →
        AnalyticAt ℂ ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) ∧
      ∃ (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ),
        (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ EE) ∧
        PolygonWordConclusion D Ts ∧
        FundamentalCycleSystem D T Z ∧
        CoverThirdKindCycleData N n radicand baseDivisor hRadicand hOrders D
          (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) T Ts Z P₀ S ∧
        CoverMeromorphicJumpData N n radicand baseDivisor hRadicand hOrders D S T Ts Z := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have h := exists_cover_normalized_meromorphic_cycle_data N n radicand baseDivisor hRadicand hOrders b P₀ S
  obtain ⟨D, hinj, ha, T, Ts, Z, hc, hword, hZ, hthird, hnorm⟩ := h
  have hmem := cover_meromorphic_jump_data_of_normalized N n radicand baseDivisor hRadicand hOrders
    D ha hinj S T Ts Z hZ hword hnorm
  exact ⟨D, hinj, ha, T, Ts, Z, hc, hword, hZ, hthird, hmem⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
