import Dubon2026.SourceOriginalWeilCoverThirdKindCycleData
import Dubon2026.SourceOriginalWeilCoverSimplePoleBasis
import Dubon2026.SourceOriginalWeilCoverMeromorphicCycleData
import Dubon2026.SourceOriginalWeilCoverNormalizedMeromorphicData

/-! DUB-17/18 -> actual auxiliary point division -> cover Abel converse.
Unpack the actual constructed dissection and retain its exact loops, matrix
and reciprocity. Derive centered pole positions, construct a basis spanning
every allowed simple-pole differential, and construct its residue-subtracted
cell primitives on the same dissection. The conclusion retains precisely the source data needed for meromorphic
generation and final 2g reindexing: injective vertices, actual forward charts,
the 2g count, polygon word, integer cycles, the same actual regular loops and
all their matrix/reciprocity identities, and normalized meromorphic primitives.
Earlier construction metadata remains proved upstream. Meromorphic generation
remains open. -/
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

theorem exists_cover_normalized_meromorphic_cycle_data {kDim : ℕ}
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
        CoverNormalizedMeromorphicPrimitives N n radicand baseDivisor hRadicand hOrders D S Ts := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have h := exists_cover_meromorphic_cycle_data N n radicand baseDivisor hRadicand hOrders b P₀ S
  obtain ⟨D, _, _, _, _, hinj, _, ha, T, Ts, Z, _, hts, _, hc, _, hword,
    hZ, _, _, _, _, _, _, _, hthird, hmer⟩ := h
  have hnormmer := cover_normalized_meromorphic_primitives_of_data N n radicand baseDivisor hRadicand hOrders
    D ha S Ts hts (RadialDissectionPeriods.cellOf D P₀) hmer
  exact ⟨D, hinj, ha, T, Ts, Z, hc, hword, hZ, hthird, hnormmer⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
