import Dubon2026.SourceOriginalWeilCoverThirdKindCycleData
import Dubon2026.SourceOriginalWeilCoverSimplePoleBasis
import Dubon2026.SourceOriginalWeilCoverMeromorphicPrimitiveData

/-! DUB-17/18 -> actual auxiliary point division -> cover Abel converse.
Unpack the actual constructed dissection and retain its exact loops, matrix
and reciprocity. Derive centered pole positions, construct a basis spanning
every allowed simple-pole differential, and construct its residue-subtracted
cell primitives on the same dissection. Meromorphic generation remains open. -/
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

theorem exists_cover_meromorphic_cycle_data {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE))
    (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE)) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∃ D : RadialCellDissection (Place ℂ EE),
      (∀ P ∈ insert P₀ (S : Set (Place ℂ EE)), ∃ i : D.ιC,
        P ∈ (D.cell i).interior' ∧ (D.cell i).ζ P = (D.cell i).R.q) ∧
      (∀ i : D.ιC, ((D.cell i).carrier ∩ (S : Set (Place ℂ EE))).Subsingleton) ∧
      ((Fintype.card D.ιV : ℤ) - (Fintype.card D.ιE : ℤ) + (Fintype.card D.ιC : ℤ) =
        2 - 2 * (Module.finrank ℂ (regularDifferentials ℂ EE) : ℤ)) ∧
      (2 ≤ Fintype.card D.ιV) ∧
      Function.Injective D.vert ∧
      (∀ v : D.ιV, ∃ e : D.ιE, (D.ends e).1 = v ∨ (D.ends e).2 = v) ∧
      (∀ i P, P ∈ (D.cell i).ζ.source →
        AnalyticAt ℂ ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ∧
          deriv ((D.cell i).ζ ∘ placeFamily N n radicand baseDivisor hRadicand hOrders P) 0 ≠ 0) ∧
      ∃ (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ),
        IsTree (hdΓ D) (tlΓ D) T ∧
        IsTree (fun e => Cside D e true) (fun e => Cside D e false) Ts ∧
        Disjoint T Ts ∧
        (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ EE) ∧
        IsWalkConn (hdΓ D) (tlΓ D) T ∧
        PolygonWordConclusion D Ts ∧
        FundamentalCycleSystem D T Z ∧
        CoverCycleLoops N n radicand baseDivisor hRadicand hOrders D Z ∧
        CoverCellPrimitives N n radicand baseDivisor hRadicand hOrders D (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) ∧
        CoverCoordinateCycleLoops N n radicand baseDivisor hRadicand hOrders D Z ∧
        CoverNormalizedCellPrimitives N n radicand baseDivisor hRadicand hOrders D (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) Ts P₀ ∧
        CoverReducedCellJumps N n radicand baseDivisor hRadicand hOrders D (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) T Ts P₀ ∧
        CoverSignedCellPrimitives N n radicand baseDivisor hRadicand hOrders D (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) T Ts P₀ ∧
        CoverPrimitivePolygonData N n radicand baseDivisor hRadicand hOrders D (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) T Ts P₀ ∧
        CoverThirdKindCycleData N n radicand baseDivisor hRadicand hOrders D (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) T Ts Z P₀ S ∧
        CoverMeromorphicPrimitives N n radicand baseDivisor hRadicand hOrders D S := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have h := exists_cover_third_kind_cycle_data N n radicand baseDivisor hRadicand hOrders b P₀ S
  obtain ⟨D, hcent, hsep, hEuler, hV2, hinj, hinc, ha, T, Ts, Z, ht, hts, hd, hc, hw, hword,
    hZ, hloops, hprim, hcoords, hnorm, hred, hsigned, hpol, hthird⟩ := h
  have hS : RadialMeromorphicPeriods.PolePos D S :=
    ⟨hsep, fun v hv => hcent v (Set.mem_insert_of_mem P₀ hv)⟩
  have hmer := exists_cover_meromorphic_primitives N n radicand baseDivisor hRadicand hOrders
    D ha S hS
  exact ⟨D, hcent, hsep, hEuler, hV2, hinj, hinc, ha, T, Ts, Z, ht, hts, hd, hc, hw, hword,
    hZ, hloops, hprim, hcoords, hnorm, hred, hsigned, hpol, hthird, hmer⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
