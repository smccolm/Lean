import Dubon2026.SourceOriginalWeilCoverBilinearCycleData
import Dubon2026.SourceOriginalWeilCoverThirdKindPolygon

/-! DUB-17/18 -> auxiliary point division -> actual cover Abel converse.
The constructed actual dissection, primitives and cycle loops now carry a
skew-symmetric unimodular matrix, regular bilinear identity and exact
Abel-divisor residue reciprocity with one common integer period correction.
All earlier geometry and regular-loop generation remain on the same witnesses.
Meromorphic loop generation and fixed 2g indexing remain open. -/
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

/-- Actual normalized primitives and cycles with both bilinear identities on the same unimodular matrix.
The existence theorem below constructs all data on the same actual dissection. -/
def CoverThirdKindCycleData {kDim : ℕ} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → (Fin kDim → Ω[EE⁄ℂ]) → Finset D.ιE → Finset D.ιE → (D.ιE → D.ιE → ℤ) → Place ℂ EE → Finset (Place ℂ EE) → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D η T Ts Z P₀ S =>
    ∃ (C₀ : D.ιC) (V : D.ιC → Set ℂ) (Ψ : Fin kDim → D.ιC → ℂ → ℂ) (J : D.ιE → Fin kDim → ℂ),
      P₀ ∈ (D.cell C₀).interior' ∧
      (∀ C, IsOpen (V C) ∧ (D.cell C).R.q ∈ V C ∧
        StarConvex ℝ (D.cell C).R.q (V C) ∧ (D.cell C).R.K ⊆ V C ∧ V C ⊆ (D.cell C).ζ.target) ∧
      (∀ i C, ∀ w ∈ V C, HasDerivAt (Ψ i C)
        (coverCoeffIn N n radicand baseDivisor hRadicand hOrders (D.cell C).ζ (η i) w) w) ∧
      (∀ e i,
        let p := D.arcOf (e, true)
        let q := D.arcOf (e, false)
        ∀ s ∈ (D.cell p.1).R.arcIcc p.2,
          Ψ i p.1 ((D.cell p.1).R.loop s) -
            Ψ i q.1 ((D.cell q.1).ζ ((D.cell p.1).bdry s)) = J e i) ∧
      (∀ e ∈ Ts, J e = 0) ∧ (∀ i, Ψ i C₀ ((D.cell C₀).ζ P₀) = 0) ∧
      (∀ w, (∑ e with (D.ends e).2 = w, J e) = ∑ e with (D.ends e).1 = w, J e) ∧
      (AddSubgroup.closure (Set.range J) ≤ AddSubgroup.closure (J '' ((T ∪ Ts)ᶜ : Finset D.ιE))) ∧
      (∀ q : D.ιE × Bool, ∀ i,
        Ψ i (D.arcOf q).1 ((D.cell (D.arcOf q).1).R.loop ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.succ)) -
          Ψ i (D.arcOf q).1 ((D.cell (D.arcOf q).1).R.loop ((D.cell (D.arcOf q).1).R.φs (D.arcOf q).2.castSucc)) =
        (if q.2 then (1 : ℂ) else -1) * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (η i) q.1) ∧
      (RadialDissectionPeriods.PrimitivePolygonConclusion D
        (fun e i => coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (η i) e) Ts J) ∧
      ∃ γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1),
        (∀ j t, γ j t ∈ D.skeleton) ∧
        (∀ j (θ : Ω[EE⁄ℂ]), (∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential θ) →
          (∃ g, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders θ (γ j) g) ∧
          pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) =
            ∑ e, (Z j e : ℂ) * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e) ∧
        CoverThirdKindCyclePeriodPolygonConclusion N n radicand baseDivisor hRadicand hOrders D η T Ts J γ P₀ S Ψ ∧
        CoverRegularCycleGeneration N n radicand baseDivisor hRadicand hOrders D η T Ts γ

theorem exists_cover_third_kind_cycle_data {kDim : ℕ}
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
        CoverThirdKindCycleData N n radicand baseDivisor hRadicand hOrders D (fun i : Fin kDim => (b i : Ω[EE⁄ℂ])) T Ts Z P₀ S := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  let η : Fin kDim → Ω[EE⁄ℂ] := fun i => b i
  have hη : ∀ i, η i ∈ regularDifferentials ℂ EE := fun i => (b i).2
  have h := exists_cover_bilinear_cycle_data N n radicand baseDivisor hRadicand hOrders b P₀ S
  obtain ⟨D, hcent, hsep, hEuler, hV2, hinj, hinc, ha, T, Ts, Z, ht, hts, hd, hc, hw, hword, hZ, hloops, hprim, hcoords, hnorm, hred, hsigned, hpol, hbilin⟩ := h
  refine ⟨D, hcent, hsep, hEuler, hV2, hinj, hinc, ha, T, Ts, Z, ht, hts, hd, hc, hw, hword, hZ, hloops, hprim, hcoords, hnorm, hred, hsigned, hpol, ?_⟩
  obtain ⟨C₀, V, Ψ, J, hP₀, hV, hΨ, hJ, hJ0, hΨ0, hcir, hclosure, hvalues, hW, γ, hγs, hγi, hmatrix, hR⟩ := hbilin
  refine ⟨C₀, V, Ψ, J, hP₀, hV, hΨ, hJ, hJ0, hΨ0, hcir, hclosure, hvalues, hW, γ, hγs, hγi, ?_, hR⟩
  have hP : CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ :=
    ⟨ha, fun C => (hV C).1, fun C => (hV C).2.2.2.1, hΨ, hη⟩
  have hC₀ : C₀ = RadialDissectionPeriods.cellOf D P₀ :=
    D.eq_of_interior_mem_carrier hP₀ (RadialDissectionPeriods.mem_cellOf D P₀)
  have hbase : RadialDissectionPeriods.gvec D Ψ P₀ (RadialDissectionPeriods.cellOf D P₀) = 0 := by
    funext i
    change Ψ i (RadialDissectionPeriods.cellOf D P₀)
      ((D.cell (RadialDissectionPeriods.cellOf D P₀)).ζ P₀) = 0
    rw [← hC₀]
    exact hΨ0 i
  exact cover_third_kind_reciprocity_of_polygon N n radicand baseDivisor hRadicand hOrders
    D η V Ψ J hP (fun i e => hJ e i) T Ts γ P₀ hbase S hmatrix

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
