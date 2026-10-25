import Dubon2026.SourceOriginalWeilCoverCoordinateCyclePrimitives
import Dubon2026.SourceOriginalWeilCoverNormalizedCellPrimitives

/-! DUB-17/18 -> actual cover reciprocity -> actual regular cell primitives.
Apply the existing integer graph spanning-tree and cotree proof to the
constructed marked analytic cover dissection. The same actual dissection retains all geometry, Euler identity and the polygon
word with actual vertex matching and closed integer subwords, together with
the native fundamental cycles and their universal additive decomposition. The same witness now has actual skeleton loops with integral identities for
every differential regular there. Every actual regular differential family now also has normalized primitives
on constructed open star-convex neighborhoods of all cells. The actual loop integrals now equal their coordinate edge sums for every
differential regular on the skeleton. Constant edge jumps are now constructed and normalized to vanish on the
dual tree, with the root primitive value zero. Period generation and
reciprocity remain separate obligations. -/
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

/-- Actual cell primitives, constant edge jumps, zero dual-tree jumps and root normalization.
The existence theorem below constructs all data on the same actual dissection. -/
def CoverNormalizedCellPrimitives {ι : Type*} :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    (D : RadialCellDissection (Place ℂ EE)) → (ι → Ω[EE⁄ℂ]) → Finset D.ιE → Place ℂ EE → Prop := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  exact fun D η Ts P₀ =>
    ∃ (C₀ : D.ιC) (V : D.ιC → Set ℂ) (Ψ : ι → D.ιC → ℂ → ℂ) (J : D.ιE → ι → ℂ),
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
      (∀ e ∈ Ts, J e = 0) ∧ ∀ i, Ψ i C₀ ((D.cell C₀).ζ P₀) = 0

theorem exists_cover_normalized_cycle_primitives {ι : Type*} (η : ι → Ω[EE⁄ℂ])
    (hη : ∀ i, η i ∈ regularDifferentials ℂ EE) (P₀ : Place ℂ EE) (S : Finset (Place ℂ EE)) :
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
        CoverCellPrimitives N n radicand baseDivisor hRadicand hOrders D η ∧
        CoverCoordinateCycleLoops N n radicand baseDivisor hRadicand hOrders D Z ∧
        CoverNormalizedCellPrimitives N n radicand baseDivisor hRadicand hOrders D η Ts P₀ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have h := exists_cover_coordinate_cycle_primitives N n radicand baseDivisor hRadicand hOrders η hη P₀ S
  obtain ⟨D, hcent, hsep, hEuler, hV2, hinj, hinc, ha, T, Ts, Z, ht, hts, hd, hc, hw, hword, hZ, hloops, hprim, hcoords⟩ := h
  refine ⟨D, hcent, hsep, hEuler, hV2, hinj, hinc, ha, T, Ts, Z, ht, hts, hd, hc, hw, hword, hZ, hloops, hprim, hcoords, ?_⟩
  obtain ⟨C₀, hP₀, _⟩ := hcent P₀ (Set.mem_insert _ _)
  obtain ⟨V, Ψ, J, hV, hΨ, hJ, hJ0, hΨ0⟩ :=
    cover_exists_normalized_primitives_and_jumps N n radicand baseDivisor hRadicand hOrders
      D ha η hη Ts hts C₀ ((D.cell C₀).ζ P₀)
  exact ⟨C₀, V, Ψ, J, hP₀, hV, hΨ, hJ, hJ0, hΨ0⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
