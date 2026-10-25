import Dubon2026.SourceOriginalWeilCoverBilinearPeriodPolygonData

/-! DUB-17/18 -> cover Abel converse -> exact bilinear reciprocity.
Consume the same actual primitive family, loop periods and integer rows from
the unimodular polygon. The proved residue theorem supplies both identities. -/
namespace Dubon2026.SourceFunctionField.OriginalWeilCoverChart
noncomputable section
open SourceCurve Set Filter KaehlerDifferential CellGeometry
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

local notation "BI" => coverBoundaryIntegrand N n radicand baseDivisor hRadicand hOrders

open MeasureTheory

open scoped Real

open RadialDissectionPeriods
variable {κ : Type*}

theorem cover_bilinear_period_polygon_of_primitives :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE)) (η : κ → Ω[EE⁄ℂ])
    (V : D.ιC → Set ℂ) (Ψ : κ → D.ιC → ℂ → ℂ) (J : D.ιE → κ → ℂ)
    (_ : CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ) (_ : IsJump D Ψ J)
    (T Ts : Finset D.ιE) (Z : D.ιE → D.ιE → ℤ)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (_ : ∀ e, J e = ∑ l ∈ Tᶜ, Z l e • J l) (_ : ∀ e ∈ Ts, J e = 0)
    (_ : ∀ j (θ : Ω[EE⁄ℂ]), (∀ v ∈ D.skeleton, 0 ≤ v.ordDifferential θ) →
      (∃ g, IsPrimitiveAlong N n radicand baseDivisor hRadicand hOrders θ (γ j) g) ∧
        pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) = ∑ e, (Z j e : ℂ) * coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D θ e)
    (S : Finset (Place ℂ EE))
    (_ : ∀ C : D.ιC, ((D.cell C).carrier ∩ (S : Set (Place ℂ EE))).Subsingleton)
    (_ : ∀ v ∈ S, ∃ C : D.ιC, v ∈ (D.cell C).interior' ∧
      (D.cell C).ζ v = (D.cell C).R.q)
    (_ : UnimodularCyclePeriodPolygonConclusion D (fun e i => coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (η i) e) T Ts J (fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l))),
    CoverBilinearCyclePeriodPolygonConclusion N n radicand baseDivisor hRadicand hOrders D η T Ts J γ S Ψ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ J hP hJ T Ts Z γ hdec hJ0 hγi S hsep hcent hW
  obtain ⟨hm, wd, hw₁, hw₃, hwjump, hrow, hcl, hskew, hu⟩ := hW
  letI := hm
  have hc : ∀ v ∈ S, v ∈ (D.cell (cellOf D v)).interior' := by
    intro v hv
    obtain ⟨C, hC, _⟩ := hcent v hv
    have he := D.eq_of_interior_mem_carrier hC (mem_cellOf D v)
    rw [← he]
    exact hC
  have hri := cover_riemann_cycle_bilinear N n radicand baseDivisor hRadicand hOrders D η V Ψ J hP hJ T Ts Z (wordMatrix wd) γ hdec hJ0 hrow hγi
  have hres := cover_cycle_bilinear_eq_neg_residue N n radicand baseDivisor hRadicand hOrders D η V Ψ J hP hJ T Ts Z (wordMatrix wd) γ
    hdec hJ0 hrow hγi S hsep hcent (cellOf D) hc
  unfold CoverBilinearCyclePeriodPolygonConclusion
  dsimp only
  exact ⟨hm, wd, hw₁, hw₃, hwjump, hrow, hcl, hskew, hu, hri, hres⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
