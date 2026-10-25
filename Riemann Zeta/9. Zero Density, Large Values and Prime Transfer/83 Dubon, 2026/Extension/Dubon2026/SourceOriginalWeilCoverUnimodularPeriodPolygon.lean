import Dubon2026.SourceOriginalWeilCoverComplementaryWordMatrix
import Dubon2026.SourceOriginalWeilCoverPeriodMatrix
import Dubon2026.SourceRadialUnimodularPeriodPolygon

/-! DUB-17/18 -> cover Abel converse -> exact unimodular reciprocity matrix.
The actual regular basis, constructed loops and Euler count discharge the
matrix nondegeneracy inputs. Retain the exact same polygon and integer rows. -/
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



open CellGeometry RadialDissectionPeriods

theorem cover_unimodular_period_polygon_of_basis {kDim : ℕ}
    (b : Module.Basis (Fin kDim) ℂ (regularDifferentials ℂ EE)) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (D : RadialCellDissection (Place ℂ EE))
      (V : D.ιC → Set ℂ) (Ψ : Fin kDim → D.ιC → ℂ → ℂ) (J : D.ιE → Fin kDim → ℂ),
      CoverPrimData N n radicand baseDivisor hRadicand hOrders D (fun i => (b i : Ω[EE⁄ℂ])) V Ψ →
      IsJump D Ψ J → ∀ (T Ts : Finset D.ιE),
      (T ∪ Ts)ᶜ.card = 2 * Module.finrank ℂ (regularDifferentials ℂ EE) →
      AddSubgroup.closure (range J) ≤ AddSubgroup.closure (J '' ((T ∪ Ts)ᶜ : Finset D.ιE)) →
      ∀ (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1)),
      CoverRegularCycleGeneration N n radicand baseDivisor hRadicand hOrders D (fun i => (b i : Ω[EE⁄ℂ])) T Ts γ →
      CyclePeriodPolygonConclusion D
        (fun e i => coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (b i : Ω[EE⁄ℂ]) e) T Ts J
        (fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (γ l)) →
      UnimodularCyclePeriodPolygonConclusion D
        (fun e i => coverEdgeIntegral N n radicand baseDivisor hRadicand hOrders D (b i : Ω[EE⁄ℂ]) e) T Ts J
        (fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (b i : Ω[EE⁄ℂ]) (γ l)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D V Ψ J hP hJ T Ts hc hgen γ hR hW
  obtain ⟨hm, wd, hw₁, hw₃, hwjump, hrow, hcl⟩ := hW
  letI := hm
  have hu := cover_complementaryWordMatrix_isUnit N n radicand baseDivisor hRadicand hOrders
    b D V Ψ J hP hJ T Ts hc hgen γ hR wd hrow
  unfold UnimodularCyclePeriodPolygonConclusion
  intro Cside startV endV L m
  exact ⟨hm, wd, hw₁, hw₃, hwjump, hrow, hcl, complementaryWordMatrix_transpose T Ts wd, hu⟩

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
