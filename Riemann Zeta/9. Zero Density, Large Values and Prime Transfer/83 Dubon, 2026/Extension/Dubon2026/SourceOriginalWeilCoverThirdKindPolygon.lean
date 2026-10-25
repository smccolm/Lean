import Dubon2026.SourceOriginalWeilCoverThirdKindPolygonData

/-! DUB-17/18 -> cover Abel converse -> third-kind reciprocity on the exact
constructed word matrix. Consume the proved Abel-path comparison directly;
all prior matrix, loop and bilinear witnesses are retained. -/
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
variable {kDim : ℕ}

theorem cover_third_kind_reciprocity_of_polygon :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀  (D : RadialCellDissection (Place ℂ EE))
    (η : Fin kDim → Ω[EE⁄ℂ]) (V : D.ιC → Set ℂ) (Ψ : Fin kDim → D.ιC → ℂ → ℂ)
    (J : D.ιE → Fin kDim → ℂ) (_ : CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ) (_ : IsJump D Ψ J)
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (P₀ : Place ℂ EE) (_ : gvec D Ψ P₀ (cellOf D P₀) = 0)
    (S : Finset (Place ℂ EE)) (_ : CoverBilinearCyclePeriodPolygonConclusion N n radicand baseDivisor hRadicand hOrders D η T Ts J γ S Ψ),
    CoverThirdKindCyclePeriodPolygonConclusion N n radicand baseDivisor hRadicand hOrders D η T Ts J γ P₀ S Ψ := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ J hP hJ T Ts γ P₀ hzero S hW
  obtain ⟨hm, wd, hw₁, hw₃, hwjump, hrow, hcl, hskew, hu, hri, hweighted⟩ := hW
  letI := hm
  have hsk : ∀ j ∈ (T ∪ Ts)ᶜ, ∀ l ∈ (T ∪ Ts)ᶜ, wordMatrix wd l j = -wordMatrix wd j l := by
    intro j hj l hl
    exact congrFun (congrFun hskew ⟨j, hj⟩) ⟨l, hl⟩
  refine ⟨hm, wd, hw₁, hw₃, hwjump, hrow, hcl, hskew, hu, hri, hweighted, ?_⟩
  exact cover_residue_reciprocity_of_weighted_cells N n radicand baseDivisor hRadicand hOrders
    D η V Ψ J hP hJ T Ts γ hcl P₀ hzero S (wordMatrix wd) hsk hweighted

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
