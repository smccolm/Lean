import Dubon2026.SourceFiniteSkewBilinearSwap
import Dubon2026.SourceOriginalWeilCoverNormalizedAbelReadings
import Dubon2026.SourceOriginalWeilCoverBilinearPeriodPolygon
import Dubon2026.SourceOriginalWeilCoverIntegralPeriodPathIndependence

/-! DUB-17/18 -> auxiliary point division -> cover Abel converse ->
third-kind reciprocity. Reuse the actual path-to-jump theorem and native
integer-span extraction. The chosen Abel paths give one common integer
period correction, and skew symmetry converts the weighted residue identity
to the exact Abel-divisor relation. No path comparison is assumed. -/
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

theorem cover_residue_reciprocity_of_weighted_cells :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀  (D : RadialCellDissection (Place ℂ EE))
    (η : Fin kDim → Ω[EE⁄ℂ]) (V : D.ιC → Set ℂ) (Ψ : Fin kDim → D.ιC → ℂ → ℂ)
    (J : D.ιE → Fin kDim → ℂ) (_ : CoverPrimData N n radicand baseDivisor hRadicand hOrders D η V Ψ) (_ : IsJump D Ψ J)
    (T Ts : Finset D.ιE)
    (γ : (j : D.ιE) → Path (D.vert (D.ends j).1) (D.vert (D.ends j).1))
    (_ : AddSubgroup.closure (range J) ≤ AddSubgroup.closure
      ((fun l i => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) '' ((T ∪ Ts)ᶜ : Finset D.ιE)))
    (P₀ : Place ℂ EE) (_ : gvec D Ψ P₀ (cellOf D P₀) = 0)
    (S : Finset (Place ℂ EE)) (Q : D.ιE → D.ιE → ℤ)
    (_ : ∀ j ∈ (T ∪ Ts)ᶜ, ∀ l ∈ (T ∪ Ts)ᶜ, Q l j = -Q j l)
    (_ : ∀ θ : Ω[EE⁄ℂ], (∀ v ∈ S, -1 ≤ v.ordDifferential θ) →
      (∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential θ) → ∀ i,
      (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
        pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j) * (Q j l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) =
        -(2 * Real.pi * Complex.I * ∑ v ∈ S,
          v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ) *
            gvec D Ψ v (cellOf D v) i))
    (E : Divisor ℂ EE) (θ : Ω[EE⁄ℂ]) (_ : ∀ v : Place ℂ EE, -1 ≤ v.ordDifferential θ)
    (_ : ∀ v : Place ℂ EE,
      v.rationalEval (originalWeilKummerCover_residue_bijective N ℂ n radicand v) (v.uniformizer * v.differentialCoeff θ) = (E v : ℂ))
    (_ : E.support ⊆ S),
    ∃ c : D.ιE → ℤ, ∀ i,
      (∑ j ∈ (T ∪ Ts)ᶜ, ∑ l ∈ (T ∪ Ts)ᶜ,
        (Q j l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ j) * pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ l)) =
        2 * Real.pi * Complex.I * (abelJacobiDiv N n radicand baseDivisor hRadicand hOrders η P₀ E i +
          ∑ l ∈ (T ∪ Ts)ᶜ, (c l : ℂ) * pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ l)) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro D η V Ψ J hP hJ T Ts γ hcl P₀ hzero S Q hskew hweighted E θ hθ hres hE
  have hreg : ∀ v : Place ℂ EE, v ∉ S → 0 ≤ v.ordDifferential θ := by
    intro v hv
    apply v.ord_nonneg_of_mem
    exact cover_coeff_regular_off_divisor N n radicand E θ hθ hres v
      (Finsupp.notMem_support_iff.mp (fun h => hv (hE h)))
  obtain ⟨c, hc⟩ := cover_weighted_readings_eq_abel_add_periods N n radicand baseDivisor hRadicand hOrders D η V Ψ J hP hJ T Ts γ hcl
    P₀ hzero S E hE
  refine ⟨c, fun i => ?_⟩
  rw [← hc i]
  have hw := hweighted θ (fun v _ => hθ v) hreg i
  simp_rw [hres] at hw
  rw [finite_skew_bilinear_swap _ Q
    (fun j => pathIntegral N n radicand baseDivisor hRadicand hOrders (η i) (γ j))
    (fun j => pathIntegral N n radicand baseDivisor hRadicand hOrders θ (γ j)) hskew, hw, neg_neg]

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
