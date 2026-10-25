import Dubon2026.SourceOriginalWeilCoverCellCoefficientPullback
import Dubon2026.SourceOriginalWeilCoverPathLocalPrimitives

/-! DUB-17/18 -> cover reciprocity -> actual cell coefficient calculus.
The centered reading and inverse derivative give the exact coefficient
change between two actual cover coordinates. No differential regularity is
needed for this pointwise identity; regularity enters continuity separately. -/
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

theorem cover_coeff_transition :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ ξ : OpenPartialHomeomorph (Place ℂ EE) ℂ) {Q : Place ℂ EE},
      Q ∈ ζ.source → Q ∈ ξ.source →
      AnalyticAt ℂ (ζ ∘ PF Q) 0 → deriv (ζ ∘ PF Q) 0 ≠ 0 →
      AnalyticAt ℂ (ξ ∘ PF Q) 0 → deriv (ξ ∘ PF Q) 0 ≠ 0 →
      ∀ θ : Ω[EE⁄ℂ], CF ζ θ (ζ Q) = CF ξ θ (ξ Q) * deriv (ξ ∘ ζ.symm) (ζ Q) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ ξ Q hζ hξ ha hd hb he θ
  have hAi := cover_coordinate_inverse N n radicand baseDivisor hRadicand hOrders ζ hζ ha hd
  have hBi := cover_coordinate_inverse N n radicand baseDivisor hRadicand hOrders ξ hξ hb he
  have hnear : ∀ᶠ w in 𝓝 (ζ Q), ζ.symm w ∈ (PC Q).source := by
    apply (ζ.continuousAt_symm (ζ.map_source hζ)).preimage_mem_nhds
    rw [ζ.left_inv hζ]
    exact placeChart_source_mem_nhds N n radicand baseDivisor hRadicand hOrders Q
  have hcomp : (ξ ∘ ζ.symm) =ᶠ[𝓝 (ζ Q)] (ξ ∘ PF Q) ∘ (PC Q ∘ ζ.symm) := by
    filter_upwards [hnear] with w hw
    have hback : PF Q (PC Q (ζ.symm w)) = ζ.symm w := (PC Q).left_inv hw
    change ξ (ζ.symm w) = ξ (PF Q (PC Q (ζ.symm w)))
    rw [hback]
  have hb' : HasDerivAt (ξ ∘ PF Q) (deriv (ξ ∘ PF Q) 0) ((PC Q ∘ ζ.symm) (ζ Q)) := by
    simp only [Function.comp_apply, ζ.left_inv hζ, placeChart_self]
    exact hb.differentiableAt.hasDerivAt
  have hchain : deriv (ξ ∘ ζ.symm) (ζ Q) =
      deriv (ξ ∘ PF Q) 0 * deriv (PC Q ∘ ζ.symm) (ζ Q) := by
    rw [hcomp.deriv_eq]
    exact (hb'.comp (ζ Q) hAi.1.differentiableAt.hasDerivAt).deriv
  change RD (ζ.symm (ζ Q)) θ 0 * deriv (PC (ζ.symm (ζ Q)) ∘ ζ.symm) (ζ Q) =
    (RD (ξ.symm (ξ Q)) θ 0 * deriv (PC (ξ.symm (ξ Q)) ∘ ξ.symm) (ξ Q)) * deriv (ξ ∘ ζ.symm) (ζ Q)
  rw [ζ.left_inv hζ, ξ.left_inv hξ, hchain, hBi.2.deriv]
  field_simp

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
