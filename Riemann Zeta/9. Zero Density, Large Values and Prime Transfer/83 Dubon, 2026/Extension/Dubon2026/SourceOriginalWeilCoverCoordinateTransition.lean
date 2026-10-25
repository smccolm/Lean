import Dubon2026.SourceOriginalWeilCoverCellCoefficientPullback
import Dubon2026.SourceOriginalWeilCoverPathLocalPrimitives

/-! DUB-17/18 -> cover reciprocity -> actual cell coefficient calculus.
Factor the actual transition through the centered cover chart. The proved
inverse analyticity and forward analyticity give the analytic transition
needed to differentiate the two cell primitives along a common edge. -/
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

theorem cover_analyticAt_coordinate_transition :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ ξ : OpenPartialHomeomorph (Place ℂ EE) ℂ) {Q : Place ℂ EE},
      Q ∈ ζ.source → AnalyticAt ℂ (ζ ∘ PF Q) 0 → deriv (ζ ∘ PF Q) 0 ≠ 0 →
      AnalyticAt ℂ (ξ ∘ PF Q) 0 → AnalyticAt ℂ (ξ ∘ ζ.symm) (ζ Q) := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ ξ Q hζ ha hd hb
  have hAi := cover_coordinate_inverse N n radicand baseDivisor hRadicand hOrders ζ hζ ha hd
  have hnear : ∀ᶠ w in 𝓝 (ζ Q), ζ.symm w ∈ (PC Q).source := by
    apply (ζ.continuousAt_symm (ζ.map_source hζ)).preimage_mem_nhds
    rw [ζ.left_inv hζ]
    exact placeChart_source_mem_nhds N n radicand baseDivisor hRadicand hOrders Q
  have hcomp : (ξ ∘ ζ.symm) =ᶠ[𝓝 (ζ Q)] (ξ ∘ PF Q) ∘ (PC Q ∘ ζ.symm) := by
    filter_upwards [hnear] with w hw
    have hback : PF Q (PC Q (ζ.symm w)) = ζ.symm w := (PC Q).left_inv hw
    change ξ (ζ.symm w) = ξ (PF Q (PC Q (ζ.symm w)))
    rw [hback]
  have hzero : (PC Q ∘ ζ.symm) (ζ Q) = 0 := by
    simp only [Function.comp_apply, ζ.left_inv hζ, placeChart_self]
  exact (hb.comp_of_eq hAi.1 hzero).congr hcomp.symm

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
