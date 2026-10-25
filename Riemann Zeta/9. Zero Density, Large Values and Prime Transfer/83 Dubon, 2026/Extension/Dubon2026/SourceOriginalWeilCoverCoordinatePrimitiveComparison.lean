import Dubon2026.SourceOriginalWeilCoverCellCoefficientPullback
import Dubon2026.SourceOriginalWeilCoverPathLocalPrimitives

/-! DUB-17/18 -> cover Abel converse -> regular loop generation -> arbitrary
path-to-jump comparison. Reuse the actual cover coefficient pullback and native
uniqueness of analytic primitives. The original path-atlas argument is adapted
from the already proved original-curve modules and their documented FLT source.
All coordinate and regularity inputs are supplied by the actual dissection. -/
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


theorem cover_hasDerivAt_coordPrimitive :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ) {Q : Place ℂ EE}, Q ∈ ζ.source →
      AnalyticAt ℂ (ζ ∘ PF Q) 0 → deriv (ζ ∘ PF Q) 0 ≠ 0 →
      ∀ {W : Set ℂ}, IsOpen W → ζ Q ∈ W →
      ∀ {θ : Ω[EE⁄ℂ]} {Ψ : ℂ → ℂ},
      (∀ w ∈ W, HasDerivAt Ψ (CF ζ θ w) w) → Q.differentialCoeff θ ∈ Q.toValuationSubring →
      ∀ᶠ z in 𝓝 (0 : ℂ), HasDerivAt (Ψ ∘ ζ ∘ PF Q) (RD Q θ z) z := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ Q hQ ha hd W hW hQW θ Ψ hΨ hθ
  let τ : ℂ → ℂ := ζ ∘ PF Q
  have hlaw := cover_coeff_comp_mul_deriv N n radicand baseDivisor hRadicand hOrders ζ hQ ha hd θ hθ
  have hτ0 : τ 0 = ζ Q := congrArg ζ (place_spec N n radicand baseDivisor hRadicand hOrders Q).2.1
  have hτnear : Tendsto τ (𝓝 (0 : ℂ)) (𝓝 (ζ Q)) := by rw [← hτ0]; exact ha.continuousAt
  have hWnear : ∀ᶠ z in 𝓝 (0 : ℂ), τ z ∈ W := hτnear.eventually (hW.mem_nhds hQW)
  filter_upwards [hlaw, hWnear, ha.eventually_analyticAt] with z hz hzW hτz
  have h1 : HasDerivAt (Ψ ∘ τ) (CF ζ θ (τ z) * deriv τ z) z :=
    (hΨ _ hzW).comp z hτz.differentiableAt.hasDerivAt
  rw [hz] at h1
  exact h1

theorem cover_eventually_coordPrimitive_sub_eq
    {Q : Place ℂ EE} {θ : Ω[EE⁄ℂ]} {Φ₁ Φ₂ : ℂ → ℂ}
    (h₁ : ∀ᶠ z in 𝓝 (0 : ℂ), HasDerivAt Φ₁ (RD Q θ z) z)
    (h₂ : ∀ᶠ z in 𝓝 (0 : ℂ), HasDerivAt Φ₂ (RD Q θ z) z) :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ᶠ x in 𝓝 Q, Φ₁ (PC Q x) - Φ₂ (PC Q x) = Φ₁ 0 - Φ₂ 0 := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  have hc := continuousAt_placeChart N n radicand baseDivisor hRadicand hOrders Q Q
    (mem_placeChart_source N n radicand baseDivisor hRadicand hOrders Q)
  change Tendsto (PC Q) (𝓝 Q) (𝓝 (PC Q Q)) at hc
  rw [placeChart_self] at hc
  exact hc.eventually (OriginalPrimitiveGlue.eventually_sub_eq_of_hasDerivAt h₁ h₂)

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
