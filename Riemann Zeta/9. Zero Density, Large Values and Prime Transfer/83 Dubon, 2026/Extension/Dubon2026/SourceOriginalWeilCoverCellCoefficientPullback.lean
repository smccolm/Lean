import Dubon2026.SourceOriginalWeilCoverCellRegularCoefficient

/-! DUB-17/18 -> cover reciprocity -> actual cell coefficient calculus.
The actual cell coefficient pulled back through its coordinate equals the
original normalized differential reading. This consumes the proved local
coefficient equality and inverse derivative; no pullback identity is assumed. -/
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

theorem cover_coeff_comp_mul_deriv :
    letI := placeTopology N n radicand baseDivisor hRadicand hOrders
    ∀ (ζ : OpenPartialHomeomorph (Place ℂ EE) ℂ) {Q : Place ℂ EE}, Q ∈ ζ.source →
      AnalyticAt ℂ (ζ ∘ PF Q) 0 → deriv (ζ ∘ PF Q) 0 ≠ 0 →
      ∀ θ : Ω[EE⁄ℂ], Q.differentialCoeff θ ∈ Q.toValuationSubring →
      ∀ᶠ y in 𝓝 (0 : ℂ), CF ζ θ ((ζ ∘ PF Q) y) * deriv (ζ ∘ PF Q) y = RD Q θ y := by
  letI := placeTopology N n radicand baseDivisor hRadicand hOrders
  intro ζ Q hQ ha hd θ hθ
  let τ : ℂ → ℂ := ζ ∘ PF Q
  let σ : ℂ → ℂ := PC Q ∘ ζ.symm
  have hkey := (cover_coeff_eq_near N n radicand baseDivisor hRadicand hOrders ζ hQ ha hd θ hθ).1
  have hτ0 : τ 0 = ζ Q := congrArg ζ (place_spec N n radicand baseDivisor hRadicand hOrders Q).2.1
  have hτnear : Tendsto τ (𝓝 (0 : ℂ)) (𝓝 (ζ Q)) := by rw [← hτ0]; exact ha.continuousAt
  have htarget : ∀ᶠ y in 𝓝 (0 : ℂ), y ∈ Metric.ball 0 (placeRadius N n radicand baseDivisor hRadicand hOrders Q) :=
    Metric.ball_mem_nhds 0 (place_spec N n radicand baseDivisor hRadicand hOrders Q).1
  have hsrc : ∀ᶠ y in 𝓝 (0 : ℂ), PF Q y ∈ ζ.source := by
    apply (placeFamily_continuousAt_zero N n radicand baseDivisor hRadicand hOrders Q).preimage_mem_nhds
    rw [(place_spec N n radicand baseDivisor hRadicand hOrders Q).2.1]
    exact ζ.open_source.mem_nhds hQ
  have hid : ∀ᶠ y in 𝓝 (0 : ℂ), σ (τ y) = y := by
    filter_upwards [htarget, hsrc] with y hyt hys
    change PC Q (ζ.symm (ζ (PF Q y))) = y
    rw [ζ.left_inv hys]
    exact place_eval_uniformizer N n radicand baseDivisor hRadicand hOrders Q hyt
  let φ : OpenPartialHomeomorph (Place ℂ EE) ℂ :=
    (placeCore N n radicand baseDivisor hRadicand hOrders).openPartialHomeomorph (PC Q) ⟨Q, rfl⟩
  have hφQ : Q ∈ φ.source := mem_placeChart_source N n radicand baseDivisor hRadicand hOrders Q
  have hφ0 : φ Q = 0 := placeChart_self N n radicand baseDivisor hRadicand hOrders Q
  have ha' : AnalyticAt ℂ (ζ ∘ φ.symm) (φ Q) := by rw [hφ0]; exact ha
  have hd' : deriv (ζ ∘ φ.symm) (φ Q) ≠ 0 := by rw [hφ0]; exact hd
  have hστ := (SheetCover.coordinate_local_inverse φ ζ hφQ hQ ha' hd').2.1
  have hσd : ∀ᶠ w in 𝓝 (ζ Q), HasDerivAt σ (deriv τ (σ w))⁻¹ w := hστ.mono fun _ hw => hw.2.2
  have hτd0 : ∀ᶠ y in 𝓝 (0 : ℂ), deriv τ y ≠ 0 := ha.deriv.continuousAt.eventually_ne hd
  filter_upwards [hτnear.eventually hkey, hτnear.eventually hσd, hid, hτd0] with y hy hσy hidy hτy
  rw [hy]
  change RD Q θ (σ (τ y)) * deriv σ (τ y) * deriv τ y = RD Q θ y
  rw [hidy, hσy.deriv, hidy, mul_assoc, inv_mul_cancel₀ hτy, mul_one]

end
end Dubon2026.SourceFunctionField.OriginalWeilCoverChart
