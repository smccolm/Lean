import Mathlib.Topology.OpenPartialHomeomorph.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Complex.CauchyIntegral

/-! DUB-17/18 -> cover reciprocity -> local calculus in actual lifted cells.
The inverse coordinate is derived from the constructed cover charts and the
source coordinate's nonzero derivative. No inverse analyticity premise remains.
Adapted from S_AlgebraicCurve_coeffIn_local_calculus, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Native complex analyticity
from eventual differentiability avoids a separate ball construction.
-/
namespace Dubon2026.SourceFunctionField.SheetCover
noncomputable section
open Set Filter
open scoped Topology
variable {X : Type*} [TopologicalSpace X]

theorem coordinate_local_inverse (φ ζ : OpenPartialHomeomorph X ℂ) {Q : X}
    (hφQ : Q ∈ φ.source) (hQ : Q ∈ ζ.source)
    (hAnalytic : AnalyticAt ℂ (ζ ∘ φ.symm) (φ Q))
    (hDeriv : deriv (ζ ∘ φ.symm) (φ Q) ≠ 0) :
    (∀ᶠ w in 𝓝 (ζ Q), w ∈ ζ.target ∧ ζ.symm w ∈ φ.source) ∧
    (∀ᶠ w in 𝓝 (ζ Q),
      AnalyticAt ℂ (ζ ∘ φ.symm) (φ (ζ.symm w)) ∧
      deriv (ζ ∘ φ.symm) (φ (ζ.symm w)) ≠ 0 ∧
      HasDerivAt (φ ∘ ζ.symm)
        (deriv (ζ ∘ φ.symm) (φ (ζ.symm w)))⁻¹ w) ∧
    ContinuousAt (φ ∘ ζ.symm) (ζ Q) ∧
    (φ ∘ ζ.symm) (ζ Q) = φ Q := by
  set τ : ℂ → ℂ := ζ ∘ φ.symm with hτ
  set σ : ℂ → ℂ := φ ∘ ζ.symm with hσ
  set c : ℂ := φ Q with hc
  set w₀ : ℂ := ζ Q with hw₀
  have hw₀t : w₀ ∈ ζ.target := ζ.map_source hQ
  have hσw₀ : ζ.symm w₀ = Q := ζ.left_inv hQ
  have hσc : σ w₀ = c := by
    show φ (ζ.symm w₀) = c
    rw [hσw₀]

  have h1 : ∀ᶠ w in 𝓝 w₀, w ∈ ζ.target := ζ.open_target.mem_nhds hw₀t
  have hzc : ContinuousAt ζ.symm w₀ := ζ.continuousAt_symm hw₀t
  have h2 : ∀ᶠ w in 𝓝 w₀, ζ.symm w ∈ φ.source := by
    refine hzc.preimage_mem_nhds ?_
    rw [hσw₀]
    exact φ.open_source.mem_nhds hφQ
  have h12 : ∀ᶠ w in 𝓝 w₀, w ∈ ζ.target ∧ ζ.symm w ∈ φ.source := h1.and h2

  have hid : ∀ᶠ w in 𝓝 w₀, τ (σ w) = w := by
    filter_upwards [h12] with w hw
    simp only [hτ, hσ, Function.comp_apply]
    rw [φ.left_inv hw.2, ζ.right_inv hw.1]
  have hσcont : ∀ᶠ w in 𝓝 w₀, ContinuousAt σ w := by
    filter_upwards [h1.eventually_nhds, h2] with w hw1 hw2
    exact (φ.continuousAt hw2).comp (ζ.continuousAt_symm hw1.self_of_nhds)
  have hσcont₀ : ContinuousAt σ w₀ := hσcont.self_of_nhds

  have hτa : ∀ᶠ y in 𝓝 c, AnalyticAt ℂ τ y := hAnalytic.eventually_analyticAt
  have hτd : ∀ᶠ y in 𝓝 c, deriv τ y ≠ 0 := hAnalytic.deriv.continuousAt.eventually_ne hDeriv
  have hσnear : Tendsto σ (𝓝 w₀) (𝓝 c) := by rw [← hσc]; exact hσcont₀
  have hτa' : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ τ (σ w) := hσnear.eventually hτa
  have hτd' : ∀ᶠ w in 𝓝 w₀, deriv τ (σ w) ≠ 0 := hσnear.eventually hτd

  have hσderiv : ∀ᶠ w in 𝓝 w₀, HasDerivAt σ (deriv τ (σ w))⁻¹ w := by
    filter_upwards [hτa', hτd', hσcont, hid.eventually_nhds] with w ha hd hcw hidw
    exact HasDerivAt.of_local_left_inverse hcw ha.differentiableAt.hasDerivAt hd hidw
  refine ⟨h12, ?_, hσcont₀, hσc⟩
  filter_upwards [hτa', hτd', hσderiv] with w ha hd hder
  exact ⟨ha, hd, hder⟩


theorem analyticAt_coordinate_inverse (φ ζ : OpenPartialHomeomorph X ℂ) {Q : X}
    (hφQ : Q ∈ φ.source) (hQ : Q ∈ ζ.source)
    (hAnalytic : AnalyticAt ℂ (ζ ∘ φ.symm) (φ Q))
    (hDeriv : deriv (ζ ∘ φ.symm) (φ Q) ≠ 0) :
    AnalyticAt ℂ (φ ∘ ζ.symm) (ζ Q) := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact (coordinate_local_inverse φ ζ hφQ hQ hAnalytic hDeriv).2.1.mono fun _ h => h.2.2.differentiableAt

end
end Dubon2026.SourceFunctionField.SheetCover
