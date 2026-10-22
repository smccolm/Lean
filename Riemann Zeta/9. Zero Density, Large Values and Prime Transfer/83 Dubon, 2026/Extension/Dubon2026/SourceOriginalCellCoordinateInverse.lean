import Dubon2026.SourceOriginalAnalyticCellCoordinates
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Complex.CauchyIntegral

/-! DUB-17/18 -> raw reciprocity -> local calculus in genuine analytic cells.
The inverse coordinate is derived from the constructed original charts and the
source coordinate's nonzero derivative. No inverse analyticity premise remains.
Adapted from S_AlgebraicCurve_coeffIn_local_calculus, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Native complex analyticity
from eventual differentiability avoids a separate ball construction.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter
open scoped Manifold Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem AnalyticCoord.local_inverse (A : AnalyticCoord N)
    {Q : Place ℂ (modularFunctionFieldOver N ℂ)} (hQ : Q ∈ A.ζ.source) :
    (∀ᶠ w in 𝓝 (A.ζ Q), w ∈ A.ζ.target ∧ A.ζ.symm w ∈ (extChartAt 𝓘(ℂ, ℂ) Q).source) ∧
    (∀ᶠ w in 𝓝 (A.ζ Q),
      AnalyticAt ℂ (A.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q (A.ζ.symm w)) ∧
      deriv (A.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q (A.ζ.symm w)) ≠ 0 ∧
      HasDerivAt (extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm)
        (deriv (A.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) (extChartAt 𝓘(ℂ, ℂ) Q (A.ζ.symm w)))⁻¹ w) ∧
    ContinuousAt (extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) (A.ζ Q) ∧
    (extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) (A.ζ Q) = extChartAt 𝓘(ℂ, ℂ) Q Q := by
  set φ := extChartAt 𝓘(ℂ, ℂ) Q with hφ
  set τ : ℂ → ℂ := A.ζ ∘ φ.symm with hτ
  set σ : ℂ → ℂ := φ ∘ A.ζ.symm with hσ
  set c : ℂ := φ Q with hc
  set w₀ : ℂ := A.ζ Q with hw₀
  have hw₀t : w₀ ∈ A.ζ.target := A.ζ.map_source hQ
  have hσw₀ : A.ζ.symm w₀ = Q := A.ζ.left_inv hQ
  have hσc : σ w₀ = c := by
    show φ (A.ζ.symm w₀) = c
    rw [hσw₀]

  have h1 : ∀ᶠ w in 𝓝 w₀, w ∈ A.ζ.target := A.ζ.open_target.mem_nhds hw₀t
  have hzc : ContinuousAt A.ζ.symm w₀ := A.ζ.continuousAt_symm hw₀t
  have h2 : ∀ᶠ w in 𝓝 w₀, A.ζ.symm w ∈ φ.source := by
    refine hzc.preimage_mem_nhds ?_
    rw [hσw₀]
    exact (isOpen_extChartAt_source (I := 𝓘(ℂ, ℂ)) Q).mem_nhds (mem_extChartAt_source Q)
  have h12 : ∀ᶠ w in 𝓝 w₀, w ∈ A.ζ.target ∧ A.ζ.symm w ∈ φ.source := h1.and h2

  have hid : ∀ᶠ w in 𝓝 w₀, τ (σ w) = w := by
    filter_upwards [h12] with w hw
    simp only [hτ, hσ, Function.comp_apply]
    rw [φ.left_inv hw.2, A.ζ.right_inv hw.1]
  have hσcont : ∀ᶠ w in 𝓝 w₀, ContinuousAt σ w := by
    filter_upwards [h1.eventually_nhds, h2] with w hw1 hw2
    exact (continuousAt_extChartAt' (I := 𝓘(ℂ, ℂ)) hw2).comp (A.ζ.continuousAt_symm hw1.self_of_nhds)
  have hσcont₀ : ContinuousAt σ w₀ := hσcont.self_of_nhds

  have hτa : ∀ᶠ y in 𝓝 c, AnalyticAt ℂ τ y := (A.analytic Q hQ).eventually_analyticAt
  have hτd : ∀ᶠ y in 𝓝 c, deriv τ y ≠ 0 := (A.analytic Q hQ).deriv.continuousAt.eventually_ne (A.deriv_ne Q hQ)
  have hσnear : Tendsto σ (𝓝 w₀) (𝓝 c) := by rw [← hσc]; exact hσcont₀
  have hτa' : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ τ (σ w) := hσnear.eventually hτa
  have hτd' : ∀ᶠ w in 𝓝 w₀, deriv τ (σ w) ≠ 0 := hσnear.eventually hτd

  have hσderiv : ∀ᶠ w in 𝓝 w₀, HasDerivAt σ (deriv τ (σ w))⁻¹ w := by
    filter_upwards [hτa', hτd', hσcont, hid.eventually_nhds] with w ha hd hcw hidw
    exact HasDerivAt.of_local_left_inverse hcw ha.differentiableAt.hasDerivAt hd hidw
  refine ⟨h12, ?_, hσcont₀, hσc⟩
  filter_upwards [hτa', hτd', hσderiv] with w ha hd hder
  exact ⟨ha, hd, hder⟩


theorem AnalyticCoord.analyticAt_inverse (A : AnalyticCoord N)
    {Q : Place ℂ (modularFunctionFieldOver N ℂ)} (hQ : Q ∈ A.ζ.source) :
    AnalyticAt ℂ (extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm) (A.ζ Q) := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  exact (A.local_inverse hQ).2.1.mono fun _ h => h.2.2.differentiableAt

end
end Dubon2026.SourceFunctionField.CellGeometry
