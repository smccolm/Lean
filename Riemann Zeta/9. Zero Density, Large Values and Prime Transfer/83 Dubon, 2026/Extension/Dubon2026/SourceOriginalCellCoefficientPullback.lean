import Dubon2026.SourceOriginalCellRegularCoefficient

/-! DUB-17/18 -> raw reciprocity -> primitives and coordinate-independent
cell integrals. Pulling the actual coefficient back through the cell coordinate
recovers the original normalized differential reading.
Adapted from S_AlgebraicCurve_coeffIn_local_calculus, anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry
noncomputable section
open SourceCurve Set Filter KaehlerDifferential
open scoped Manifold Topology
attribute [local instance] OriginalChart.placeTopology OriginalChart.placeChartedSpace
variable {N : ℕ} [NeZero N]

theorem AnalyticCoord.coeff_comp_mul_deriv (A : AnalyticCoord N)
    {Q : Place ℂ (modularFunctionFieldOver N ℂ)} (hQ : Q ∈ A.ζ.source)
    {θ : Ω[modularFunctionFieldOver N ℂ⁄ℂ]}
    (hθ : Q.differentialCoeff θ ∈ Q.toValuationSubring) :
    ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q),
      coeffIn A.ζ θ ((A.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y) *
          deriv (A.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm) y =
        OriginalChart.readDifferential N Q θ y := by
  set τ : ℂ → ℂ := A.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) Q).symm with hτ
  set σ : ℂ → ℂ := extChartAt 𝓘(ℂ, ℂ) Q ∘ A.ζ.symm with hσ
  obtain ⟨hkey, -⟩ := A.coeff_eq_near hQ hθ
  have hτc : τ (extChartAt 𝓘(ℂ, ℂ) Q Q) = A.ζ Q := by
    show A.ζ ((extChartAt 𝓘(ℂ, ℂ) Q).symm (extChartAt 𝓘(ℂ, ℂ) Q Q)) = A.ζ Q
    rw [(extChartAt 𝓘(ℂ, ℂ) Q).left_inv (mem_extChartAt_source Q)]
  have hτcont : ContinuousAt τ (extChartAt 𝓘(ℂ, ℂ) Q Q) := (A.analytic Q hQ).continuousAt
  have hτnear : Tendsto τ (𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q)) (𝓝 (A.ζ Q)) := by
    rw [← hτc]; exact hτcont

  have htarget : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q), y ∈ (extChartAt 𝓘(ℂ, ℂ) Q).target :=
    extChartAt_target_mem_nhds (I := 𝓘(ℂ, ℂ)) Q
  have hsrc : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q), (extChartAt 𝓘(ℂ, ℂ) Q).symm y ∈ A.ζ.source := by
    refine (continuousAt_extChartAt_symm (I := 𝓘(ℂ, ℂ)) Q).preimage_mem_nhds ?_
    rw [extChartAt_to_inv (I := 𝓘(ℂ, ℂ)) Q]
    exact A.ζ.open_source.mem_nhds hQ
  have hid : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q), σ (τ y) = y := by
    filter_upwards [htarget, hsrc] with y hyt hys
    show extChartAt 𝓘(ℂ, ℂ) Q (A.ζ.symm (A.ζ ((extChartAt 𝓘(ℂ, ℂ) Q).symm y))) = y
    rw [A.ζ.left_inv hys, (extChartAt 𝓘(ℂ, ℂ) Q).right_inv hyt]
  obtain ⟨-, hστ, -, -⟩ := A.local_inverse hQ
  have hσd : ∀ᶠ w in 𝓝 (A.ζ Q), HasDerivAt σ (deriv τ (σ w))⁻¹ w := hστ.mono fun w hw => hw.2.2
  have hτd0 : ∀ᶠ y in 𝓝 (extChartAt 𝓘(ℂ, ℂ) Q Q), deriv τ y ≠ 0 :=
    (A.analytic Q hQ).deriv.continuousAt.eventually_ne (A.deriv_ne Q hQ)
  filter_upwards [hτnear.eventually hkey, hτnear.eventually hσd, hid, hτd0] with y hy hσy hidy hτy
  rw [hy]
  show OriginalChart.readDifferential N Q θ (σ (τ y)) * deriv σ (τ y) * deriv τ y = OriginalChart.readDifferential N Q θ y
  rw [hidy, hσy.deriv, hidy, mul_assoc, inv_mul_cancel₀ hτy, mul_one]

end
end Dubon2026.SourceFunctionField.CellGeometry
