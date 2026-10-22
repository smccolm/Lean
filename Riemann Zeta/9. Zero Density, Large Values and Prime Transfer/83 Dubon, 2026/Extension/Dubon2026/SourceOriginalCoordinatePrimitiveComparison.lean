import Dubon2026.SourceOriginalCellCoefficientPullback
import Dubon2026.SourceComplexPrimitiveGluing

/-! DUB-17/18 -> original Abel-Jacobi -> regular loop-period generation.
This is a necessary step in converting arbitrary actual path integrals into
the subgroup of the constructed primitive jumps. Adapted from
S_AlgebraicCurve_CellDissection_exists_int_pathIntegral_sub_primitive_eq_sum_jump,
anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2.
Reuse original cell compactness, coefficient pullback and primitive uniqueness;
no new ambient curve, manifold, compactness or primitive existence is assumed.
-/
namespace Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
noncomputable section
open SourceCurve Set Filter KaehlerDifferential OriginalChart
open scoped Topology Manifold
attribute [local instance] placeTopology placeChartedSpace
variable {N : ℕ} [NeZero N] {κ : Type*}
local notation "F" => modularFunctionFieldOver N ℂ

theorem hasDerivAt_coordPrimitive (A : AnalyticCoord N) {y : Place ℂ F}
    (hy : y ∈ A.ζ.source) {W : Set ℂ} (hW : IsOpen W) (hyW : A.ζ y ∈ W)
    {θ : Ω[F⁄ℂ]} {Ψ : ℂ → ℂ}
    (hΨ : ∀ w ∈ W, HasDerivAt Ψ (coeffIn A.ζ θ w) w)
    (hθ : 0 ≤ y.ordDifferential θ) :
    ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) y y),
      HasDerivAt (Ψ ∘ A.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm) (readDifferential N y θ z) z := by
  set τ : ℂ → ℂ := A.ζ ∘ (extChartAt 𝓘(ℂ, ℂ) y).symm with hτ
  have hlaw := A.coeff_comp_mul_deriv hy (y.mem_of_ord_nonneg hθ)
  have hτc : τ (extChartAt 𝓘(ℂ, ℂ) y y) = A.ζ y := by
    show A.ζ ((extChartAt 𝓘(ℂ, ℂ) y).symm (extChartAt 𝓘(ℂ, ℂ) y y)) = A.ζ y
    rw [(extChartAt 𝓘(ℂ, ℂ) y).left_inv (mem_extChartAt_source y)]
  have hτnear : Tendsto τ (𝓝 (extChartAt 𝓘(ℂ, ℂ) y y)) (𝓝 (A.ζ y)) := by
    rw [← hτc]; exact (A.analytic y hy).continuousAt
  have hWnear : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) y y), τ z ∈ W :=
    hτnear.eventually (hW.mem_nhds hyW)
  filter_upwards [hlaw, hWnear, (A.analytic y hy).eventually_analyticAt] with z hz hzW hτz
  have h1 : HasDerivAt (Ψ ∘ τ) (coeffIn A.ζ θ (τ z) * deriv τ z) z :=
    (hΨ _ hzW).comp z hτz.differentiableAt.hasDerivAt
  rw [hz] at h1
  exact h1

theorem eventually_coordPrimitive_sub_eq {y : Place ℂ F} {θ : Ω[F⁄ℂ]} {Φ₁ Φ₂ : ℂ → ℂ}
    (h₁ : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) y y), HasDerivAt Φ₁ (readDifferential N y θ z) z)
    (h₂ : ∀ᶠ z in 𝓝 (extChartAt 𝓘(ℂ, ℂ) y y), HasDerivAt Φ₂ (readDifferential N y θ z) z) :
    ∀ᶠ x in 𝓝 y, Φ₁ (extChartAt 𝓘(ℂ, ℂ) y x) - Φ₂ (extChartAt 𝓘(ℂ, ℂ) y x) =
      Φ₁ (extChartAt 𝓘(ℂ, ℂ) y y) - Φ₂ (extChartAt 𝓘(ℂ, ℂ) y y) :=
  (continuousAt_extChartAt (I := 𝓘(ℂ, ℂ)) y).eventually
    (OriginalPrimitiveGlue.eventually_sub_eq_of_hasDerivAt h₁ h₂)

end
end Dubon2026.SourceFunctionField.CellGeometry.DissectionPeriods
