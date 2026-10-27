import Dubon2026.SourceGammaOneMeromorphicRealization

/-! DUB-17/18 -> actual Gamma1 differential/cusp converse -> normalized
analytic places. Actual modular quotient realization preserves constants
and the addition and multiplication of punctured germs. Adapt the proved
SourceOriginalRealizationAlgebra; no germ homomorphism is assumed. -/
namespace Dubon2026.SourceFunctionField.GammaOne
noncomputable section
open UpperHalfPlane Filter ModularRatios
open scoped MatrixGroups Topology Manifold

theorem realize_algebraMap {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (hT : ModularGroup.T ∈ Γ) (c : ℂ) (τ : ℍ) :
    realize Γ (algebraMap ℂ (LaurentSeries ℂ) c) τ = c := by
  have he : algebraMap ℂ (LaurentSeries ℂ) c * qL (1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0) =
      qL (c • (1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0)) := by
    rw [qL_one, mul_one, qL_const hT]
  rw [realize_eq_div Γ hT (c • (1 : ModularForm (Γ : Subgroup (GL (Fin 2) ℝ)) 0)) 1 _ he τ (by simp)]
  simp

theorem realize_mul_eventuallyEq {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (hT : ModularGroup.T ∈ Γ)
    (x y : functionFieldOver Γ ℂ) (τ : ℍ) :
    (fun z : ℂ => realize Γ ((x * y : functionFieldOver Γ ℂ) : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z : ℂ => realize Γ (x : LaurentSeries ℂ) (ofComplex z)) *
        fun z => realize Γ (y : LaurentSeries ℂ) (ofComplex z) := by
  obtain ⟨a, g, h, hh, hx⟩ := functionFieldOver_modular_ratio hT x
  obtain ⟨b, g', h', hh', hy⟩ := functionFieldOver_modular_ratio hT y
  change (x : LaurentSeries ℂ) * qL h = qL g at hx
  change (y : LaurentSeries ℂ) * qL h' = qL g' at hy
  have he : ((x * y : functionFieldOver Γ ℂ) : LaurentSeries ℂ) * qL (h.mul h') =
      qL (g.mul g') := by
    change (x : LaurentSeries ℂ) * (y : LaurentSeries ℂ) * qL (h.mul h') = _
    rw [qL_mul hT, qL_mul hT, ← hx, ← hy]
    ring
  filter_upwards [realize_eventuallyEq_of_ratio hT (g.mul g') (h.mul h') _
    (mul_ne_zero' hT h h' hh hh') he τ,
    realize_eventuallyEq_of_ratio hT g h x hh hx τ,
    realize_eventuallyEq_of_ratio hT g' h' y hh' hy τ] with z hxy hxe hye
  rw [Pi.mul_apply, hxy, hxe, hye]
  change (g (ofComplex z) * g' (ofComplex z)) / (h (ofComplex z) * h' (ofComplex z)) = _
  exact mul_div_mul_comm _ _ _ _

theorem realize_add_eventuallyEq {Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)} (hT : ModularGroup.T ∈ Γ)
    (x y : functionFieldOver Γ ℂ) (τ : ℍ) :
    (fun z : ℂ => realize Γ ((x + y : functionFieldOver Γ ℂ) : LaurentSeries ℂ) (ofComplex z))
      =ᶠ[𝓝[≠] (τ : ℂ)]
      (fun z : ℂ => realize Γ (x : LaurentSeries ℂ) (ofComplex z)) +
        fun z => realize Γ (y : LaurentSeries ℂ) (ofComplex z) := by
  obtain ⟨a, g, h, hh, hx⟩ := functionFieldOver_modular_ratio hT x
  obtain ⟨b, g', h', hh', hy⟩ := functionFieldOver_modular_ratio hT y
  change (x : LaurentSeries ℂ) * qL h = qL g at hx
  change (y : LaurentSeries ℂ) * qL h' = qL g' at hy
  have he : ((x + y : functionFieldOver Γ ℂ) : LaurentSeries ℂ) * qL (h.mul h') =
      qL (g.mul h' + h.mul g') := by
    change ((x : LaurentSeries ℂ) + (y : LaurentSeries ℂ)) * qL (h.mul h') = _
    rw [qL_add hT, qL_mul hT, qL_mul hT, qL_mul hT, ← hx, ← hy]
    ring
  filter_upwards [realize_eventuallyEq_of_ratio hT (g.mul h' + h.mul g') (h.mul h') _
    (mul_ne_zero' hT h h' hh hh') he τ,
    realize_eventuallyEq_of_ratio hT g h x hh hx τ,
    realize_eventuallyEq_of_ratio hT g' h' y hh' hy τ,
    eventually_ne_zero_ofComplex h hh τ,
    eventually_ne_zero_ofComplex h' hh' τ] with z hxy hxe hye hz hz'
  rw [Pi.add_apply, hxy, hxe, hye]
  change (g (ofComplex z) * h' (ofComplex z) + h (ofComplex z) * g' (ofComplex z)) /
    (h (ofComplex z) * h' (ofComplex z)) = _
  rw [div_add_div _ _ hz hz']

end
end Dubon2026.SourceFunctionField.GammaOne
