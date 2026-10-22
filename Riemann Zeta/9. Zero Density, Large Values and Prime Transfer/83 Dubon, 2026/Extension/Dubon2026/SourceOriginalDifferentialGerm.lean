import Dubon2026.SourceOriginalRealizationGermHom
import Dubon2026.SourceOriginalHolomorphicDifferentials

/-! DUB-17/18 -> matching cusp-form lower dimension -> injective analytic
regular-differential realization. Use the already proved original j-basis
and punctured realization ring homomorphism. Only the resulting linear germ
map is needed for the dimension comparison; no new function-field model is
introduced.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open UpperHalfPlane Filter KaehlerDifferential SourceCurve
open scoped Topology

/-- The actual original differential space is coordinated by d(j). -/
def originalDifferentialCoordinateEquiv (N : ℕ) [NeZero N] :
    modularFunctionFieldOver N ℂ ≃ₗ[modularFunctionFieldOver N ℂ]
      Ω[modularFunctionFieldOver N ℂ⁄ℂ] :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (modularFunctionFieldOver N ℂ)
      Ω[modularFunctionFieldOver N ℂ⁄ℂ] (D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ)))
    ⟨smul_left_injective (modularFunctionFieldOver N ℂ) (D_jOver_ne_zero N ℂ), by
      rw [← LinearMap.range_eq_top, LinearMap.range_toSpanSingleton, span_D_jOver]⟩

theorem originalDifferentialCoordinateEquiv_apply (N : ℕ) [NeZero N]
    (x : modularFunctionFieldOver N ℂ) :
    originalDifferentialCoordinateEquiv N x =
      x • D ℂ (modularFunctionFieldOver N ℂ) (jOver N ℂ) := rfl

/-- Original meromorphic realization, as a complex-linear map on germs. -/
def originalRealizeGermLinear (N : ℕ) [NeZero N] (τ : ℍ) :
    modularFunctionFieldOver N ℂ →ₗ[ℂ] Germ (𝓝[≠] (τ : ℂ)) ℂ where
  toFun := originalRealizeGerm N τ
  map_add' := (originalRealizeGerm N τ).map_add
  map_smul' c x := by
    rw [Algebra.smul_def, map_mul, originalRealizeGerm_algebraMap]
    rfl

/-- The analytic germ of the differential with original coefficient x. -/
def originalCoefficientDifferentialGerm (N : ℕ) [NeZero N] (τ : ℍ) :
    modularFunctionFieldOver N ℂ →ₗ[ℂ] Germ (𝓝[≠] (τ : ℂ)) ℂ where
  toFun x := originalRealizeGermLinear N τ x *
    ((deriv (JMultiplicity.jf ∘ ofComplex)) : Germ (𝓝[≠] (τ : ℂ)) ℂ)
  map_add' x y := by rw [map_add, add_mul]
  map_smul' c x := by
    rw [map_smul]
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun z => mul_assoc c _ _

theorem eventually_raw_j_derivative_ne_zero (N : ℕ) [NeZero N] (τ : ℍ) :
    ∀ᶠ z in 𝓝[≠] (τ : ℂ), deriv (JMultiplicity.jf ∘ ofComplex) z ≠ 0 := by
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero
    (JMultiplicity.analyticAt_comp JMultiplicity.mdifferentiable_jf τ).deriv.meromorphicAt).mp
  rw [original_analytic_derivative_order N τ]
  exact WithTop.coe_ne_top

theorem originalCoefficientDifferentialGerm_injective (N : ℕ) [NeZero N] (τ : ℍ) :
    Function.Injective (originalCoefficientDifferentialGerm N τ) := by
  intro x y h
  apply (originalRealizeGerm N τ).injective
  apply Germ.coe_eq.mpr
  have he : (fun z : ℂ => realize N (x : LaurentSeries ℂ) (ofComplex z) *
      deriv (JMultiplicity.jf ∘ ofComplex) z) =ᶠ[𝓝[≠] (τ : ℂ)]
      fun z => realize N (y : LaurentSeries ℂ) (ofComplex z) *
        deriv (JMultiplicity.jf ∘ ofComplex) z := Germ.coe_eq.mp h
  filter_upwards [he, eventually_raw_j_derivative_ne_zero N τ] with z hz hd
  exact mul_right_cancel₀ hd hz

/-- The complex-linear analytic germ map on the actual regular differentials. -/
def originalRegularDifferentialGerm (N : ℕ) [NeZero N] (τ : ℍ) :
    regularDifferentials ℂ (modularFunctionFieldOver N ℂ) →ₗ[ℂ]
      Germ (𝓝[≠] (τ : ℂ)) ℂ :=
  (originalCoefficientDifferentialGerm N τ).comp
    (((originalDifferentialCoordinateEquiv N).symm.restrictScalars ℂ).toLinearMap.comp
      (regularDifferentials ℂ (modularFunctionFieldOver N ℂ)).subtype)

theorem originalRegularDifferentialGerm_injective (N : ℕ) [NeZero N] (τ : ℍ) :
    Function.Injective (originalRegularDifferentialGerm N τ) :=
  (originalCoefficientDifferentialGerm_injective N τ).comp
    ((originalDifferentialCoordinateEquiv N).symm.injective.comp Subtype.val_injective)

end
end Dubon2026.SourceFunctionField
