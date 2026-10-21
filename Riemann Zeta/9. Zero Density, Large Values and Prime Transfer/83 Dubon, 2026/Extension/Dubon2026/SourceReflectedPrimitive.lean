import Dubon2026.SourcePeriodSlash
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.UpperHalfPlane.FunctionsBoundedAtInfty

/-! DUB-17/18 -> residual Galois association -> parabolic Hecke realization
-> period-pair injectivity -> reflected primitive. The pinned derivative
under two conjugations and the actual upper-half-plane J action replace
the external separate real-linear reflection derivative calculation.
-/
namespace Dubon2026
noncomputable section
open Complex UpperHalfPlane Filter
open scoped Topology MatrixGroups ComplexConjugate

/-- The actual conjugated primitive pulled back by J is holomorphic,
with its exact reflected derivative and sign. -/
theorem sourceReflectedPrimitive_hasDerivAt {G g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) (τ : ℂ)) (τ : ℍ) :
    HasDerivAt ((fun z : ℍ => conj (G (J • z))) ∘ ofComplex)
      (-conj (g (J • τ))) (τ : ℂ) := by
  have ho : HasDerivAt (conj ∘ (G ∘ ofComplex) ∘ conj)
      (conj (g (J • τ))) (-(τ : ℂ)) := by
    simpa only [coe_J_smul, map_neg, Complex.conj_conj] using (hG (J • τ)).conj_conj
  have hd := ho.comp (τ : ℂ) (hasDerivAt_id (τ : ℂ)).neg
  have he : ((fun z : ℍ => conj (G (J • z))) ∘ ofComplex) =ᶠ[𝓝 (τ : ℂ)]
      (conj ∘ (G ∘ ofComplex) ∘ conj) ∘ (fun z : ℂ => -z) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds τ.2] with w hw
    simp only [Function.comp_apply, J_smul, ofComplex_apply_of_im_pos hw,
      map_neg]
  simpa only [mul_neg, mul_one] using hd.congr_of_eventuallyEq he

/-- Reflection by the actual J action preserves approach to the original cusp. -/
theorem sourceReflectedPrimitive_tendsto :
    Tendsto (fun z : ℍ => J • z) atImInfty atImInfty := by
  apply tendsto_comap_iff.mpr
  simpa only [Function.comp_def, UpperHalfPlane.im, coe_J_smul,
    Complex.neg_im, Complex.conj_im, neg_neg] using
    (show Tendsto UpperHalfPlane.im atImInfty atTop from tendsto_comap)

end
end Dubon2026
