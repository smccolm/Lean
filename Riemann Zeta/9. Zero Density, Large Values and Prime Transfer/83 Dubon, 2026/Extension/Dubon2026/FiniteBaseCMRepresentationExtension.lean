import Dubon2026.FiniteBaseCMKernelCoordinate
import Dubon2026.PolarizedTopologicalGroup

/-! Extend original continuous CM subgroup representations by their
explicit compatible real-place action. The group law uses Mathlib's
semidirect lift; continuity uses the proved arithmetic kernel coordinate.
This is the extension step in DUB-17's polarized residual realization. -/

namespace Dubon2026
open NumberField Algebra
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the CM representation extension. -/
local instance finiteBaseCMRepresentationUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]
  {T : Type*} [Group T] [TopologicalSpace T] [IsTopologicalGroup T]
  (r : FiniteBaseCMKernel a F K →ₜ* T) (s : Multiplicative (ZMod 2) →* T)
  (h : ∀ z, r.toMonoidHom.comp ((finiteBaseCMGroupSplitting a F K).conjAct z).toMonoidHom =
    (MulAut.conj (s z)).toMonoidHom.comp r.toMonoidHom)

/-- The compatible original CM and real-place representations extend to the same arithmetic group. -/
def finiteBaseCMRepresentationExtension : finiteBaseArithmeticGaloisGroup a F →ₜ* T where
  toMonoidHom := (SemidirectProduct.lift r.toMonoidHom s h).comp
    (finiteBaseCMSemidirectEquiv a F K).symm.toMonoidHom
  continuous_toFun := by
    have he (g : finiteBaseArithmeticGaloisGroup a F) :
        (SemidirectProduct.lift r.toMonoidHom s h)
          ((finiteBaseCMSemidirectEquiv a F K).symm g) =
        r (finiteBaseCMKernelCoordinate a F K g) * s (finiteBaseQuadraticComponent a F K g) := by
      change r (((finiteBaseCMSemidirectEquiv a F K).symm g).left) *
        s (((finiteBaseCMSemidirectEquiv a F K).symm g).right) = _
      rw [finiteBaseCMSemidirectEquiv_symm_left, finiteBaseCMSemidirectEquiv_symm_component]
    change Continuous (fun g => (SemidirectProduct.lift r.toMonoidHom s h)
      ((finiteBaseCMSemidirectEquiv a F K).symm g))
    simp_rw [he]
    exact (r.continuous.comp (finiteBaseCMKernelCoordinate_continuous a F K)).mul
      (continuous_of_discreteTopology.comp (finiteBaseQuadraticComponent a F K).continuous)

/-- The constructed extension evaluates on the original arithmetic element by its actual coordinates. -/
theorem finiteBaseCMRepresentationExtension_apply (g : finiteBaseArithmeticGaloisGroup a F) :
    finiteBaseCMRepresentationExtension a F K r s h g =
      r (finiteBaseCMKernelCoordinate a F K g) * s (finiteBaseQuadraticComponent a F K g) := by
  change r (((finiteBaseCMSemidirectEquiv a F K).symm g).left) *
    s (((finiteBaseCMSemidirectEquiv a F K).symm g).right) = _
  rw [finiteBaseCMSemidirectEquiv_symm_left, finiteBaseCMSemidirectEquiv_symm_component]

/-- The constructed extension retains every original CM subgroup value. -/
theorem finiteBaseCMRepresentationExtension_kernel (g : FiniteBaseCMKernel a F K) :
    finiteBaseCMRepresentationExtension a F K r s h g.val = r g := by
  rw [finiteBaseCMRepresentationExtension_apply]
  have hg : finiteBaseQuadraticComponent a F K g.val = 1 := g.property
  have hc : finiteBaseCMKernelCoordinate a F K g.val = g := by
    apply Subtype.ext
    change g.val * (finiteBaseCMComponentSection a F (finiteBaseQuadraticComponent a F K g.val))⁻¹ = g.val
    rw [hg, map_one, inv_one, mul_one]
  rw [hc, hg, map_one, mul_one]

/-- The same extension retains the specified real-place action. -/
theorem finiteBaseCMRepresentationExtension_section (z : Multiplicative (ZMod 2)) :
    finiteBaseCMRepresentationExtension a F K r s h (finiteBaseCMComponentSection a F z) = s z := by
  rw [finiteBaseCMRepresentationExtension_apply, finiteBaseCMComponentSection_component]
  have hc : finiteBaseCMKernelCoordinate a F K (finiteBaseCMComponentSection a F z) = 1 := by
    apply Subtype.ext
    change finiteBaseCMComponentSection a F z *
      (finiteBaseCMComponentSection a F
        (finiteBaseQuadraticComponent a F K (finiteBaseCMComponentSection a F z)))⁻¹ = 1
    rw [finiteBaseCMComponentSection_component, mul_inv_cancel]
  rw [hc, map_one, one_mul]

end
end Dubon2026
