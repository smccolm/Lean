import Dubon2026.FiniteBaseCMKernel

/-! The continuous kernel coordinate of the original split CM arithmetic
group. Its exact formula is needed to extend continuous residual matrices
without assuming continuity of an abstract semidirect decomposition. -/

namespace Dubon2026
open NumberField Algebra
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the continuous CM decomposition. -/
local instance finiteBaseCMCoordinateUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]

/-- The original element divided by the actual real-place section lies in the CM kernel. -/
def finiteBaseCMKernelCoordinate (g : finiteBaseArithmeticGaloisGroup a F) :
    FiniteBaseCMKernel a F K :=
  ⟨g * (finiteBaseCMComponentSection a F (finiteBaseQuadraticComponent a F K g))⁻¹, by
    change finiteBaseQuadraticComponent a F K
      (g * (finiteBaseCMComponentSection a F (finiteBaseQuadraticComponent a F K g))⁻¹) = 1
    rw [map_mul, map_inv, finiteBaseCMComponentSection_component, mul_inv_cancel]⟩

/-- The actual kernel coordinate is continuous in the original profinite topology. -/
theorem finiteBaseCMKernelCoordinate_continuous :
    Continuous (finiteBaseCMKernelCoordinate a F K) :=
  (continuous_id.mul (((finiteBaseCMComponentSection a F).continuous.comp
    (finiteBaseQuadraticComponent a F K).continuous).inv)).subtype_mk _

/-- Mathlib's abstract inverse has exactly this original continuous kernel coordinate. -/
theorem finiteBaseCMSemidirectEquiv_symm_left (g : finiteBaseArithmeticGaloisGroup a F) :
    ((finiteBaseCMSemidirectEquiv a F K).symm g).left = finiteBaseCMKernelCoordinate a F K g :=
  Subtype.ext (finiteBaseCMSemidirectEquiv_symm_kernel a F K g)

/-- The original kernel coordinate and real-place section reconstruct the same arithmetic element. -/
theorem finiteBaseCMKernelCoordinate_reconstruct (g : finiteBaseArithmeticGaloisGroup a F) :
    (finiteBaseCMKernelCoordinate a F K g : finiteBaseArithmeticGaloisGroup a F) *
      finiteBaseCMComponentSection a F (finiteBaseQuadraticComponent a F K g) = g :=
  inv_mul_cancel_right _ _

end
end Dubon2026
