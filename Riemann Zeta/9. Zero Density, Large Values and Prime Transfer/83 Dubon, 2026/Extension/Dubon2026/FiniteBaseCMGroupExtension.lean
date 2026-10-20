import Dubon2026.FiniteBaseCMSection
import Mathlib.GroupTheory.GroupExtension.Basic

/-! The actual CM arithmetic extension and its semidirect decomposition,
reusing Mathlib's split-extension theorem. This supplies the domain on which
the original CM residual representation must be extended for DUB-17. -/

namespace Dubon2026
open NumberField Algebra
open scoped NumberField
noncomputable section

/-- Retain the original rational algebra in the arithmetic group extension. -/
local instance finiteBaseCMExtensionUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]

/-- The source CM arithmetic kernel in the original finite-base Galois group. -/
abbrev FiniteBaseCMKernel := (finiteBaseQuadraticComponent a F K).toMonoidHom.ker

/-- The actual arithmetic component sequence is exact. -/
def finiteBaseCMGroupExtension :
    GroupExtension (FiniteBaseCMKernel a F K) (finiteBaseArithmeticGaloisGroup a F)
      (Multiplicative (ZMod 2)) where
  inl := (FiniteBaseCMKernel a F K).subtype
  rightHom := (finiteBaseQuadraticComponent a F K).toMonoidHom
  inl_injective := Subtype.val_injective
  range_inl_eq_ker_rightHom := Subgroup.range_subtype _
  rightHom_surjective := finiteBaseQuadraticComponent_surjective a F K

/-- The original real-place involution splits this exact arithmetic sequence. -/
def finiteBaseCMGroupSplitting : (finiteBaseCMGroupExtension a F K).Splitting where
  toMonoidHom := (finiteBaseCMComponentSection a F).toMonoidHom
  rightInverse_rightHom := finiteBaseCMComponentSection_component a F K

/-- Mathlib's split-extension equivalence applied to the actual CM arithmetic group. -/
def finiteBaseCMSemidirectEquiv :
    SemidirectProduct (FiniteBaseCMKernel a F K) (Multiplicative (ZMod 2))
      (finiteBaseCMGroupSplitting a F K).conjAct ≃* finiteBaseArithmeticGaloisGroup a F :=
  (finiteBaseCMGroupSplitting a F K).semidirectProductMulEquiv

/-- The equivalence multiplies the actual kernel element and the real-place section. -/
theorem finiteBaseCMSemidirectEquiv_apply
    (x : SemidirectProduct (FiniteBaseCMKernel a F K) (Multiplicative (ZMod 2))
      (finiteBaseCMGroupSplitting a F K).conjAct) :
    finiteBaseCMSemidirectEquiv a F K x =
      (x.left : finiteBaseArithmeticGaloisGroup a F) * finiteBaseCMComponentSection a F x.right := rfl

/-- The inverse decomposition retains the actual CM restriction character. -/
theorem finiteBaseCMSemidirectEquiv_symm_component (g : finiteBaseArithmeticGaloisGroup a F) :
    ((finiteBaseCMSemidirectEquiv a F K).symm g).right = finiteBaseQuadraticComponent a F K g := rfl

/-- The inverse kernel coordinate is the original element divided by its real-place section. -/
theorem finiteBaseCMSemidirectEquiv_symm_kernel (g : finiteBaseArithmeticGaloisGroup a F) :
    (((finiteBaseCMSemidirectEquiv a F K).symm g).left : finiteBaseArithmeticGaloisGroup a F) =
      g * (finiteBaseCMComponentSection a F (finiteBaseQuadraticComponent a F K g))⁻¹ := by
  apply (eq_mul_inv_iff_mul_eq).mpr
  have h := (finiteBaseCMSemidirectEquiv a F K).apply_symm_apply g
  rw [finiteBaseCMSemidirectEquiv_apply, finiteBaseCMSemidirectEquiv_symm_component] at h
  exact h

end
end Dubon2026
