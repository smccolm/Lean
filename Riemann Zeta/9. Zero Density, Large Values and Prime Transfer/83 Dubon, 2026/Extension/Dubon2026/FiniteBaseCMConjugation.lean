import Dubon2026.FiniteBaseCMSymmetricMatrices
import Dubon2026.RepresentationIrreducibilityFromRestriction
import Dubon2026.MatrixAdjointScalarDescent

/-! The actual real-place conjugation on the original CM group is
continuous and preserves absolute residual irreducibility. These are the
domain and residual hypotheses of the trace-conjugacy step in DUB-17's
polarization descent. -/

namespace Dubon2026
open NumberField Algebra Matrix
open scoped NumberField
noncomputable section

/-- Preserve the original rational algebra on the arithmetic extension. -/
local instance finiteBaseCMConjugationUnionAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

variable (a : 𝓞 ℚ) (F : IntermediateField ℚ (rationalUnramifiedExtension a))
  [FiniteDimensional ℚ F] [IsTotallyReal F]
  (K : IntermediateField F (rationalUnramifiedExtension a))
  [IsQuadraticExtension F K] [IsTotallyComplex K]

/-- Conjugation by the actual original real-place element is continuous
on the CM kernel, in its original inherited Krull topology. -/
def finiteBaseCMConjugation : FiniteBaseCMKernel a F K →ₜ* FiniteBaseCMKernel a F K where
  toFun g := ⟨finiteBaseRealConjugation a F * g.val * (finiteBaseRealConjugation a F)⁻¹, by
    have hg : finiteBaseQuadraticComponent a F K g.val = 1 := g.property
    change finiteBaseQuadraticComponent a F K
      (finiteBaseRealConjugation a F * g.val * (finiteBaseRealConjugation a F)⁻¹) = 1
    rw [map_mul, map_mul, map_inv, hg, mul_one, mul_inv_cancel]⟩
  map_one' := Subtype.ext (by simp)
  map_mul' g h := Subtype.ext (by
    change finiteBaseRealConjugation a F * (g.val * h.val) * (finiteBaseRealConjugation a F)⁻¹ =
      (finiteBaseRealConjugation a F * g.val * (finiteBaseRealConjugation a F)⁻¹) *
        (finiteBaseRealConjugation a F * h.val * (finiteBaseRealConjugation a F)⁻¹)
    group)
  continuous_toFun := by
    exact ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _

/-- The continuous formula is the actual action in the original CM splitting. -/
theorem finiteBaseCMConjugation_eq :
    (finiteBaseCMConjugation a F K).toMonoidHom =
      ((finiteBaseCMGroupSplitting a F K).conjAct
        (Multiplicative.ofAdd (1 : ZMod 2))).toMonoidHom := by
  apply MonoidHom.ext
  intro g
  exact Subtype.ext (finiteBaseCMKernel_conjugate a F K g).symm

/-- The actual CM conjugation reaches every original CM group element. -/
theorem finiteBaseCMConjugation_surjective : Function.Surjective (finiteBaseCMConjugation a F K) := by
  change Function.Surjective (finiteBaseCMConjugation a F K).toMonoidHom
  rw [finiteBaseCMConjugation_eq]
  exact ((finiteBaseCMGroupSplitting a F K).conjAct (Multiplicative.ofAdd (1 : ZMod 2))).surjective

/-- Original absolute irreducibility persists under the actual CM
conjugation, by restriction along the inverse arithmetic automorphism. -/
theorem finiteBaseCMConjugate_absoluteIrreducible
    {ι k L : Type} [Fintype ι] [DecidableEq ι] [Field k] [Field L] [Algebra k L]
    (σ : FiniteBaseCMKernel a F K →* GeneralLinearGroup ι k)
    [Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) σ))] :
    Representation.IsIrreducible (matrixStandardRepresentation
      (matrixCoefficientExtension (L := L) (σ.comp (finiteBaseCMConjugation a F K).toMonoidHom))) := by
  let e := (finiteBaseCMGroupSplitting a F K).conjAct (Multiplicative.ofAdd (1 : ZMod 2))
  let r := matrixStandardRepresentation (matrixCoefficientExtension (L := L) σ)
  rw [finiteBaseCMConjugation_eq]
  change Representation.IsIrreducible (r.comp e.toMonoidHom)
  have he : (r.comp e.toMonoidHom).comp e.symm.toMonoidHom = r :=
    MonoidHom.ext (fun g => congrArg r (e.apply_symm_apply g))
  letI : Representation.IsIrreducible ((r.comp e.toMonoidHom).comp e.symm.toMonoidHom) := by
    rw [he]
    infer_instance
  exact representation_irreducible_of_restriction e.symm.toMonoidHom (r.comp e.toMonoidHom)

end
end Dubon2026
