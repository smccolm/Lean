import Dubon2026.SourceFractionTensorInjective
import Mathlib.LinearAlgebra.BilinearForm.TensorProduct

/-! DUB-17/18 -> primitive determinant -> required Hecke component pairing.
The actual integral Tate pairing must remain nondegenerate on its literal
fraction-field tensor. Native module localization reduces this to evaluation
on integral pure tensors; no perfect-pairing or target basis is assumed. -/
namespace Dubon2026
noncomputable section
open scoped TensorProduct

theorem sourceFraction_bilinear_baseChange_injective
    {R K M W : Type*} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup M] [Module R M] [AddCommGroup W] [Module R W]
    (B : M →ₗ[R] M →ₗ[R] W) (hB : Function.Injective B)
    (hW : Function.Injective (TensorProduct.mk R K W 1)) :
    Function.Injective (LinearMap.BilinMap.baseChange K B) := by
  let j := TensorProduct.mk R K M 1
  letI : IsLocalizedModule (nonZeroDivisors R) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K j).mpr
      (TensorProduct.isBaseChange R M K)
  apply IsLocalizedModule.injective_of_map_eq (nonZeroDivisors R) j
    (g := (LinearMap.BilinMap.baseChange K B).restrictScalars R)
  intro x y h
  apply congrArg j
  apply hB
  apply LinearMap.ext
  intro z
  apply hW
  have hz := congrArg (fun f => f ((1 : K) ⊗ₜ[R] z)) h
  change (1 : K) ⊗ₜ[R] B x z = (1 : K) ⊗ₜ[R] B y z
  change LinearMap.BilinMap.baseChange K B ((1 : K) ⊗ₜ[R] x) ((1 : K) ⊗ₜ[R] z) =
    LinearMap.BilinMap.baseChange K B ((1 : K) ⊗ₜ[R] y) ((1 : K) ⊗ₜ[R] z) at hz
  simpa only [LinearMap.BilinMap.baseChange_tmul, one_mul] using hz

end
end Dubon2026
