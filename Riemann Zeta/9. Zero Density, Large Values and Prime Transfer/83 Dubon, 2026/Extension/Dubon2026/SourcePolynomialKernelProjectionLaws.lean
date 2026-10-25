import Dubon2026.SourcePolynomialKernelProjection
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! DUB-17/18 -> primitive component. The constructed polynomial fixes
the kernel, has exactly that range, and is idempotent. These identities
are the algebraic ones to retain under the original matrix comparison. -/
namespace Dubon2026
noncomputable section
open Polynomial
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem kernel_projector_polynomial_fixes (H : Module.End K V) (P : K[X])
    (hP : P.eval 0 = 1) (x : V) (hx : H x = 0) : aeval H P x = x := by
  have he : H x = (0 : K) • x := by simpa only [zero_smul] using hx
  simpa only [hP, one_smul] using Module.End.aeval_apply_of_mem_apply_eq_smul (p := P) he

theorem kernel_projector_polynomial_range (H : Module.End K V) (P : K[X])
    (hP : P.eval 0 = 1) (hHP : H * aeval H P = 0) :
    LinearMap.range (aeval H P) = LinearMap.ker H := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact congrArg (fun T : Module.End K V => T x) hHP
  · intro x hx
    exact ⟨x, kernel_projector_polynomial_fixes H P hP x hx⟩

theorem kernel_projector_polynomial_idempotent (H : Module.End K V) (P : K[X])
    (hP : P.eval 0 = 1) (hHP : H * aeval H P = 0) :
    IsIdempotentElem (aeval H P) := by
  apply LinearMap.ext
  intro x
  exact kernel_projector_polynomial_fixes H P hP (aeval H P x)
    (congrArg (fun T : Module.End K V => T x) hHP)

end
end Dubon2026
