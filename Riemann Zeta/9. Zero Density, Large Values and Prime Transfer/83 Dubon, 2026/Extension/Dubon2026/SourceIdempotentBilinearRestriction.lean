import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import Mathlib.Algebra.Ring.Idempotent

/-! DUB-17/18 -> primitive determinant -> restriction of the original pairing.
The image of a self-adjoint idempotent inherits injectivity from the ambient
bilinear map. This will be applied to the actual arithmetic primitive projector. -/
namespace Dubon2026
noncomputable section

/-- Restriction to a self-adjoint idempotent's image preserves left nondegeneracy. -/
theorem idempotent_bilinear_restriction_injective
    {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (B : V →ₗ[R] V →ₗ[R] W) (hB : Function.Injective B)
    (Q : Module.End R V) (hQ : IsIdempotentElem Q)
    (hBQ : B.IsSelfAdjoint Q) :
    Function.Injective (B.compl₁₂ Q.range.subtype Q.range.subtype) := by
  have hfix (x : Q.range) : Q x.val = x.val := by
    rcases x.property with ⟨z, hz⟩
    rw [← hz]
    exact DFunLike.congr_fun hQ z
  intro x z h
  apply Subtype.ext
  apply hB
  apply LinearMap.ext
  intro y
  calc
    B x.val y = B (Q x.val) y := by rw [hfix]
    _ = B x.val (Q y) := hBQ _ _
    _ = B z.val (Q y) :=
      congrArg (fun l => l (⟨Q y, ⟨y, rfl⟩⟩ : Q.range)) h
    _ = B (Q z.val) y := (hBQ _ _).symm
    _ = B z.val y := by rw [hfix]

end
end Dubon2026
