import Dubon2026.SourcePrimitiveTensorProjection
import Dubon2026.SourcePrimitiveTensorEigencharacter

/-! DUB-17/18 -> original Tate primitive component. Assemble the actual
nonzero arithmetic idempotent, its full Hecke eigencharacter identities,
and its normalization at the prescribed primitive character. -/
namespace Dubon2026
noncomputable section
open Polynomial TensorProduct
variable (N : ℕ) [NeZero N]

theorem exists_nonzero_primitive_tensor_projection (f : PrimitiveCuspForm N 2) :
    ∃ (s : Finset {q : Nat.Primes // q.val.Coprime N})
      (P : Polynomial (sourcePrimitiveCoefficientField f)),
      P.eval 0 = 1 ∧
      primitiveGoodTensorAnnihilator N f s * primitiveGoodTensorProjector N f s P = 0 ∧
      IsIdempotentElem (primitiveGoodTensorProjector N f s P) ∧
      (∀ n : ℕ+, ((1 : sourcePrimitiveCoefficientField f) ⊗ₜ[ℤ] primitiveIntegralHeckeIndex N n) *
          primitiveGoodTensorProjector N f s P =
        sourcePrimitiveFieldCoefficient f n • primitiveGoodTensorProjector N f s P) ∧
      primitiveTensorEigencharacter N f (primitiveGoodTensorProjector N f s P) = 1 ∧
      primitiveGoodTensorProjector N f s P ≠ 0 := by
  obtain ⟨s, P, hP, hHP, hIdem, hHecke⟩ := exists_primitive_tensor_projection N f
  exact ⟨s, P, hP, hHP, hIdem, hHecke, primitiveTensorEigencharacter_projector N f s P hP,
    primitiveGoodTensorProjector_ne_zero N f s P hP⟩

end
end Dubon2026
