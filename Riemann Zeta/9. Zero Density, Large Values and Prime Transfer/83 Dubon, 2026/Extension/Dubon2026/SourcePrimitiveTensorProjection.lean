import Dubon2026.SourcePrimitiveTensorOperators

/-! DUB-17/18 -> original Tate primitive component. Faithfulness of the
actual coefficient realization lifts idempotence and every required Hecke
scalar identity into the literal arithmetic tensor algebra. -/
namespace Dubon2026
noncomputable section
open Polynomial TensorProduct
variable (N : ℕ) [NeZero N]
local notation "TZ" => sourceOriginalIntegralHeckeAlgebra N 2

theorem exists_primitive_tensor_projection (f : PrimitiveCuspForm N 2) :
    ∃ (s : Finset {q : Nat.Primes // q.val.Coprime N})
      (P : Polynomial (sourcePrimitiveCoefficientField f)),
      P.eval 0 = 1 ∧
      primitiveGoodTensorAnnihilator N f s * primitiveGoodTensorProjector N f s P = 0 ∧
      IsIdempotentElem (primitiveGoodTensorProjector N f s P) ∧
      ∀ n : ℕ+, ((1 : sourcePrimitiveCoefficientField f) ⊗ₜ[ℤ] primitiveIntegralHeckeIndex N n) *
          primitiveGoodTensorProjector N f s P =
        sourcePrimitiveFieldCoefficient f n • primitiveGoodTensorProjector N f s P := by
  obtain ⟨s, P, hP, hHP, _, hIdem, hHecke⟩ :=
    exists_primitive_good_coefficient_hecke_projection N f
  refine ⟨s, P, hP, ?_, ?_, ?_⟩
  · apply integerCoefficientExtension_mul_eq_zero
      (algebraMap (sourcePrimitiveCoefficientField f) ℂ)
      (sourceOriginalIntegralHeckeAlgebra N 2).val.toRingHom
      (primitiveCoefficientCuspEvaluation_injective N f)
    change primitiveCoefficientCuspEvaluation N f (primitiveGoodTensorAnnihilator N f s) *
      primitiveCoefficientCuspEvaluation N f (primitiveGoodTensorProjector N f s P) = 0
    rw [primitiveCoefficientCuspEvaluation_annihilator, primitiveCoefficientCuspEvaluation_projector]
    exact hHP
  · apply integerCoefficientExtension_idempotent
      (algebraMap (sourcePrimitiveCoefficientField f) ℂ)
      (sourceOriginalIntegralHeckeAlgebra N 2).val.toRingHom
      (primitiveCoefficientCuspEvaluation_injective N f)
    change IsIdempotentElem (primitiveCoefficientCuspEvaluation N f (primitiveGoodTensorProjector N f s P))
    rw [primitiveCoefficientCuspEvaluation_projector]
    exact hIdem
  · intro n
    apply integerCoefficientExtension_mul_eq_smul
      (algebraMap (sourcePrimitiveCoefficientField f) ℂ)
      (sourceOriginalIntegralHeckeAlgebra N 2).val.toRingHom
      (primitiveCoefficientCuspEvaluation_injective N f)
    change primitiveCoefficientCuspEvaluation N f
      ((1 : sourcePrimitiveCoefficientField f) ⊗ₜ[ℤ] primitiveIntegralHeckeIndex N n) *
      primitiveCoefficientCuspEvaluation N f (primitiveGoodTensorProjector N f s P) =
      cuspCoefficients f.toCuspForm n •
      primitiveCoefficientCuspEvaluation N f (primitiveGoodTensorProjector N f s P)
    rw [primitiveCoefficientCuspEvaluation_hecke, primitiveCoefficientCuspEvaluation_projector]
    exact hHecke n n.pos

end
end Dubon2026
