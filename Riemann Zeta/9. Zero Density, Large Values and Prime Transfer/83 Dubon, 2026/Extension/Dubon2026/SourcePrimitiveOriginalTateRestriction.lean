import Dubon2026.SourcePrimitiveOriginalTateAdjoint
import Dubon2026.SourcePrimitiveTensorProjection
import Dubon2026.SourceEndIdempotentPairingRestriction

/-! DUB-17/18 -> primitive determinant -> the actual projector's pairing.
The constructed arithmetic idempotent maps to an actual self-adjoint Tate
idempotent, so the original pairing is injective on its image. Nonzero
rank-two identification with the prescribed specialization remains separate. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Polynomial TensorProduct
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
variable {E : Type*} [Field E] [Algebra ℚ_[p] E]

theorem exists_primitive_originalTate_pairing_restriction {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E) :
    ∃ (s : Finset {q : Nat.Primes // q.val.Coprime N})
      (P : (sourcePrimitiveCoefficientField f)[X]),
      P.eval 0 = 1 ∧
      let Q := primitiveOriginalTateEvaluation N p b P₀ lb f τ
        (primitiveGoodTensorProjector N f s P)
      IsIdempotentElem Q ∧ (originalCoefficientWeilBilinear N p E).IsSelfAdjoint Q ∧
      Function.Injective ((originalCoefficientWeilBilinear N p E).compl₁₂
        Q.range.subtype Q.range.subtype) := by
  exact (exists_primitive_tensor_projection N f).imp fun s hs => hs.imp fun P h =>
    ⟨h.1, mapped_idempotent_pairing_restriction (originalCoefficientWeilBilinear N p E)
      (originalCoefficientWeilBilinear_injective N p E)
      (primitiveOriginalTateEvaluation N p b P₀ lb f τ)
      (primitiveGoodTensorProjector N f s P) h.2.2.1
      (primitiveOriginalTateEvaluation_projector_selfAdjoint N p b P₀ lb f τ s P)⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
