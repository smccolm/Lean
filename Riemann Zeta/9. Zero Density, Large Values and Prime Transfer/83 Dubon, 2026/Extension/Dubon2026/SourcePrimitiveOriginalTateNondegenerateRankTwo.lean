import Dubon2026.SourcePrimitiveOriginalTateRankTwo
import Dubon2026.SourcePrimitiveOriginalTateRestriction

/-! DUB-17/18 -> primitive Frobenius determinant. One actual arithmetic
projector has a rank-two original Tate image and a nondegenerate restriction
of the literal root-valued Weil pairing. The determinant and comparison to
the existing spanning primitive specialization remain subsequent obligations. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Polynomial TensorProduct
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
variable {E : Type*} [Field E] [Algebra ℚ_[p] E]

theorem exists_primitive_originalTate_nondegenerate_rankTwo {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E) :
    ∃ (s : Finset {q : Nat.Primes // q.val.Coprime N})
      (P : (sourcePrimitiveCoefficientField f)[X]), P.eval 0 = 1 ∧
      let Q := primitiveOriginalTateEvaluation N p b P₀ lb f τ
        (primitiveGoodTensorProjector N f s P)
      Nonempty (Q.range ≃ₗ[E] (Fin 2 → E)) ∧
      IsIdempotentElem Q ∧ (originalCoefficientWeilBilinear N p E).IsSelfAdjoint Q ∧
      Function.Injective ((originalCoefficientWeilBilinear N p E).compl₁₂
        Q.range.subtype Q.range.subtype) := by
  exact (exists_primitive_originalTate_rankTwo N p b P₀ lb f τ).imp fun s hs =>
    hs.imp fun P h => ⟨h.1, h.2.2,
      mapped_idempotent_pairing_restriction (originalCoefficientWeilBilinear N p E)
        (originalCoefficientWeilBilinear_injective N p E)
        (primitiveOriginalTateEvaluation N p b P₀ lb f τ)
        (primitiveGoodTensorProjector N f s P) h.2.1
        (primitiveOriginalTateEvaluation_projector_selfAdjoint N p b P₀ lb f τ s P)⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
