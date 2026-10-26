import Dubon2026.SourcePrimitiveOriginalTateNondegenerateRankTwo
import Dubon2026.SourceOriginalSpecializationProjector
import Dubon2026.SourceSpanningProjectorImage

/-! DUB-17/18 -> primitive determinant. The existing spanning primitive
specialization itself restricts to an isomorphism on the same nondegenerate
rank-two original Tate image. No replacement coefficient map or representation
is introduced, and no dimension or projector-preservation input remains. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Polynomial TensorProduct
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
local notation "Qbar" => AlgebraicClosure ℚ
variable {E : Type*} [Field E] [Algebra ℚ_[p] E]
private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem exists_original_primitive_specialization_image_equiv {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (π : originalRationalTateModule N p →ₗ[ℚ_[p]] (Fin 2 → E))
    (hspan : Submodule.span E (Set.range π) = ⊤)
    (hH : ∀ (q : Nat.Primes) (x : originalRationalTateModule N p),
      π ((TateModule.tateMap p (originalHeckePicard Qbar N q.val)).baseChange ℚ_[p] x) =
        τ (sourcePrimitiveFieldCoefficient f q.val) • π x) :
    ∃ (s : Finset {q : Nat.Primes // q.val.Coprime N})
      (P : (sourcePrimitiveCoefficientField f)[X]), P.eval 0 = 1 ∧
      let Q := primitiveOriginalTateEvaluation N p b P₀ lb f τ
        (primitiveGoodTensorProjector N f s P)
      ∃ e : Q.range ≃ₗ[E] (Fin 2 → E),
        (∀ x, e x = π.liftBaseChange E x.val) ∧
        IsIdempotentElem Q ∧ (originalCoefficientWeilBilinear N p E).IsSelfAdjoint Q ∧
        Function.Injective ((originalCoefficientWeilBilinear N p E).compl₁₂
          Q.range.subtype Q.range.subtype) := by
  refine (exists_primitive_originalTate_nondegenerate_rankTwo N p b P₀ lb f τ).imp
    fun s hs => hs.imp fun P h => ?_
  refine ⟨h.1, ?_⟩
  exact h.2.1.elim fun e =>
    ⟨projectorRangeSpecializationEquiv (π.liftBaseChange E) _
      (spanning_liftBaseChange_surjective π hspan)
      (original_specialization_primitive_projector N p b P₀ lb f τ π hH s P h.1) e,
      fun _ => rfl, h.2.2⟩

end
end Dubon2026.SourceFunctionField.OriginalChart
