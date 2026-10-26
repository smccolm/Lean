import Dubon2026.SourcePrimitiveOriginalTateEvaluation
import Dubon2026.SourcePolynomialSpecialization
import Dubon2026.SourceSpecializationBaseChangeIntertwiner

/-! DUB-17/18 -> primitive determinant -> compare with the same existing
primitive specialization. Its original prime Hecke eigenvalues imply that
the actual good-prime annihilator acts by zero and its normalized arithmetic
projector acts by the identity after the prescribed specialization. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Polynomial TensorProduct
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
local notation "Qbar" => AlgebraicClosure ℚ
variable {E : Type*} [Field E] [Algebra ℚ_[p] E]
local notation "VE" => E ⊗[ℚ_[p]] originalRationalTateModule N p
private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem original_specialization_coefficient_hecke {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (π : originalRationalTateModule N p →ₗ[ℚ_[p]] (Fin 2 → E))
    (q : Nat.Primes) (a : E)
    (hH : ∀ x, π ((TateModule.tateMap p (originalHeckePicard Qbar N q.val)).baseChange ℚ_[p] x) =
      a • π x) (x : VE) :
    π.liftBaseChange E (originalCuspCoefficientTateHecke N p b P₀ lb
      (primitiveIntegralHeckeIndex N ⟨q.val, q.property.pos⟩) x) = a • π.liftBaseChange E x := by
  exact (congrArg (fun H : Module.End E VE => π.liftBaseChange E (H x))
    (originalCuspCoefficientTateHecke_prime N p b P₀ lb (E := E) q)).trans
      (liftBaseChange_scalar_intertwine π
        ((TateModule.tateMap p (originalHeckePicard Qbar N q.val)).baseChange ℚ_[p]) a hH x)

theorem original_specialization_primitive_annihilator {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (π : originalRationalTateModule N p →ₗ[ℚ_[p]] (Fin 2 → E))
    (hH : ∀ (q : Nat.Primes) (x : originalRationalTateModule N p),
      π ((TateModule.tateMap p (originalHeckePicard Qbar N q.val)).baseChange ℚ_[p] x) =
        τ (sourcePrimitiveFieldCoefficient f q.val) • π x)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) (x : VE) :
    π.liftBaseChange E (primitiveOriginalTateEvaluation N p b P₀ lb f τ
      (primitiveGoodTensorAnnihilator N f s) x) = 0 := by
  rw [primitiveOriginalTateEvaluation_annihilator]
  exact specialization_shifted_squares_zero (π.liftBaseChange E) s
    (fun q => originalCuspCoefficientTateHecke N p b P₀ lb
      (primitiveIntegralHeckeIndex N ⟨q.val.val, q.val.property.pos⟩))
    (fun q => τ (sourcePrimitiveFieldCoefficient f q.val.val))
    (fun q _ => original_specialization_coefficient_hecke N p b P₀ lb π q.val _ (hH q.val)) x

theorem original_specialization_primitive_projector {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (π : originalRationalTateModule N p →ₗ[ℚ_[p]] (Fin 2 → E))
    (hH : ∀ (q : Nat.Primes) (x : originalRationalTateModule N p),
      π ((TateModule.tateMap p (originalHeckePicard Qbar N q.val)).baseChange ℚ_[p] x) =
        τ (sourcePrimitiveFieldCoefficient f q.val) • π x)
    (s : Finset {q : Nat.Primes // q.val.Coprime N})
    (P : (sourcePrimitiveCoefficientField f)[X]) (hP : P.eval 0 = 1) (x : VE) :
    π.liftBaseChange E (primitiveOriginalTateEvaluation N p b P₀ lb f τ
      (primitiveGoodTensorProjector N f s P) x) = π.liftBaseChange E x := by
  rw [primitiveOriginalTateEvaluation_projector]
  have h := specialization_aeval_zero (π.liftBaseChange E)
    (primitiveOriginalTateEvaluation N p b P₀ lb f τ (primitiveGoodTensorAnnihilator N f s))
    (original_specialization_primitive_annihilator N p b P₀ lb f τ π hH s) (P.map τ) x
  simpa only [Polynomial.eval_zero_map, hP, map_one, one_smul] using h

end
end Dubon2026.SourceFunctionField.OriginalChart
