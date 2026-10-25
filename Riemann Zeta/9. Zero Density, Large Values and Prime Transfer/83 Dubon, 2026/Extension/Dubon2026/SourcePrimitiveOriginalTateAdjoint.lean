import Dubon2026.SourcePrimitiveOriginalTateEvaluation
import Dubon2026.SourceOriginalCoefficientWeilLaws
import Dubon2026.SourceBilinearPolynomialAdjoint

/-! DUB-17/18 -> primitive determinant -> the actual primitive Tate projector.
Its self-adjointness follows from its good-prime sum of squares and the
same coefficient polynomial, with no full-Hecke adjointness premise. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Polynomial TensorProduct
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
variable {E : Type*} [Field E] [Algebra ℚ_[p] E]

theorem primitiveOriginalTateEvaluation_annihilator_selfAdjoint {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) :
    (originalCoefficientWeilBilinear N p E).IsSelfAdjoint
      (primitiveOriginalTateEvaluation N p b P₀ lb f τ (primitiveGoodTensorAnnihilator N f s)) := by
  rw [primitiveOriginalTateEvaluation_annihilator]
  apply bilinear_selfAdjoint_sum_shifted_squares
  intro q _
  rw [originalCuspCoefficientTateHecke_prime]
  letI : Fact q.val.val.Prime := ⟨q.val.property⟩
  exact originalCoefficientWeilBilinear_hecke N p E q.val.val
    ((Nat.Prime.coprime_iff_not_dvd q.val.property).mp q.property)

theorem primitiveOriginalTateEvaluation_projector_selfAdjoint {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) (P : (sourcePrimitiveCoefficientField f)[X]) :
    (originalCoefficientWeilBilinear N p E).IsSelfAdjoint
      (primitiveOriginalTateEvaluation N p b P₀ lb f τ (primitiveGoodTensorProjector N f s P)) := by
  rw [primitiveOriginalTateEvaluation_projector]
  exact bilinear_selfAdjoint_aeval (originalCoefficientWeilBilinear N p E) _
    (primitiveOriginalTateEvaluation_annihilator_selfAdjoint N p b P₀ lb f τ s) (P.map τ)

end
end Dubon2026.SourceFunctionField.OriginalChart
