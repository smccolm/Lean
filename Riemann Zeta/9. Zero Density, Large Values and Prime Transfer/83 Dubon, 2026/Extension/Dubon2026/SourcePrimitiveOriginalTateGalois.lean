import Dubon2026.SourcePrimitiveOriginalTateEvaluation
import Dubon2026.SourceOriginalRationalTateGalois
import Dubon2026.SourcePolynomialCommutant

/-! DUB-17/18 -> primitive Frobenius determinant -> the same original
arithmetic action preserves the primitive projector image. Original prime
commutation, native scalar extension and the literal projector polynomial
discharge this invariance without a new representation. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Polynomial TensorProduct
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
local notation "Qbar" => AlgebraicClosure ℚ
variable {E : Type*} [Field E] [Algebra ℚ_[p] E]
private local instance (q : Nat.Primes) : NeZero q.val := ⟨q.property.ne_zero⟩

theorem originalCuspCoefficientTateHecke_galois_commute {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (σ : Qbar ≃ₐ[ℚ] Qbar) (q : Nat.Primes) :
    Commute ((originalRationalTateGaloisRep N p σ).baseChange E)
      (originalCuspCoefficientTateHecke N p b P₀ lb
        (primitiveIntegralHeckeIndex N ⟨q.val, q.property.pos⟩)) := by
  rw [originalCuspCoefficientTateHecke_prime]
  exact (originalRationalTateGaloisRep_prime_commute N p σ q).map
    (Module.End.baseChangeHom ℚ_[p] E (originalRationalTateModule N p))

theorem primitiveOriginalTateEvaluation_galois_commute {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (σ : Qbar ≃ₐ[ℚ] Qbar)
    (s : Finset {q : Nat.Primes // q.val.Coprime N})
    (P : (sourcePrimitiveCoefficientField f)[X]) :
    Commute ((originalRationalTateGaloisRep N p σ).baseChange E)
      (primitiveOriginalTateEvaluation N p b P₀ lb f τ
        (primitiveGoodTensorProjector N f s P)) := by
  rw [primitiveOriginalTateEvaluation_projector]
  apply commute_aeval_of_commute
  rw [primitiveOriginalTateEvaluation_annihilator]
  exact commute_shifted_squares _ s _ _ fun q _ =>
    originalCuspCoefficientTateHecke_galois_commute N p b P₀ lb σ q.val

end
end Dubon2026.SourceFunctionField.OriginalChart
