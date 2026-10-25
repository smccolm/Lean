import Dubon2026.SourceOriginalCuspRationalTateHecke
import Dubon2026.SourcePrimitiveTensorOperators
import Dubon2026.SourceIntegerCoefficientEndExtension

/-! DUB-17/18 -> primitive determinant -> evaluate the same arithmetic
primitive idempotent on the original coefficient-extended Tate module.
Pure Hecke tensors and polynomial evaluation retain their exact values. -/
namespace Dubon2026.SourceFunctionField.OriginalChart
noncomputable section
open SourceCurve KaehlerDifferential Polynomial TensorProduct
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
local notation "V" => regularDifferentials ℂ (modularFunctionFieldOver N ℂ)
variable {E : Type*} [Field E] [Algebra ℚ_[p] E]
local notation "VE" => E ⊗[ℚ_[p]] originalRationalTateModule N p
private local instance (ell : Nat.Primes) : NeZero ell.val := ⟨ell.property.ne_zero⟩

/-- The integral cusp Hecke action on the original Tate module over the coefficient field. -/
def originalCuspCoefficientTateHecke {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val))) :
    sourceOriginalIntegralHeckeAlgebra N 2 →+*
    Module.End E VE :=
  (Module.End.baseChangeHom ℚ_[p] E (originalRationalTateModule N p)).toRingHom.comp
    (originalCuspRationalTateHecke N p b P₀ lb)

/-- Evaluation of the literal arithmetic tensor algebra on the original Tate module. -/
def primitiveOriginalTateEvaluation {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E) :
    sourcePrimitiveCoefficientField f ⊗[ℤ] sourceOriginalIntegralHeckeAlgebra N 2 →+*
      Module.End E VE :=
  integerCoefficientEndExtension τ (originalCuspCoefficientTateHecke N p b P₀ lb (E := E))

theorem originalCuspCoefficientTateHecke_prime {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (ell : Nat.Primes) :
    originalCuspCoefficientTateHecke N p b P₀ lb (E := E)
      (primitiveIntegralHeckeIndex N ⟨ell.val, ell.property.pos⟩) =
      ((TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val)).baseChange
        ℚ_[p]).baseChange E := by
  have h : primitiveIntegralHeckeIndex N ⟨ell.val, ell.property.pos⟩ =
      sourceIntegralCuspHeckeWord N (FreeAlgebra.ι ℤ ell) :=
    Subtype.ext (sourceIntegralCuspHeckeWord_prime N ell).symm
  change ((originalCuspRationalTateHecke N p b P₀ lb
    (primitiveIntegralHeckeIndex N ⟨ell.val, ell.property.pos⟩)).baseChange E) = _
  rw [h, originalCuspRationalTateHecke_prime]

theorem primitiveOriginalTateEvaluation_hecke {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (ell : Nat.Primes) :
    primitiveOriginalTateEvaluation N p b P₀ lb f τ
      ((1 : sourcePrimitiveCoefficientField f) ⊗ₜ[ℤ]
        primitiveIntegralHeckeIndex N ⟨ell.val, ell.property.pos⟩) =
      ((TateModule.tateMap p (originalHeckePicard (AlgebraicClosure ℚ) N ell.val)).baseChange
        ℚ_[p]).baseChange E := by
  dsimp only [primitiveOriginalTateEvaluation]
  exact (integerCoefficientEndExtension_one_tmul τ
    (originalCuspCoefficientTateHecke N p b P₀ lb (E := E))
    (primitiveIntegralHeckeIndex N ⟨ell.val, ell.property.pos⟩)).trans
      (originalCuspCoefficientTateHecke_prime N p b P₀ lb (E := E) ell)

theorem primitiveOriginalTateEvaluation_annihilator {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) :
    primitiveOriginalTateEvaluation N p b P₀ lb f τ (primitiveGoodTensorAnnihilator N f s) =
      ∑ q ∈ s, (originalCuspCoefficientTateHecke N p b P₀ lb (E := E)
        (primitiveIntegralHeckeIndex N ⟨q.val.val, q.val.property.pos⟩) -
        τ (sourcePrimitiveFieldCoefficient f q.val.val) • 1) ^ 2 := by
  dsimp only [primitiveOriginalTateEvaluation, primitiveGoodTensorAnnihilator]
  exact integerCoefficientEndExtension_shifted_squares τ
    (originalCuspCoefficientTateHecke N p b P₀ lb (E := E)) s
    (fun q => primitiveIntegralHeckeIndex N ⟨q.val.val, q.val.property.pos⟩)
    (fun q => sourcePrimitiveFieldCoefficient f q.val.val)

theorem primitiveOriginalTateEvaluation_projector {n m : ℕ}
    (b : Module.Basis (Fin n) ℂ V) (P₀ : Place ℂ (modularFunctionFieldOver N ℂ))
    (lb : Module.Basis (Fin m) ℤ (pathPeriodLattice N (fun i => (b i).val)))
    (f : PrimitiveCuspForm N 2) (τ : sourcePrimitiveCoefficientField f →+* E)
    (s : Finset {q : Nat.Primes // q.val.Coprime N}) (P : (sourcePrimitiveCoefficientField f)[X]) :
    primitiveOriginalTateEvaluation N p b P₀ lb f τ (primitiveGoodTensorProjector N f s P) =
      aeval (primitiveOriginalTateEvaluation N p b P₀ lb f τ
        (primitiveGoodTensorAnnihilator N f s)) (P.map τ) := by
  dsimp only [primitiveOriginalTateEvaluation, primitiveGoodTensorProjector]
  exact integerCoefficientEndExtension_aeval τ
    (originalCuspCoefficientTateHecke N p b P₀ lb (E := E))
    (primitiveGoodTensorAnnihilator N f s) P

end
end Dubon2026.SourceFunctionField.OriginalChart
