import Dubon2026.ArithmeticConjugateCocycleFrobenius
import Dubon2026.RationalPrimeSymmetricUnramifiedDimension

/-! Exact original-object interfaces for DUB-17/18's split regular
detecting primes and their local adjoint dimension. Every condition is
about the same original field, action, cocycle, finite factor and Frobenius. -/
namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField
attribute [local instance] rationalArithmeticOriginalFiniteGalois

/-- The original local Frobenius witness in one actual finite factor. -/
def OriginalTorusPrimeWitness
    (a : 𝓞 ℚ) (n : ℕ) {K : Type} [Field K] (u : Kˣ)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (n + 1)) K)
    (D : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (q : ℕ) (hq : q.Prime) : Prop :=
  letI : NumberField D := NumberField.of_module_finite ℚ D
  ∃ γ : Gal(rationalPrimeLocalClosure q hq / rationalPrimeLocalField q hq),
             Chebotarev.frobeniusClass ℚ D (Ideal.span {(q : 𝓞 ℚ)}) =
               ConjClasses.mk (AlgEquiv.restrictNormalHom D
                 (rationalPrimeArithmeticRestriction a q hq γ)) ∧
             IsConj (ρ (rationalPrimeArithmeticRestriction a q hq γ))
               (homogeneousSymmetricGL n (SpecialLinearGroup.toGL (ringSL2UnitDiagonal u))) ∧
             (ρ (rationalPrimeArithmeticRestriction a q hq γ)).val.charpoly.Separable

/-- Exact unramified adjoint dimension over the original finite field. -/
def OriginalPrimeAdjointDimension
    (a : 𝓞 ℚ) (n : ℕ) {K : Type} [Field K]
    [TopologicalSpace K] [IsTopologicalRing K]
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin (n + 1)) K)
    (hρ : Continuous ρ) (q : ℕ) (hq : q.Prime) : Prop :=
  let R := ρ.comp (rationalPrimeArithmeticRestriction a q hq).toMonoidHom
            let hR := hρ.comp (rationalPrimeArithmeticRestriction a q hq).continuous
            Module.finrank K (continuousRepresentationH1Restriction
              (matrixTraceZeroAdjointRep R) (matrixTraceZeroAdjointAction_continuous R hR)
              (rationalPrimeNormInertia q hq).subtype continuous_subtype_val).ker = n

end
end Dubon2026
