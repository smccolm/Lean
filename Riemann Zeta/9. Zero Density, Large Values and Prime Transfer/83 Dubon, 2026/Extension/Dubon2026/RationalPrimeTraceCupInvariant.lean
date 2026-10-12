import Dubon2026.RationalPrimeCyclotomicH2Scalar
import Dubon2026.ArithmeticCyclotomicCupRestriction

/-! # The actual scalar-valued arithmetic trace cup

Compose the original prime-local trace cup with its constructed cyclotomic H2
invariant. Its values detect the original H2 class and agree with restriction of
the global arithmetic cup. Nondegeneracy is not assumed or claimed here.
-/

namespace Dubon2026
noncomputable section
open Matrix
open scoped NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (p : ℕ) (hp : p.Prime) (q : ℕ) [Fact q.Prime]
  [TopologicalSpace (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [DiscreteTopology (galoisRootOfUnityRepresentation
    (K := rationalPrimeLocalField p hp) (Ω := rationalPrimeLocalClosure p hp) q)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits
    (rationalPrimeLocalField p hp) (rationalPrimeLocalClosure p hp))]
  (ρ : (rationalPrimeLocalClosure p hp ≃ₐ[rationalPrimeLocalField p hp]
    rationalPrimeLocalClosure p hp) →* GeneralLinearGroup ι (ZMod q)) (hρ : Continuous ρ)

/-- The actual prime-local deformation trace cup with values in the original
coefficient prime field, using the constructed invariant and no duality input. -/
def rationalPrimeTraceH1ScalarCup :
    ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ρ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous ρ hρ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous) →ₗ[ZMod q]
      ContinuousTraceZeroAdjointH1 ρ hρ →ₗ[ZMod q] ZMod q :=
  (matrixTraceZeroCharacterH1Cup ρ hρ
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
    (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous).compr₂
      (rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q).toLinearMap

/-- A scalar trace cup vanishes exactly when the actual original H2 cup class
vanishes. No information is lost in passing to the scalar invariant. -/
theorem rationalPrimeTraceH1ScalarCup_eq_zero_iff
    (x : ContinuousRepresentationH1
      (matrixTraceZeroCharacterRep ρ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous ρ hρ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous))
    (y : ContinuousTraceZeroAdjointH1 ρ hρ) :
    rationalPrimeTraceH1ScalarCup p hp q ρ hρ x y = 0 ↔
      matrixTraceZeroCharacterH1Cup ρ hρ
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).toMonoidHom
        (rationalPrimeCyclotomicCoefficientCharacter p hp q (ZMod q)).continuous x y = 0 := by
  exact (rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q).map_eq_zero_iff

omit ρ hρ in
/-- Restricting the original global arithmetic cup and taking its actual local
invariant agrees with the scalar cup of the original restricted H1 classes. -/
theorem rationalArithmeticTraceH1ScalarCup_prime_restriction
    (a : 𝓞 ℚ) (hqa : (q : 𝓞 ℚ) ∣ a)
    (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q))
    (hσ : Continuous σ)
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    let j := rationalPrimeArithmeticRestriction a p hp
    rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q
      (rationalPrimeCyclotomicH2Restriction a q hqa p hp
        (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y)) =
      rationalPrimeTraceH1ScalarCup p hp q (σ.comp j.toMonoidHom)
        (hσ.comp j.continuous)
        (rationalPrimeCyclotomicAdjointH1Restriction a q hqa p hp σ hσ x)
        (continuousTraceZeroH1Restriction σ hσ j.toMonoidHom j.continuous y) := by
  exact congrArg (rationalPrimeCyclotomicH2ScalarLinearEquiv p hp q)
    (rationalArithmeticTraceZeroH1Cup_prime_restriction a q hqa σ hσ p hp x y)

end
end Dubon2026
