import Dubon2026.ArithmeticPrincipalCarryInvariant
import Dubon2026.ArithmeticCoherentTraceCup

/-! # Global orthogonality of the actual arithmetic trace cup

The proved odd-prime invariant product formula applies directly to the
global trace cup of two original arithmetic H1 classes.  This removes the
reciprocity premise from the orthogonality relation used by the subsequent
global-duality and Selmer construction.
-/
namespace Dubon2026
noncomputable section

open Matrix
open scoped BigOperators NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime] (hqa : (q : 𝓞 ℚ) ∣ a)
  (σ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup ι (ZMod q))
  (hσ : Continuous σ)
  [TopologicalSpace (rationalArithmeticRootRepresentation a q)]
  [DiscreteTopology (rationalArithmeticRootRepresentation a q)]
  [TopologicalSpace (rationalArithmeticUnitRepresentation a)]
  [DiscreteTopology (rationalArithmeticUnitRepresentation a)]

/-- The coherent finite-prime invariant sum of the actual global trace cup
vanishes at every odd coefficient prime. -/
theorem rationalArithmeticTraceZeroH1Cup_finiteInvariantSum_eq_zero
    (ha : a ≠ 0) (hq2 : q ≠ 2)
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    rationalArithmeticFiniteH2InvariantSum a q hqa ha
      (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y) = 0 :=
  rationalArithmeticFiniteH2InvariantSum_eq_zero a q hqa ha hq2
    (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y)

/-- Equivalently, the literal finite sum of coherent prime-local trace-cup
coordinates over its proved support is zero. -/
theorem rationalArithmeticTraceZeroH1Cup_primeInvariant_sum_eq_zero
    (ha : a ≠ 0) (hq2 : q ≠ 2)
    (x : ContinuousRepresentationH1 (matrixTraceZeroCharacterRep σ
      (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom)
      (matrixTraceZeroCharacterAction_continuous σ hσ
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).toMonoidHom
        (rationalArithmeticCyclotomicCoefficientCharacter a q hqa (ZMod q)).continuous))
    (y : ContinuousTraceZeroAdjointH1 σ hσ) :
    (∑ p ∈ (rationalArithmeticPrimeH2InvariantFamily a q hqa ha
        (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y)).support,
      rationalArithmeticPrimeH2Invariant a q hqa p.val p.property
        (rationalArithmeticTraceZeroH1Cup a q hqa σ hσ x y)) = 0 := by
  rw [← rationalArithmeticFiniteH2InvariantSum_apply]
  exact rationalArithmeticTraceZeroH1Cup_finiteInvariantSum_eq_zero
    a q hqa σ hσ ha hq2 x y

end
end Dubon2026
