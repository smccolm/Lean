import Dubon2026.ArithmeticOrbitPrimeInvariantSum

/-! # The completion invariant at each genuine original prime

Choose the rational prime through the existing integral-prime equivalence,
then use the proved exact local-orbit equivalence. The completion is the
literal indexed original prime. This supplies the single-prime function
whose finite total is needed on DUB-17's number-field reciprocity route.
-/
namespace Dubon2026
noncomputable section
open scoped NumberField
attribute [local instance] arithmeticOrbitLocalUnionAlgebra arithmeticOrbitNormalSubfieldAlgebra
  arithmeticOrbitCompletionNumberField arithmeticOrbitUpperGalois

variable (a : 𝓞 ℚ)
  (F : IntermediateField ℚ (rationalUnramifiedExtension a)) [FiniteDimensional ℚ F]

/-- The rational prime below the genuine original prime, using the existing integral-prime equivalence. -/
def rationalArithmeticOriginalPrimeBase
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : Nat.Primes :=
  Rat.HeightOneSpectrum.primesEquiv (originalIntegerPrimeBelow F w)

/-- The chosen rational prime has exactly the original contracted integral prime. -/
theorem rationalArithmeticOriginalPrimeBase_below
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
    originalIntegerPrimeBelow F w = rationalPrimePlace
      (rationalArithmeticOriginalPrimeBase a F w).val
      (rationalArithmeticOriginalPrimeBase a F w).property :=
  (Rat.HeightOneSpectrum.primesEquiv.symm_apply_apply (originalIntegerPrimeBelow F w)).symm

/-- The canonical rational-prime index agrees with any given genuine prime fiber. -/
theorem rationalArithmeticOriginalPrimeBase_eq
    (p : Nat.Primes) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hw : originalIntegerPrimeBelow F w = rationalPrimePlace p.val p.property) :
    rationalArithmeticOriginalPrimeBase a F w = p :=
  (congrArg Rat.HeightOneSpectrum.primesEquiv hw).trans
    (Rat.HeightOneSpectrum.primesEquiv.apply_symm_apply p)

variable [TopologicalSpace (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a))]

/-- The actual completion-localized invariant at the indexed original prime. -/
def rationalArithmeticOriginalPrimeInvariant
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : AddCircle (1 : ℚ) :=
  let p := rationalArithmeticOriginalPrimeBase a F w
  rationalArithmeticOrbitCompletionUnitInvariant a p.val p.property F
    ((rationalArithmeticOrbitPrimeEquiv a p.val p.property F).symm
      ⟨w, rationalArithmeticOriginalPrimeBase_below a F w⟩).out y

/-- On each rational-prime fiber the indexed invariant is precisely its original Mackey completion summand. -/
theorem rationalArithmeticOriginalPrimeInvariant_fiber
    (y : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits F (rationalUnramifiedExtension a)))
    (p : Nat.Primes) (w : IsDedekindDomain.HeightOneSpectrum (𝓞 F))
    (hw : originalIntegerPrimeBelow F w = rationalPrimePlace p.val p.property) :
    rationalArithmeticOriginalPrimeInvariant a F y w =
      rationalArithmeticOrbitCompletionUnitInvariant a p.val p.property F
        ((rationalArithmeticOrbitPrimeEquiv a p.val p.property F).symm ⟨w, hw⟩).out y := by
  have hp := rationalArithmeticOriginalPrimeBase_eq a F p w hw
  subst p
  rfl

end
end Dubon2026
