import Dubon2026.OriginalPrincipalPowerExactSequence
import Dubon2026.OriginalFinitePowerQuotientFinite
import Dubon2026.OriginalInfinitePowerIndex

/-! # Finiteness of the actual original power quotients and unconditional cardinal comparison

The proved original local quotient finiteness and exact local-product
equivalence make the supported quotient finite. Its actual principal
S-unit subquotient and class quotient are therefore finite as well.
This removes the finite-power-quotient hypothesis from DUB-17's norm
cardinal comparison, retaining only the actual split-prime and
class-surjective support inputs that the later construction must supply.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K : Type) [Field K] [NumberField K]

/-- The actual original supported local-power quotient is finite for every positive exponent and finite support. -/
theorem originalSupportedPowerLocalUnitQuotient_finite (n : ℕ) (hn : 0 < n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite (OriginalSupportedPowerLocalUnitQuotient K n S T) := by
  haveI (w : InfinitePlace K) : Finite (w.Completionˣ ⧸
      (powMonoidHom n : w.Completionˣ →* w.Completionˣ).range) := originalInfinitePowerQuotient_finite K w n hn
  haveI (v : S) : Finite ((v.val.adicCompletion K)ˣ ⧸
      (powMonoidHom n : (v.val.adicCompletion K)ˣ →* (v.val.adicCompletion K)ˣ).range) :=
    originalFinitePowerQuotient_finite K v.val n hn
  exact Finite.of_equiv (OriginalSupportedLocalPowerClasses K n S)
    (originalSupportedPowerLocalUnitQuotientEquiv K n S T).symm.toEquiv

/-- The original principal S-unit local-power quotient is finite by its proved injection into the actual supported quotient. -/
theorem originalSUnitPowerLocalQuotient_finite (n : ℕ) (hn : 0 < n)
    (S T : Finset (HeightOneSpectrum (𝓞 K))) :
    Finite (OriginalSUnitPowerLocalQuotient K n S T) := by
  haveI := originalSupportedPowerLocalUnitQuotient_finite K n hn S T
  exact Finite.of_injective _ (originalSUnitPowerLocalQuotientMap_injective K n S T)

/-- Actual class-surjectivity of the support makes the original class power/local-unit quotient finite. -/
theorem originalIdeleClassPowerLocalUnitQuotient_finite (n : ℕ) (hn : 0 < n)
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hS : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) :
    Finite (OriginalIdeleClassPowerLocalUnitQuotient K n S T) := by
  haveI := originalSupportedPowerLocalUnitQuotient_finite K n hn S T
  exact Finite.of_surjective _ (originalSupportedClassPowerQuotientMap_surjective K n S T hS)

variable (L : Type) [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual norm quotient is bounded by the actual degree-power class quotient with its finiteness proved, retaining explicit structural support and splitting inputs only. -/
theorem originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient_of_support
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
      OriginalFiniteDecompositionGroup K L w = ⊥)
    (hS : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑((S ∪ originalNormRamificationSupport K L) ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) :
    Nat.card (OriginalIdeleClassNormQuotient K L) ≤
      Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K (Module.finrank K L)
        (S ∪ originalNormRamificationSupport K L) T) := by
  haveI := originalIdeleClassPowerLocalUnitQuotient_finite K (Module.finrank K L)
    Module.finrank_pos (S ∪ originalNormRamificationSupport K L) T hS
  exact originalIdeleClassNormQuotient_card_le_powerLocalUnitQuotient K L S T hT

end
end Dubon2026
