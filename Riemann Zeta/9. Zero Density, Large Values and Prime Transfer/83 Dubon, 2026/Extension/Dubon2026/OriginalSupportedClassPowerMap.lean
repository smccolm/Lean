import Dubon2026.OriginalPowerLocalUnitNormQuotient
import Dubon2026.OriginalSUnitPowerLocalQuotient

/-! # The actual class map out of the original supported local-power quotient

The original supported-idele class map followed by the original class
power quotient kills precisely the specified local conditions needed to
descend. This is the right-hand map of DUB-17's principal S-unit cardinal
sequence. Surjectivity follows from the already constructed class-surjective
support, retained explicitly here as the genuine narrower support input.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))

/-- The original supported-idele class map followed by the actual additive class power quotient. -/
def originalSupportedClassPowerMap :
    numberFieldSupportedIdeles K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) →*
      Multiplicative (OriginalIdeleClassPowerLocalUnitQuotient K n S T) :=
  (originalIdeleClassPowerLocalUnitSubmodule K n S T).mkQ.toAddMonoidHom.toMultiplicative.comp
    (numberFieldSupportedIdeleClassMap K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))).toAdditive.toMultiplicative

/-- An actual supported idele maps to zero class precisely when its original class satisfies the actual source local-power image condition. -/
theorem originalSupportedClassPowerMap_eq_one_iff
    (a : numberFieldSupportedIdeles K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))) :
    originalSupportedClassPowerMap K n S T a = 1 ↔
      numberFieldSupportedIdeleClassMap K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) a ∈
        originalIdeleClassPowerLocalUnitSubgroup K n S T := by
  change (originalIdeleClassPowerLocalUnitSubmodule K n S T).mkQ
    (Additive.ofMul (numberFieldSupportedIdeleClassMap K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) a)) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl

/-- The actual source local conditions are killed by the actual supported class power map. -/
theorem originalSupportedPowerLocalUnitSubgroup_le_classPowerKer :
    originalSupportedPowerLocalUnitSubgroup K n S T ≤ (originalSupportedClassPowerMap K n S T).ker := by
  intro a ha
  apply (originalSupportedClassPowerMap_eq_one_iff K n S T a).mpr
  exact ⟨a.val, ha, rfl⟩

/-- The actual supported class power map descends to the original supported local-power quotient. -/
def originalSupportedClassPowerQuotientMap :
    OriginalSupportedPowerLocalUnitQuotient K n S T →*
      Multiplicative (OriginalIdeleClassPowerLocalUnitQuotient K n S T) :=
  QuotientGroup.lift _ (originalSupportedClassPowerMap K n S T)
    (originalSupportedPowerLocalUnitSubgroup_le_classPowerKer K n S T)

/-- The descended class map preserves the original supported idele representative. -/
theorem originalSupportedClassPowerQuotientMap_mk
    (a : numberFieldSupportedIdeles K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))) :
    originalSupportedClassPowerQuotientMap K n S T
      (QuotientGroup.mk' (originalSupportedPowerLocalUnitSubgroup K n S T) a) =
        originalSupportedClassPowerMap K n S T a := rfl

/-- Actual class-surjectivity of the support makes the original class power quotient map surjective. -/
theorem originalSupportedClassPowerQuotientMap_surjective
    (hS : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) :
    Function.Surjective (originalSupportedClassPowerQuotientMap K n S T) := by
  intro x
  obtain ⟨c, hc⟩ := (originalIdeleClassPowerLocalUnitSubmodule K n S T).mkQ_surjective x.toAdd
  obtain ⟨a, ha⟩ := hS c.toMul
  refine ⟨QuotientGroup.mk' (originalSupportedPowerLocalUnitSubgroup K n S T) a, ?_⟩
  apply Multiplicative.toAdd.injective
  change (originalIdeleClassPowerLocalUnitSubmodule K n S T).mkQ
    (Additive.ofMul (numberFieldSupportedIdeleClassMap K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) a)) = x.toAdd
  rw [ha]
  exact hc

end
end Dubon2026
