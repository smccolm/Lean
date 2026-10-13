import Dubon2026.OriginalSupportedClassPowerMap
import Mathlib.GroupTheory.Index

/-! # The exact original principal S-unit / supported-idele / class power sequence

The actual kernel consists precisely of original principal S-unit classes.
The resulting cardinal product is the exact source identity needed for
DUB-17's prime-degree norm-index upper bound. Numerical local indices and
the selected-prime localization of the S-unit kernel remain to be proved.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
attribute [local instance 1100] AddCommGroup.toAddCommMonoid Rep.hV2
variable (K : Type) [Field K] [NumberField K]
  (n : ℕ) (S T : Finset (HeightOneSpectrum (𝓞 K)))

/-- The kernel of the actual class power quotient map is exactly the original principal S-unit quotient image. -/
theorem originalSupportedClassPowerQuotientMap_ker :
    (originalSupportedClassPowerQuotientMap K n S T).ker = (originalSUnitPowerLocalQuotientMap K n S T).range := by
  ext q
  induction q using QuotientGroup.induction_on
  rename_i a
  constructor
  · intro ha
    have ha' : originalSupportedClassPowerMap K n S T a = 1 := ha
    obtain ⟨b, hb, hclass⟩ := (originalSupportedClassPowerMap_eq_one_iff K n S T a).mp ha'
    let B : numberFieldSupportedIdeles K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) :=
      ⟨b, originalIdelePowerLocalUnitSubgroup_le_supported K n S T hb⟩
    let c := numberFieldSupportedIdeleClassMap K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))
    have hB : c B = c a := hclass
    have hker : a * B⁻¹ ∈ c.ker := by
      change c (a * B⁻¹) = 1
      rw [map_mul, map_inv, hB, mul_inv_cancel]
    rw [show c.ker = (numberFieldSupportedPrincipalIdele K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))).range from numberFieldSupportedIdeleClassMap_ker K _] at hker
    obtain ⟨x, hx⟩ := hker
    refine ⟨QuotientGroup.mk' (originalSUnitPowerLocalSubgroup K n S T) x, ?_⟩
    rw [originalSUnitPowerLocalQuotientMap_mk, hx, map_mul, map_inv]
    have hqB : QuotientGroup.mk' (originalSupportedPowerLocalUnitSubgroup K n S T) B = 1 :=
      (QuotientGroup.eq_one_iff B).mpr hb
    rw [hqB, inv_one]
    exact mul_one (QuotientGroup.mk' (originalSupportedPowerLocalUnitSubgroup K n S T) a)
  · rintro ⟨r, hr⟩
    rw [← hr]
    induction r using QuotientGroup.induction_on
    rename_i x
    change originalSupportedClassPowerMap K n S T
      (numberFieldSupportedPrincipalIdele K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) x) = 1
    apply (originalSupportedClassPowerMap_eq_one_iff K n S T _).mpr
    have hx : numberFieldSupportedIdeleClassMap K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K)))
        (numberFieldSupportedPrincipalIdele K (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))) x) = 1 := by
      apply (QuotientGroup.eq_one_iff _).mpr
      exact ⟨x.val, rfl⟩
    rw [hx]
    exact (originalIdeleClassPowerLocalUnitSubgroup K n S T).one_mem

/-- The original S-unit power quotient times the original class power quotient has exactly the original supported-idele quotient cardinal. -/
theorem originalSUnitPowerLocalQuotient_card_mul_class
    (hS : Function.Surjective (numberFieldSupportedIdeleClassMap K
      (↑(S ∪ T) : Set (HeightOneSpectrum (𝓞 K))))) :
    Nat.card (OriginalSUnitPowerLocalQuotient K n S T) *
        Nat.card (OriginalIdeleClassPowerLocalUnitQuotient K n S T) =
      Nat.card (OriginalSupportedPowerLocalUnitQuotient K n S T) := by
  let f := originalSupportedClassPowerQuotientMap K n S T
  have h := f.ker.card_mul_index
  rw [Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f
      (originalSupportedClassPowerQuotientMap_surjective K n S T hS)).toEquiv] at h
  rw [show f.ker = (originalSUnitPowerLocalQuotientMap K n S T).range from
    originalSupportedClassPowerQuotientMap_ker K n S T] at h
  rw [← Nat.card_congr (MonoidHom.ofInjective (originalSUnitPowerLocalQuotientMap_injective K n S T)).toEquiv] at h
  exact h

end
end Dubon2026
