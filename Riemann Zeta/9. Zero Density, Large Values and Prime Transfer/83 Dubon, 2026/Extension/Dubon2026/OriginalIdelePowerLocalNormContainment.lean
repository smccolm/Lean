import Dubon2026.OriginalIdelePowerLocalUnits
import Dubon2026.OriginalLocalNormSplitPrime
import Dubon2026.OriginalLocalNormUnramifiedUnits
import Dubon2026.OriginalIdeleNormLocalGlobal
import Dubon2026.OriginalIdeleClassNorm

/-! # The actual degree-power/local-unit subgroup lies in the original norm image

Powers have explicit actual local norm preimages; split places have
surjective local norms; outside the finite absolute ramification support,
original integer units are actual local norms. The proved original idele
assembly combines these and descends the containment to original classes.
For the prime-degree step the source power exponent is exactly the degree,
so no general abelian local-reciprocity input is needed. The selected-prime
quotient cardinal bound and coprime base change remain separate DUB-17 inputs.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The actual degree-power/local-unit subgroup lies in the original idele norm image, with the split and unramified place inputs explicit. -/
theorem originalIdelePowerLocalUnitSubgroup_le_norm
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
      OriginalFiniteDecompositionGroup K L w = ⊥)
    (hAway : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∪ T →
      Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    originalIdelePowerLocalUnitSubgroup K (Module.finrank K L) S T ≤ (originalIdeleNorm K L).range := by
  intro a ha
  obtain ⟨hInf, hS, hUnits⟩ := (originalIdelePowerLocalUnitSubgroup_mem_iff K _ S T a).mp ha
  apply originalIdeleNorm_exists_of_local K L a
  · intro w
    by_cases hs : originalFinitePrimeBelow K L w ∈ S
    · obtain ⟨u, hu⟩ := hS _ hs
      change u ^ Module.finrank K L = _ at hu
      rw [← hu]
      exact originalFiniteLocalNorm_degreePower K L w u
    · by_cases ht : originalFinitePrimeBelow K L w ∈ T
      · exact originalFiniteLocalNorm_surjective_of_split K L w (hT w ht) _
      · have hst : originalFinitePrimeBelow K L w ∉ S ∪ T := by
          simpa only [Finset.mem_union, not_or] using And.intro hs ht
        exact originalFiniteLocalNorm_integerUnit_of_unramified K L w (hAway w hst) _ (hUnits _ hst)
  · intro w
    obtain ⟨u, hu⟩ := hInf (w.comap (algebraMap K L))
    change u ^ Module.finrank K L = _ at hu
    rw [← hu]
    exact originalInfiniteLocalNorm_degreePower K L w u

attribute [-instance] UniformSpace.Completion.instSMul in
/-- The same actual local conditions descend to containment in the actual original idele-class norm image. -/
theorem originalIdeleClassPowerLocalUnitSubgroup_le_norm
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
      OriginalFiniteDecompositionGroup K L w = ⊥)
    (hAway : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∉ S ∪ T →
      Algebra.IsUnramifiedAt ℤ w.asIdeal) :
    originalIdeleClassPowerLocalUnitSubgroup K (Module.finrank K L) S T ≤ (originalIdeleClassNorm K L).range := by
  rintro c ⟨a, ha, rfl⟩
  obtain ⟨b, hb⟩ := originalIdelePowerLocalUnitSubgroup_le_norm K L S T hT hAway ha
  refine ⟨QuotientGroup.mk' (numberFieldPrincipalIdele L).range b, ?_⟩
  rw [originalIdeleClassNorm_mk, hb]

end
end Dubon2026
