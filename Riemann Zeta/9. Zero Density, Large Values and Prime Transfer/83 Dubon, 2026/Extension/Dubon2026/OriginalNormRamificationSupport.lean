import Dubon2026.OriginalIdelePowerLocalNormContainment
import Dubon2026.OriginalFiniteRamification

/-! # A constructed finite support discharges the unramified norm condition

Contract the already proved finite set of absolutely ramified upper
primes and adjoin it to any prescribed base support. Every upper prime
outside it is unramified. Thus DUB-17's degree-power/local-unit norm
containment retains only the actual selected-prime splitting input;
no unramified-support existence assumption remains.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField Classical
variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- The actual finite base support obtained by contracting the absolutely ramified upper primes. -/
def originalNormRamificationSupport : Finset (HeightOneSpectrum (𝓞 K)) :=
  (original_finite_absolutely_ramified_places L).toFinset.image (originalFinitePrimeBelow K L)

omit [NumberField K] in
/-- Every actual upper prime outside the constructed original base support is absolutely unramified. -/
theorem originalNormRamificationSupport_unramified (w : HeightOneSpectrum (𝓞 L))
    (hw : originalFinitePrimeBelow K L w ∉ originalNormRamificationSupport K L) :
    Algebra.IsUnramifiedAt ℤ w.asIdeal := by
  by_contra h
  apply hw
  exact Finset.mem_image.mpr ⟨w, (Set.Finite.mem_toFinset _).mpr h, rfl⟩

variable [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup

attribute [-instance] UniformSpace.Completion.instSMul in
/-- Enlarging any prescribed support by the constructed ramification support gives original class norm containment for every actual split prime set. -/
theorem originalIdeleClassPowerLocalUnitSubgroup_le_norm_enlarged
    (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ w : HeightOneSpectrum (𝓞 L), originalFinitePrimeBelow K L w ∈ T →
      OriginalFiniteDecompositionGroup K L w = ⊥) :
    originalIdeleClassPowerLocalUnitSubgroup K (Module.finrank K L)
      (S ∪ originalNormRamificationSupport K L) T ≤ (originalIdeleClassNorm K L).range := by
  apply originalIdeleClassPowerLocalUnitSubgroup_le_norm K L _ T hT
  intro w hw
  apply originalNormRamificationSupport_unramified K L w
  intro h
  exact hw (Finset.mem_union_left T (Finset.mem_union_right S h))

end
end Dubon2026
