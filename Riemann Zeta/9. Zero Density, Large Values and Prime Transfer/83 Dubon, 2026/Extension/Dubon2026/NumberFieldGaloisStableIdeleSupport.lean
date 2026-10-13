import Dubon2026.NumberFieldSUnitGaloisAction
import Dubon2026.NumberFieldSupportedIdeleSurjection

/-! # One original finite support is both Galois-stable and large enough

The actual supported-idele map remains onto when support is enlarged.
Combining its constructed finite support with finite original Galois
orbits gives a single finite stable support. These conditions are derived
for the original objects, discharging the support hypotheses needed by
DUB-17's equivariant supported-idele and norm-index calculation.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain
open scoped NumberField

/-- Enlarging the original support enlarges its original supported-idele subgroup. -/
theorem numberFieldSupportedIdeles_mono (L : Type) [Field L] [NumberField L]
    {S T : Set (HeightOneSpectrum (𝓞 L))} (h : S ⊆ T) :
    numberFieldSupportedIdeles L S ≤ numberFieldSupportedIdeles L T := by
  intro a ha
  simp only [numberFieldSupportedIdeles, Subgroup.mem_iInf, Subgroup.mem_comap] at ha ⊢
  exact fun v hv => ha v (fun hs => hv (h hs))

/-- Onto original global classes stays onto after an actual support enlargement. -/
theorem numberFieldSupportedIdeleClassMap_surjective_mono
    (L : Type) [Field L] [NumberField L]
    {S T : Set (HeightOneSpectrum (𝓞 L))} (h : S ⊆ T)
    (hS : Function.Surjective (numberFieldSupportedIdeleClassMap L S)) :
    Function.Surjective (numberFieldSupportedIdeleClassMap L T) := by
  intro c
  obtain ⟨a, ha⟩ := hS c
  exact ⟨⟨a.val, numberFieldSupportedIdeles_mono L h a.property⟩, ha⟩

/-- A constructed finite enlargement is simultaneously Galois-stable and onto the original global idele classes. -/
theorem numberField_exists_galoisStable_idele_support
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (S₀ : Finset (HeightOneSpectrum (𝓞 L))) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 L)), S₀ ⊆ S ∧
      (∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S) ∧
      Function.Surjective (numberFieldSupportedIdeleClassMap L S) := by
  obtain ⟨T, hT, hf⟩ := numberField_exists_supportedIdeleClassMap_surjective L S₀
  obtain ⟨S, hTS, hS⟩ := numberField_exists_finite_galoisStable_support K L T
  exact ⟨S, hT.trans hTS, hS, numberFieldSupportedIdeleClassMap_surjective_mono L hTS hf⟩

end
end Dubon2026
