import Dubon2026.FiniteBaseUnramifiedExtensions
import Dubon2026.FinitePrimeBaseChange
import Dubon2026.CyclotomicGaloisCharacterDescent

/-! # Actual unramified prime characters from roots in the original ambient extension -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]
  [IsGalois K Ω]

/-- An actual primitive root in the original ambient extension suffices for character finiteness: adjoin that same root, transfer actual unramifiedness to the finite cyclotomic base, and descend through its original coprime degree. -/
theorem unramified_prime_characters_finite_of_ambient_root
    (S : Set (HeightOneSpectrum (𝓞 K))) (hS : S.Finite)
    (hunram : ∀ F : FiniteGaloisIntermediateField K Ω,
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
          v.asIdeal.ramificationIdx w.asIdeal = 1)
    (p : ℕ) (hp : p.Prime) {ζ : Ω} (hζ : IsPrimitiveRoot ζ p) :
    Finite (Gal(Ω/K) →ₜ* Multiplicative (ZMod p)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let F := IntermediateField.adjoin K ({ζ} : Set Ω)
  letI : IsCyclotomicExtension {p} K F :=
    (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin p K Ω F hζ).mpr rfl
  letI : FiniteDimensional K F := IsCyclotomicExtension.finiteDimensional {p} K F
  letI : NumberField F := NumberField.of_module_finite K F
  letI : TopologicalSpace Fˣ := ⊥
  letI : DiscreteTopology Fˣ := ⟨rfl⟩
  let ζF : F := ⟨ζ, IntermediateField.subset_adjoin K _ (Set.mem_singleton ζ)⟩
  have hζF : IsPrimitiveRoot ζF p := IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ
  letI : Finite (Gal(Ω/F) →ₜ* Multiplicative (ZMod p)) :=
    unramified_continuous_prime_characters_finite
      {v : HeightOneSpectrum (𝓞 F) | v.under (𝓞 K) ∈ S}
      (heightOneUnder_preimage_finite S hS)
      (fun L v hv => finiteBase_unramified_finite_subextensions S hunram F L v hv)
      p hp hζF
  exact cyclotomic_continuous_prime_characters_finite p hp F

end
end Dubon2026
