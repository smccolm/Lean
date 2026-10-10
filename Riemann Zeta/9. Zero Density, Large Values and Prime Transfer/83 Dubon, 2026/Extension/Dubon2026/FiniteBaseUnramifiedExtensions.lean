import Dubon2026.HeightOnePrimeLifting
import Dubon2026.UnramifiedGaloisPrimeTransfer
import Dubon2026.UnramifiedIdealTowers
import Dubon2026.UnramifiedGaloisCharacters

/-! # Actual unramified finite subextensions after a finite change of base field -/

namespace Dubon2026

open scoped NumberField

noncomputable section
open IsDedekindDomain IntermediateField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]
  [IsGalois K Ω]

/-- Genuine unramified finite Galois subextensions over the original base give the same property over every actual finite intermediate field, with the literal inverse image of the original exceptional prime set. -/
theorem finiteBase_unramified_finite_subextensions
    (S : Set (HeightOneSpectrum (𝓞 K)))
    (hunram : ∀ F : FiniteGaloisIntermediateField K Ω,
      ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
        ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
          v.asIdeal.ramificationIdx w.asIdeal = 1)
    (E : IntermediateField K Ω) [FiniteDimensional K E] [NumberField E]
    (F : FiniteGaloisIntermediateField E Ω)
    (v : HeightOneSpectrum (𝓞 E)) (hv : v.under (𝓞 K) ∉ S) :
    ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
      v.asIdeal.ramificationIdx w.asIdeal = 1 := by
  letI : IsScalarTower K F Ω := IsScalarTower.of_algebraMap_eq' rfl
  letI : FiniteDimensional K F := Module.Finite.trans E F
  let N : FiniteGaloisIntermediateField K Ω :=
    ⟨normalClosure K F Ω⟩
  letI : NumberField N := NumberField.of_module_finite K N
  letI : Algebra F N := normalClosure.algebra K F Ω
  letI : IsScalarTower K F N := inferInstanceAs
    (IsScalarTower K F (normalClosure K F Ω))
  letI : IsScalarTower F N Ω := inferInstanceAs
    (IsScalarTower F (normalClosure K F Ω) Ω)
  letI : Algebra E N := Algebra.compHom N (algebraMap E F)
  letI : IsScalarTower E F N := IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower K E N := IsScalarTower.of_algebraMap_eq' (by
    ext x
    rw [IsScalarTower.algebraMap_apply K F N, IsScalarTower.algebraMap_apply K E F]
    rfl)
  obtain ⟨w, hw⟩ := heightOnePrime_exists_liesOver (S := 𝓞 F) v
  letI := hw
  obtain ⟨z, hz⟩ := heightOnePrime_exists_liesOver (S := 𝓞 N) w
  letI := hz
  letI : z.asIdeal.LiesOver v.asIdeal := Ideal.LiesOver.trans z.asIdeal w.asIdeal v.asIdeal
  letI : v.asIdeal.LiesOver (v.under (𝓞 K)).asIdeal :=
    inferInstanceAs (v.asIdeal.LiesOver (v.asIdeal.under (𝓞 K)))
  letI : z.asIdeal.LiesOver (v.under (𝓞 K)).asIdeal :=
    Ideal.LiesOver.trans z.asIdeal v.asIdeal (v.under (𝓞 K)).asIdeal
  have htotal : (v.under (𝓞 K)).asIdeal.ramificationIdx z.asIdeal = 1 :=
    numberField_galois_unramified_at_every_prime (v.under (𝓞 K))
      (hunram N (v.under (𝓞 K)) hv) z
  have hEN : v.asIdeal.ramificationIdx z.asIdeal = 1 :=
    (unramifiedIdealTower_indices (v.under (𝓞 K)).asIdeal v.asIdeal z.asIdeal htotal).2
  exact ⟨w, hw, (unramifiedIdealTower_indices v.asIdeal w.asIdeal z.asIdeal hEN).1⟩

end
end Dubon2026
