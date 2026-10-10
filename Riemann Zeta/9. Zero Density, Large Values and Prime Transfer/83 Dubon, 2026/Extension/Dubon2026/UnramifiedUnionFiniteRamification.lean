import Dubon2026.UnramifiedUnionFiniteStage
import Dubon2026.HeightOnePrimeLifting
import Dubon2026.UnramifiedIdealTowers

/-! # Original finite-prime ramification in the actual constructed stage union -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Every original prime of an actual finite subextension of the constructed arithmetic union is unramified away from the original exceptional integer. -/
theorem originalUnramifiedUnion_finite_ramification
    (a : 𝓞 K) (ha : a ≠ 0)
    (E : IntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    [FiniteDimensional K E] [NumberField E]
    (w : HeightOneSpectrum (𝓞 E)) (hw : algebraMap (𝓞 K) (𝓞 E) a ∉ w.asIdeal) :
    (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  obtain ⟨F, i, _⟩ := originalUnramifiedUnion_finite_subextension_embeds_stage a ha E
  let N := F.val
  letI : Algebra E N := i.toRingHom.toAlgebra
  letI : IsScalarTower K E N := IsScalarTower.of_algHom i
  obtain ⟨z, hz⟩ := heightOnePrime_exists_liesOver (S := 𝓞 N) w
  letI := hz
  have hza : algebraMap (𝓞 K) (𝓞 N) a ∉ z.asIdeal := by
    intro h
    apply hw
    apply (Ideal.mem_of_liesOver z.asIdeal w.asIdeal _).mpr
    simpa only [← IsScalarTower.algebraMap_apply] using h
  letI : w.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)) := inferInstance
  letI : z.asIdeal.LiesOver (w.asIdeal.under (𝓞 K)) :=
    Ideal.LiesOver.trans z.asIdeal w.asIdeal (w.asIdeal.under (𝓞 K))
  have htotal := F.property z hza
  rw [← Ideal.over_def z.asIdeal (w.asIdeal.under (𝓞 K))] at htotal
  exact (unramifiedIdealTower_indices (w.asIdeal.under (𝓞 K))
    w.asIdeal z.asIdeal htotal).1

/-- The constructed original arithmetic union satisfies the actual finite-Galois-subextension prime-lifting and index-one condition required by the original Kummer character argument. -/
theorem originalUnramifiedUnion_finiteGalois_unramified
    (a : 𝓞 K) (ha : a ≠ 0)
    (F : FiniteGaloisIntermediateField K (originalUnramifiedGaloisUnion (Ω := Ω) a))
    (v : HeightOneSpectrum (𝓞 K)) (hv : a ∉ v.asIdeal) :
    ∃ w : HeightOneSpectrum (𝓞 F), w.asIdeal.LiesOver v.asIdeal ∧
      v.asIdeal.ramificationIdx w.asIdeal = 1 := by
  obtain ⟨w, hw⟩ := heightOnePrime_exists_liesOver (S := 𝓞 F) v
  letI := hw
  have hwa : algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal := by
    intro h
    exact hv ((Ideal.mem_of_liesOver w.asIdeal v.asIdeal a).mpr h)
  have h := originalUnramifiedUnion_finite_ramification a ha F.toIntermediateField w hwa
  rw [← Ideal.over_def w.asIdeal v.asIdeal] at h
  exact ⟨w, hw, h⟩

end
end Dubon2026
