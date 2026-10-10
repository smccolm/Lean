import Dubon2026.UnramifiedUnionFiniteRamification

/-! # Exact original finite-field containment in the constructed unramified union -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain
open scoped NumberField

variable {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [NumberField K]

/-- Every original finite ambient intermediate field contained in the actual unramified union satisfies the original primewise unramifiedness condition. Its containment in an original finite stage is derived. -/
theorem originalUnramifiedUnion_ambient_finite_ramification
    (a : 𝓞 K) (ha : a ≠ 0) (E : IntermediateField K Ω)
    [FiniteDimensional K E] [NumberField E]
    (hE : E ≤ originalUnramifiedGaloisUnion (Ω := Ω) a)
    (w : HeightOneSpectrum (𝓞 E)) (hw : algebraMap (𝓞 K) (𝓞 E) a ∉ w.asIdeal) :
    (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  letI := originalUnramifiedGaloisStage_nonempty (Ω := Ω) a
  obtain ⟨F, hF⟩ := finiteIntermediateField_le_directed_stage
    (fun F : OriginalUnramifiedGaloisStage (Ω := Ω) a => F.val.toIntermediateField)
    (originalUnramifiedGaloisStages_directed a ha) E hE
  let N := F.val
  let i := IntermediateField.inclusion hF
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

/-- An original finite Galois intermediate field belongs to the actual arithmetic union exactly when its original finite primes satisfy the original unramifiedness condition outside the exceptional integer. -/
theorem originalUnramifiedUnion_finiteGalois_le_iff
    (a : 𝓞 K) (ha : a ≠ 0) (F : FiniteGaloisIntermediateField K Ω) :
    F.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a ↔
      ∀ w : HeightOneSpectrum (𝓞 F), algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal →
        (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  constructor
  · intro hF w hw
    exact originalUnramifiedUnion_ambient_finite_ramification a ha F.toIntermediateField hF w hw
  · intro hF
    exact originalUnramifiedGaloisStage_le_union a ⟨F, hF⟩

end
end Dubon2026
