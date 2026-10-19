import Dubon2026.UnramifiedUnionFiniteFieldCriterion
import Dubon2026.FiniteGaloisEmbeddingStage

/-! Transport of the original primewise support condition across an actual
number-field equivalence. This lets the finite faithful quotient field be
placed in the original ambient algebraic closure without replacing its
ramification condition by an independently supplied certificate. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField

/-- The original primewise ramification condition is preserved by a
number-field equivalence, using the induced equivalence of integer rings. -/
theorem originalSupport_ramification_transport
    {K F L : Type*} [Field K] [Field F] [Field L] [NumberField K]
    [Algebra K F] [Algebra K L] (e : F ≃ₐ[K] L) (a : 𝓞 K)
    (hF : ∀ w : HeightOneSpectrum (𝓞 F),
      algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1)
    (w : HeightOneSpectrum (𝓞 L))
    (hw : algebraMap (𝓞 K) (𝓞 L) a ∉ w.asIdeal) :
    (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1 := by
  let E := NumberField.RingOfIntegers.mapAlgEquiv e
  let v := HeightOneSpectrum.comap E.toRingHom E.surjective w
  have hv : algebraMap (𝓞 K) (𝓞 F) a ∉ v.asIdeal := by
    change E (algebraMap (𝓞 K) (𝓞 F) a) ∉ w.asIdeal
    simpa only [E.commutes] using hw
  have hbase : v.asIdeal.under (𝓞 K) = w.asIdeal.under (𝓞 K) := by
    ext x
    change E (algebraMap (𝓞 K) (𝓞 F) x) ∈ w.asIdeal ↔
      algebraMap (𝓞 K) (𝓞 L) x ∈ w.asIdeal
    rw [E.commutes]
  have h := hF v hv
  rw [hbase] at h
  exact ((w.asIdeal.under (𝓞 K)).ramificationIdx_comap_eq E w.asIdeal).symm.trans h

/-- A finite Galois field satisfying the original support condition
embeds in the original union with its displayed ambient values. -/
theorem originalSupport_exists_embedding
    {K F Ω : Type} [Field K] [Field F] [Field Ω] [NumberField K]
    [Algebra K F] [Algebra K Ω] [FiniteDimensional K F] [IsGalois K F]
    (j : F →ₐ[K] Ω) (a : 𝓞 K)
    (hF : ∀ w : HeightOneSpectrum (𝓞 F),
      algebraMap (𝓞 K) (𝓞 F) a ∉ w.asIdeal →
      (w.asIdeal.under (𝓞 K)).ramificationIdx w.asIdeal = 1) :
    ∃ i : F →ₐ[K] originalUnramifiedGaloisUnion (Ω := Ω) a,
      ∀ x : F, (i x : Ω) = j x := by
  let E := finiteGaloisEmbeddingStage j
  let e : F ≃ₐ[K] E := finiteGaloisEmbeddingStageEquiv j
  have hE := originalSupport_ramification_transport e a hF
  have hle : E.toIntermediateField ≤ originalUnramifiedGaloisUnion (Ω := Ω) a :=
    originalUnramifiedGaloisStage_le_union a ⟨E, hE⟩
  let i := (IntermediateField.inclusion hle).comp e.toAlgHom
  exact ⟨i, fun _ => rfl⟩

end
end Dubon2026
