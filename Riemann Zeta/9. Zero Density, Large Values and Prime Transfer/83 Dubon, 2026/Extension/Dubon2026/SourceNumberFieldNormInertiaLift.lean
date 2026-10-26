import Dubon2026.OriginalGeneratedLocalInertiaLift
import Dubon2026.EmbeddedFiniteGaloisCompositumMaps
import Dubon2026.RationalPrimeCyclotomicInertia
import Dubon2026.RationalOriginalPrimeCompletion
import Dubon2026.RationalArithmeticFrobeniusLift

/-! DUB-17/18 -> arithmetic quotient of the actual residual representation
-> unramified faithful finite field. Reuse the existing generated local
compositum and inertia-lifting theorem for any actual finite Galois number
field embedding, before containment in the arithmetic union is known. -/
namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField ValuativeRel NNReal
attribute [local instance] rationalPrimeLocalField_charZero
  rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField

theorem numberField_embedded_inertia_exists_norm_lift
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    (p : ℕ) (hp : p.Prime) (i : F →ₐ[ℚ] rationalPrimeLocalClosure p hp) :
    ∃ w : HeightOneSpectrum (𝓞 F),
      w.asIdeal.LiesOver (rationalOriginalPrimePlace p hp).asIdeal ∧
      ∀ σ : Gal(F/ℚ), σ ∈ w.asIdeal.inertia Gal(F/ℚ) →
        ∃ g, g ∈ rationalPrimeNormInertia p hp ∧
          ∀ x : F, g (i x) = i (σ x) := by
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let C := embeddedFiniteGaloisCompositum (K := K) i
  let E := C.toIntermediateField
  letI : Algebra ℚ E := (E.restrictScalars ℚ).algebra'
  letI : Field K := (inferInstance : NontriviallyNormedField K).toField
  letI : NormedField E := (inferInstance : NontriviallyNormedField E).toNormedField
  letI : Field E := (inferInstance : NormedField E).toField
  letI : NormedAlgebra K E := inferInstance
  letI : Algebra K E := (inferInstance : NormedAlgebra K E).toAlgebra
  letI : @IsGalois K (inferInstance : NontriviallyNormedField K).toField E
      (inferInstance : NormedField E).toField (inferInstance : NormedAlgebra K E).toAlgebra := C.isGalois
  letI : IsUltrametricDist E := IsUltrametricDist.of_normedAlgebra K
  haveI : ProperSpace E := FiniteDimensional.proper K E
  haveI : CompleteSpace E := inferInstance
  letI : NormedAlgebra E Ω := ⟨fun x y => by
    change ‖(x : Ω) * y‖ ≤ ‖(x : Ω)‖ * ‖y‖
    exact (norm_mul _ _).le⟩
  letI : ValuativeRel E := ValuativeRel.ofValuation (NormedField.valuation (K := E))
  letI : (NormedField.valuation (K := E)).Compatible := Valuation.Compatible.ofValuation _
  letI : (NormedField.valuation (K := K)).Compatible := localFieldOriginalNorm_compatible K
  letI : IsNonarchimedeanLocalField E := normValuation_isNonarchimedeanLocalField E
  letI : (ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E) := ⟨by
    intro x y
    rw [← (ValuativeRel.valuation K).vle_iff_le,
      (NormedField.valuation (K := K)).vle_iff_le]
    change _ ↔ ValuativeRel.valuation E (algebraMap K E x) ≤ ValuativeRel.valuation E (algebraMap K E y)
    rw [← (ValuativeRel.valuation E).vle_iff_le,
      (NormedField.valuation (K := E)).vle_iff_le]
    change ‖x‖₊ ≤ ‖y‖₊ ↔ ‖algebraMap K E x‖₊ ≤ ‖algebraMap K E y‖₊
    exact Iff.of_eq ((congrArg₂ (fun x y : ℝ≥0 => x ≤ y)
      (nnnorm_algebraMap' E x) (nnnorm_algebraMap' E y)).symm)⟩
  let j : F →ₐ[ℚ] E := embeddedFiniteGaloisCompositumInclusion (K := K) i
  letI : Algebra F E := j.toRingHom.toAlgebra
  let w := originalLocalEmbeddingPrime F E p hp
  have hgen : (algebraMap K E).fieldRange ⊔ (algebraMap F E).fieldRange = ⊤ :=
    embeddedFiniteGaloisCompositum_ranges (K := K) i
  have hw : w.asIdeal.LiesOver (rationalOriginalPrimePlace p hp).asIdeal := by
    letI : w.asIdeal.IsPrime := w.isPrime
    have hle : (rationalOriginalPrimePlace p hp).asIdeal ≤ w.asIdeal.under (𝓞 ℚ) := by
      rw [rationalOriginalPrimePlace_eq_span, Ideal.span_le, Set.singleton_subset_iff]
      change algebraMap (𝓞 ℚ) (𝓞 F) (p : 𝓞 ℚ) ∈ w.asIdeal
      rw [map_natCast]
      exact originalLocalEmbeddingPrime_prime_mem F E p hp
    exact ⟨(rationalOriginalPrimePlace p hp).isMaximal.eq_of_le (Ideal.IsPrime.ne_top inferInstance) hle⟩
  refine ⟨w, hw, ?_⟩
  intro σ hσ
  obtain ⟨g, hg, he⟩ := originalGeneratedLocalField_exists_closure_inertia_lift
    F E p hp Ω hgen σ hσ
  exact ⟨g, hg, he⟩

end
end Dubon2026
