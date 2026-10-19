import Dubon2026.OriginalGeneratedLocalInertiaLift
import Dubon2026.ArithmeticFiniteLocalRestrictionSquare
import Dubon2026.RationalArithmeticOriginalCompletionTower
import Dubon2026.RationalPrimeCyclotomicInertia
import Dubon2026.RationalArithmeticFiniteInertiaTrivial

/-! Every inertia element at an actual prime of the original finite
arithmetic field lifts to the original prime-local norm inertia. The
finite local stage, completion extension, valuation comparison and norm
inertia lifting are all constructed. This removes the inertia-image
surjectivity assumption in the finite-field unramifiedness step serving
Dubon Theorem 2.6's base-support deformation quotient. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField ValuativeRel NNReal

attribute [local instance] arithmeticFiniteLocalStageAlgebra
  arithmeticFiniteLocalStageGalois arithmeticFiniteLocalStageRationalAlgebra
  rationalPrimeLocalField_charZero rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
  rationalPrimeOriginalClosureNorm rationalPrimeOriginalClosureNormedAlgebra
  rationalPrimeOriginalClosureNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField

/-- At an actual original prime above the selected rational prime,
every original finite inertia automorphism is realized by original local
norm inertia under the literal arithmetic restriction. -/
theorem rationalArithmetic_finite_inertia_exists_norm_lift
    (a : 𝓞 ℚ) (F : FiniteGaloisIntermediateField ℚ (rationalUnramifiedExtension a))
    (p : ℕ) (hp : p.Prime) :
    ∃ w : HeightOneSpectrum (𝓞 F),
      w.asIdeal.LiesOver (rationalOriginalPrimePlace p hp).asIdeal ∧
      ∀ σ : Gal(F/ℚ), σ ∈ w.asIdeal.inertia Gal(F/ℚ) →
        ∃ g, g ∈ rationalPrimeNormInertia p hp ∧
          AlgEquiv.restrictNormalHom F (rationalPrimeArithmeticRestriction a p hp g) = σ := by
  let K := rationalPrimeLocalField p hp
  let Ω := rationalPrimeLocalClosure p hp
  let C := rationalArithmeticFiniteLocalStage a F p hp
  let E := C.toIntermediateField
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
  letI : NumberField F := NumberField.of_module_finite ℚ F
  let j : F →ₐ[ℚ] E := rationalArithmeticFiniteLocalStageInclusion a F p hp
  letI : Algebra F E := j.toRingHom.toAlgebra
  let w := originalLocalEmbeddingPrime F E p hp
  have hgen : (algebraMap K E).fieldRange ⊔ (algebraMap F E).fieldRange = ⊤ :=
    rationalArithmeticFiniteLocalStage_ranges a F p hp
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
  refine ⟨g, hg, ?_⟩
  apply AlgEquiv.ext
  intro x
  let e := rationalPrimeArithmeticOriginalEmbedding a p hp
  apply Subtype.ext
  apply e.injective
  have hr := (show Gal(rationalUnramifiedExtension a/ℚ) from
    rationalPrimeArithmeticRestriction a p hp g).restrictNormal_commutes F x
  have hfirst := (congrArg e hr).trans (rationalPrimeArithmeticRestriction_commutes a p hp g
    (algebraMap F (rationalUnramifiedExtension a) x))
  exact hfirst.trans (he x)

end
end Dubon2026
