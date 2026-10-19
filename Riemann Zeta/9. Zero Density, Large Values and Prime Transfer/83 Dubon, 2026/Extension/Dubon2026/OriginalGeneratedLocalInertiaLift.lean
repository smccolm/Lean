import Dubon2026.OriginalGeneratedLocalAutomorphism
import Dubon2026.OriginalGeneratedLocalInertia
import Dubon2026.AlgebraicLocalInertiaRestriction
import Dubon2026.RationalPrimeOriginalNormPrime

/-! Every actual global inertia element at the induced prime lifts to
inertia in the generated original local field, then to inertia in its
algebraic overfield. This supplies the surjectivity direction needed to
turn the auxiliary matrix unramifiedness relations into original finite-
field unramifiedness for Dubon Theorem 2.6's base-support quotient. -/

namespace Dubon2026
noncomputable section
open IsDedekindDomain
open scoped NumberField ValuativeRel

attribute [local instance] rationalPrimeOriginalNorm rationalPrimeOriginalNorm_ultrametric
attribute [local instance 1100] rationalPrimeOriginalNormedField

variable (F E : Type) [Field F] [NumberField F] [NontriviallyNormedField E] [Algebra F E]
  (p : ℕ) (hp : p.Prime) [NormedAlgebra (rationalPrimeLocalField p hp) E]
  [ValuativeRel E] [IsNonarchimedeanLocalField E] [IsUltrametricDist E]
  [IsGalois (rationalPrimeLocalField p hp) E]
  [(NormedField.valuation (K := E)).Compatible]
  [(ValuativeRel.valuation (rationalPrimeLocalField p hp)).HasExtension (ValuativeRel.valuation E)]

/-- Original global inertia lifts to actual norm inertia in the same
generated local field, with its complete action on the original field. -/
theorem originalGeneratedLocalField_exists_inertia_lift
    (hgen : (algebraMap (rationalPrimeLocalField p hp) E).fieldRange ⊔
      (algebraMap F E).fieldRange = ⊤)
    (σ : Gal(F/ℚ))
    (hσ : σ ∈ (originalLocalEmbeddingPrime F E p hp).asIdeal.inertia Gal(F/ℚ)) :
    ∃ g : Gal(E/rationalPrimeLocalField p hp), g ∈ algebraicLocalInertia (rationalPrimeLocalField p hp) E ∧
      ∀ x : F, g (algebraMap F E x) = algebraMap F E (σ x) := by
  obtain ⟨g, hg⟩ := originalGeneratedLocalField_exists_automorphism F E p hp hgen σ
    (originalInertia_fixes_prime ℚ F (originalLocalEmbeddingPrime F E p hp) σ hσ)
  exact ⟨g, originalGeneratedLocalField_inertia_mem_normInertia F E p hp hgen σ hσ g hg, hg⟩

/-- The actual generated-field inertia lift extends to norm inertia in
the given algebraic local overfield, preserving the original field action. -/
theorem originalGeneratedLocalField_exists_closure_inertia_lift
    (Ω : Type) [NormedField Ω] [NormedAlgebra (rationalPrimeLocalField p hp) Ω]
    [NormedAlgebra E Ω] [IsScalarTower (rationalPrimeLocalField p hp) E Ω]
    [IsUltrametricDist Ω] [CompleteSpace E]
    [IsGalois (rationalPrimeLocalField p hp) Ω] [IsGalois E Ω]
    (hgen : (algebraMap (rationalPrimeLocalField p hp) E).fieldRange ⊔
      (algebraMap F E).fieldRange = ⊤)
    (σ : Gal(F/ℚ))
    (hσ : σ ∈ (originalLocalEmbeddingPrime F E p hp).asIdeal.inertia Gal(F/ℚ)) :
    ∃ g : Gal(Ω/rationalPrimeLocalField p hp), g ∈ algebraicLocalInertia (rationalPrimeLocalField p hp) Ω ∧
      ∀ x : F, g (algebraMap E Ω (algebraMap F E x)) =
        algebraMap E Ω (algebraMap F E (σ x)) := by
  obtain ⟨h, hh, he⟩ := originalGeneratedLocalField_exists_inertia_lift F E p hp hgen σ hσ
  obtain ⟨g, hg, hgh⟩ := algebraicLocal_inertia_exists_restriction_lift
    (rationalPrimeLocalField p hp) E Ω h hh
  refine ⟨g, hg, ?_⟩
  intro x
  have hres := congrArg (fun s : Gal(E/rationalPrimeLocalField p hp) =>
    algebraMap E Ω (s (algebraMap F E x))) hgh
  exact ((g.restrictNormal_commutes E (algebraMap F E x)).symm.trans hres).trans
    (congrArg (algebraMap E Ω) (he x))

end
end Dubon2026
