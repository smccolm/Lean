import Dubon2026.OriginalFiniteFundamentalNormHomologyEquiv
import Dubon2026.OriginalFiniteNormalizedQuotientSystem
import Dubon2026.OriginalFundamentalTwoDegreeVanishing

/-! # Actual outside-unit quotient norm classes and dual homology

Unpack the original normalized class system and derive the fundamental
subgroup vanishing used by the finite norm/homology comparison. This is
the actual arithmetic-coefficient input to the remaining cardinality
argument for DUB-17's relation-obstruction surjectivity.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2 Submodule.module

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The actual normalized outside-unit quotient system constructs the
norm-class/homology equivalence without supplied fundamental cocycles,
subgroup vanishing, norm lifts or a p-group degree hypothesis. -/
theorem originalClassQuotient_norm_homology_equiv
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (M : Rep.{0} ℤ Gal(L/K)) [Module.Projective ℤ M] :
    Nonempty (OriginalCoefficientNormQuotient M (originalIdeleClassesModOutsideRep K L S hS) ≃ₗ[ℤ]
      groupHomology ((Rep.ihom M).obj (Rep.trivial ℤ Gal(L/K) ℤ)) 1) := by
  obtain ⟨u, _, h1, hc, hg, _⟩ := hsys
  let C := originalIdeleClassesModOutsideRep K L S hS
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π C)).mp inferInstance u
  have hv (H : Subgroup Gal(L/K)) :
      Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 2) := by
    letI : Fintype H := Fintype.ofFinite H
    exact originalFundamentalSubgroup_first_second_zero C φ H (h1 H)
      ((hc H).trans Nat.card_eq_fintype_card) (hg H)
  exact ⟨originalFiniteFundamentalNormHomologyEquiv M C φ hv⟩

end
end Dubon2026
