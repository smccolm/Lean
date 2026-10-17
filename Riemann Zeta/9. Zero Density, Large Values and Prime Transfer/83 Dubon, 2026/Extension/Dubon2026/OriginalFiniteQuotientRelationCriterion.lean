import Dubon2026.OriginalFiniteFundamentalRelationCriterion
import Dubon2026.OriginalFiniteNormalizedQuotientSystem
import Dubon2026.OriginalFundamentalTwoDegreeVanishing

/-! # Relation extension for the original finite outside-unit quotient

Unpack the genuine normalized quotient system and derive its fundamental
cocycle and subgroup vanishing. The finite-group converse norm theorem
then applies without a p-group assumption. The remaining arithmetic
inputs are the original normalized class system and invariant norm roots;
nontrivial coefficient actions still require the subgroup extension step
on DUB-17's finite class/Ext and reverse-localization chain.
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

/-- The actual finite quotient class system and invariant norm roots
give the literal relation-extension criterion. No fundamental cocycle,
subgroup acyclicity or p-group certificate is assumed. -/
theorem originalClassQuotient_relation_obstruction_zero_iff_extension
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (p : ℕ) [Fact p.Prime]
    (hnorm : ∀ c : originalIdeleClassesModOutsideRep K L S hS,
      ∃ d : originalIdeleClassesModOutsideRep K L S hS,
        (∀ g, (originalIdeleClassesModOutsideRep K L S hS).ρ g d = d) ∧
        (∑ g : Gal(L/K), (originalIdeleClassesModOutsideRep K L S hS).ρ g c) = p • d)
    (B : Rep.{0} ℤ Gal(L/K)) [Finite B] (hB : ∀ b : B, p • b = 0)
    (htriv : ∀ (g : Gal(L/K)) (b : B), B.ρ g b = b)
    (χ : originalRelationModule B ⟶ originalIdeleClassesModOutsideRep K L S hS) :
    originalRelationExtensionObstruction B (originalIdeleClassesModOutsideRep K L S hS) χ = 0 ↔
      ∃ a : Rep.free ℤ Gal(L/K) B ⟶ originalIdeleClassesModOutsideRep K L S hS,
        originalRelationInclusion B ≫ a = χ := by
  obtain ⟨u, ho, h1, hc, hg, _⟩ := hsys
  let C := originalIdeleClassesModOutsideRep K L S hS
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π C)).mp inferInstance u
  have horder : addOrderOf (groupCohomology.H2π C φ) = Fintype.card Gal(L/K) :=
    ho.trans ((IsGalois.card_aut_eq_finrank K L).symm.trans Nat.card_eq_fintype_card)
  have hv (H : Subgroup Gal(L/K)) :
      Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 2) := by
    letI : Fintype H := Fintype.ofFinite H
    exact originalFundamentalSubgroup_first_second_zero C φ H (h1 H)
      ((hc H).trans Nat.card_eq_fintype_card) (hg H)
  exact originalFiniteFundamental_relation_obstruction_zero_iff_extension C φ horder hv
    p hnorm B hB htriv χ

end
end Dubon2026
