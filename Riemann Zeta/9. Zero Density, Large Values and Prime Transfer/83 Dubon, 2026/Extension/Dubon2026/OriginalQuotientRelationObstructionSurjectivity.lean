import Dubon2026.OriginalFiniteRelationH2Surjectivity
import Dubon2026.OriginalFiniteNormalizedQuotientSystem
import Dubon2026.OriginalFundamentalTwoDegreeVanishing

/-! # Actual normalized quotient relation obstructions are surjective

The original arithmetic quotient class system supplies full fundamental
order, subgroup vanishing, and a finite cyclic H2 target. The proved
finite-group comparison then realizes every H1-to-H2 functional by an
actual relation morphism. This is the surjectivity premise of DUB-17's
remaining relation-extension dévissage for nontrivial coefficient actions.
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

/-- Every functional from actual H1 of the finite original coefficient
to H2 of the normalized outside-unit quotient is realized by a literal
relation morphism. All intermediate duality and cyclicity inputs are derived. -/
theorem originalClassQuotient_relation_obstruction_surjective
    (hsys : OriginalFiniteNormalizedQuotientSystem K L S hS)
    (B : Rep.{0} ℤ Gal(L/K)) [Finite B] :
    Function.Surjective
      (originalRelationExtensionObstruction B (originalIdeleClassesModOutsideRep K L S hS)) := by
  obtain ⟨u, ho, h1, hc, hg, _⟩ := hsys
  let C := originalIdeleClassesModOutsideRep K L S hS
  have hcard : Nat.card (groupCohomology C 2) = Nat.card Gal(L/K) :=
    (Nat.card_congr (originalCohomologyReindex C Subgroup.topEquiv 2).toLinearEquiv.toEquiv).trans
      ((hc ⊤).trans (Nat.card_congr Subgroup.topEquiv.toEquiv))
  letI : Finite (groupCohomology C 2) := Nat.finite_of_card_ne_zero
    (hcard.trans_ne Nat.card_pos.ne')
  have horder : addOrderOf u = Nat.card Gal(L/K) :=
    ho.trans (IsGalois.card_aut_eq_finrank K L).symm
  letI : IsAddCyclic (groupCohomology C 2) :=
    isAddCyclic_of_addOrderOf_eq_card u (horder.trans hcard.symm)
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π C)).mp inferInstance u
  have hv (H : Subgroup Gal(L/K)) :
      Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 2) := by
    letI : Fintype H := Fintype.ofFinite H
    exact originalFundamentalSubgroup_first_second_zero C φ H (h1 H)
      ((hc H).trans Nat.card_eq_fintype_card) (hg H)
  exact originalFiniteFundamental_relation_obstruction_surjective B C φ
    (horder.trans Nat.card_eq_fintype_card) hv

end
end Dubon2026
