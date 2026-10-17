import Dubon2026.OriginalFundamentalPGroupVanishing
import Dubon2026.OriginalFiniteNormalizedQuotientSystem

/-! # The source-normalized original quotient's actual fundamental coefficient

A cocycle representing the already constructed normalized quotient class
defines the literal twisted extension. Its subgroup H1/H2 vanishing and
positive/degree-zero p-group acyclicity are derived, with the source
completion normalization retained. This supplies a necessary coefficient
on DUB-17's finite class/Ext route, not the remaining duality statement.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped NumberField
attribute [local instance 1100] Rep.hV2

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
  (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- A source-normalized quotient cocycle with its literal short exact splitting coefficient, derived subgroup H1/H2 vanishing, positive vanishing and invariant norm preimages. This proposition alone asserts no existence. -/
def OriginalNormalizedQuotientSplitting : Prop :=
  let C := originalIdeleClassesModOutsideRep K L S hS
  ∃ φ : groupCohomology.cocycles₂ C,
    addOrderOf (groupCohomology.H2π C φ) = Module.finrank K L ∧
    OriginalCompletionQuotientRestrictions K L S hS (groupCohomology.H2π C φ) ∧
    (originalFundamentalSplittingShortComplex C φ).ShortExact ∧
    (∀ H : Subgroup Gal(L/K),
      Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 1) ∧
        Limits.IsZero (groupCohomology (Rep.res H.subtype (originalFundamentalSplittingModule C φ)) 2)) ∧
    (∀ n : ℕ, Limits.IsZero (groupCohomology (originalFundamentalSplittingModule C φ) (n + 1))) ∧
    OriginalInvariantNormSurjective (originalFundamentalSplittingModule C φ)

/-- The already proved original normalized finite quotient system constructs its actual fundamental coefficient and discharges its subgroup, positive and invariant-norm vanishing for a finite p-group. -/
theorem originalClassQuotient_normalized_fundamental_splitting
    (p : ℕ) [Fact p.Prime] (hG : IsPGroup p Gal(L/K))
    (h : OriginalFiniteNormalizedQuotientSystem K L S hS) :
    OriginalNormalizedQuotientSplitting K L S hS := by
  obtain ⟨u, ho, h1, hc, hg, hl⟩ := h
  let C := originalIdeleClassesModOutsideRep K L S hS
  obtain ⟨φ, rfl⟩ := (ModuleCat.epi_iff_surjective (groupCohomology.H2π C)).mp inferInstance u
  obtain ⟨hv, hp, hn⟩ := originalFundamentalPGroup_positive_and_norm p hG C φ h1 hc hg
  exact ⟨φ, ho, hl, originalFundamentalSplittingShortComplex_shortExact C φ, hv, hp, hn⟩

end
end Dubon2026
