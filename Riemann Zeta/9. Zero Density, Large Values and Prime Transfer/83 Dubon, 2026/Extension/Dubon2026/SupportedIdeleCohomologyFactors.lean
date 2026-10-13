import Dubon2026.SupportedIdeleLocalFactorRepresentation
import Dubon2026.BinaryProductCohomology

/-! # Original supported-idele cohomology after outside-support vanishing

The actual representation isomorphism and existing product cohomology
identify the original group with its two actual factors. A zero outside
factor removes it completely, deriving both finiteness and the original
cohomology order needed for DUB-17's supported-idele Herbrand formula.
-/

namespace Dubon2026
noncomputable section
open NumberField IsDedekindDomain CategoryTheory
open scoped NumberField Classical
variable (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
  (S : Finset (HeightOneSpectrum (𝓞 L)))
  (hS : ∀ (σ : Gal(L/K)) v, v ∈ S ↔ numberFieldGaloisPlaceEquiv K L σ v ∈ S)

/-- The original supported-idele cohomology is the product of its actual unrestricted and outside-support cohomologies. -/
def supportedIdeleCohomologyFactorEquiv (n : ℕ) :
    groupCohomology (originalSupportedIdeleRep K L S hS) n ≃
      groupCohomology (supportedUnrestrictedUnitRep K L S hS) n ×
        groupCohomology (supportedOutsideUnitRep K L S hS) n :=
  (supportedIdeleLocalFactorCohomologyIso K L S hS n).toLinearEquiv.toEquiv.trans
    (originalBinaryProductCohomologyIso
      (supportedUnrestrictedUnitRep K L S hS) (supportedOutsideUnitRep K L S hS) n).toLinearEquiv.toEquiv

/-- Outside-support vanishing reduces actual supported-idele finiteness and order to the original unrestricted factor. -/
theorem originalSupportedIdele_cohomology_of_outside_zero (n : ℕ)
    [Finite (groupCohomology (supportedUnrestrictedUnitRep K L S hS) n)]
    (hout : Limits.IsZero (groupCohomology (supportedOutsideUnitRep K L S hS) n)) :
    Finite (groupCohomology (originalSupportedIdeleRep K L S hS) n) ∧
      Nat.card (groupCohomology (originalSupportedIdeleRep K L S hS) n) =
        Nat.card (groupCohomology (supportedUnrestrictedUnitRep K L S hS) n) := by
  letI : Subsingleton (groupCohomology (supportedOutsideUnitRep K L S hS) n) :=
    ModuleCat.isZero_iff_subsingleton.mp hout
  let e := supportedIdeleCohomologyFactorEquiv K L S hS n
  refine ⟨Finite.of_equiv
    (groupCohomology (supportedUnrestrictedUnitRep K L S hS) n ×
      groupCohomology (supportedOutsideUnitRep K L S hS) n) e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_prod,
    Nat.card_unique (α := groupCohomology (supportedOutsideUnitRep K L S hS) n), mul_one]

end
end Dubon2026
