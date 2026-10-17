import Dubon2026.OriginalCoinducedInternalHomIso
import Dubon2026.OriginalPrimeReductionClassification

/-! # Transport actual internal-Hom vanishing through the original mod-p isomorphism

Pinned contravariant internal-Hom functoriality transports the explicit
coinduced classification. The resulting original reduced internal Hom
has zero positive cohomology, the input to integral H1 lifting on
DUB-17's fundamental-kernel projectivity route.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory
attribute [local instance 1100] Rep.hV2

/-- An actual isomorphism to original coinduced functions gives positive internal-Hom cohomology vanishing by pinned functoriality. -/
theorem originalInternalHom_positive_zero_of_coinduced_iso
    {k G : Type} [CommRing k] [Group G] [Fintype G]
    (A D R : Rep.{0} k G) (e : A ≅ originalCoinducedFunctionRep D) (n : ℕ) :
    Limits.IsZero (groupCohomology ((Rep.ihom A).obj R) (n + 1)) := by
  let hi : (Rep.ihom A).obj R ≅ (Rep.ihom (originalCoinducedFunctionRep D)).obj R :=
    ((MonoidalClosed.internalHom.mapIso e.op).app R).symm
  exact (originalCoinducedInternalHom_positive_zero D R n).of_iso
    ((groupCohomology.functor k G (n + 1)).mapIso hi)

/-- The original reduced internal Hom has zero positive cohomology, with the mod-p coinduced classification derived from the original low-degree conditions. -/
theorem originalPrimeReducedInternalHom_positive_zero
    {G : Type} [Group G] [Fintype G] (A R : Rep.{0} ℤ G)
    [Module.IsTorsionFree ℤ A] (p : ℕ) [Fact p.Prime] (hG : IsPGroup p G)
    (hnorm : OriginalNormCoinvariantInjective A)
    (hfirst : Limits.IsZero (groupHomology A 1)) (n : ℕ) :
    Limits.IsZero (groupCohomology
      ((Rep.ihom (originalScalarReduction A (p : ℤ))).obj (originalScalarReduction R (p : ℤ)))
      (n + 1)) := by
  obtain ⟨e⟩ := originalPrimeReduction_coinduced_iso A p hG hnorm hfirst
  exact originalInternalHom_positive_zero_of_coinduced_iso _ _ _ e n

end
end Dubon2026
