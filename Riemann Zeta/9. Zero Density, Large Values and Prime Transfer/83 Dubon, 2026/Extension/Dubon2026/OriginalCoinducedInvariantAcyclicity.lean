import Dubon2026.OriginalCoinducedInvariantQuotient
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-! # Genuine positive cohomology vanishing for the original invariant coinduction -/

namespace Dubon2026
noncomputable section

open CategoryTheory

/-- The original function representation coinduced from the trivial
subgroup has zero positive cohomology by the pinned Shapiro isomorphism. -/
theorem originalCoinducedFunction_positive_zero
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G) (n : ℕ) :
    Limits.IsZero (groupCohomology (originalCoinducedFunctionRep A) (n + 1)) := by
  exact (isZero_groupCohomology_succ_of_subsingleton
    (Rep.res (⊥ : Subgroup G).subtype A) n).of_iso
      (groupCohomology.coindIso (Rep.res (⊥ : Subgroup G).subtype A) (n + 1))

/-- Its actual normal-subgroup invariants have zero positive cohomology
over the actual quotient group, using the proved original function isomorphism. -/
theorem originalCoinducedInvariant_positive_zero
    {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)
    (S : Subgroup G) [S.Normal] (n : ℕ) :
    Limits.IsZero (groupCohomology
      ((originalCoinducedFunctionRep A).quotientToInvariants S) (n + 1)) := by
  exact (originalCoinducedFunction_positive_zero (Rep.trivial k (G ⧸ S) A) n).of_iso
    ((groupCohomology.functor k (G ⧸ S) (n + 1)).mapIso
      (originalCoinducedInvariantQuotientIso A S))

end
end Dubon2026
