import Dubon2026.OriginalCoinducedSubgroupRetract
import Dubon2026.OriginalNormalSequenceCohomologyMaps

/-! # Positive dimension shifts on the original coefficients and invariants

These are the shifts needed to transfer positive cohomological vanishing
across a normal subgroup in the finite class/Ext norm criterion. Existing
short exact sequences and subgroup retractions discharge all intermediate
acyclicity; the connecting maps remain the original ones.
-/
namespace Dubon2026
noncomputable section
open CategoryTheory

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)

/-- The original global coinduced connecting map is an isomorphism in every positive degree. -/
theorem originalCoinducedGlobalPositiveShift_isIso (n : ℕ) :
    IsIso (groupCohomology.δ (originalCoinducedShortComplex_shortExact A) (n + 1) (n + 2) rfl) :=
  groupCohomology.isIso_δ_of_isZero (originalCoinducedShortComplex_shortExact A) (n + 1)
    (originalCoinducedFunction_positive_zero A n) (originalCoinducedFunction_positive_zero A (n + 1))

/-- The same original connecting map remains an isomorphism in every positive degree after subgroup restriction. -/
theorem originalCoinducedSubgroupPositiveShift_isIso (S : Subgroup G) (n : ℕ) :
    IsIso (groupCohomology.δ (originalCoinducedShortComplex_restrict_shortExact A S)
      (n + 1) (n + 2) rfl) :=
  groupCohomology.isIso_δ_of_isZero (originalCoinducedShortComplex_restrict_shortExact A S) (n + 1)
    (originalCoinducedSubgroup_positive_zero A S n) (originalCoinducedSubgroup_positive_zero A S (n + 1))

/-- Positive subgroup vanishing passes to the actual coinduced quotient. -/
theorem originalCoinducedQuotient_subgroup_positive_zero (S : Subgroup G)
    (h : ∀ n : ℕ, Limits.IsZero (groupCohomology (Rep.res S.subtype A) (n + 1)))
    (n : ℕ) :
    Limits.IsZero (groupCohomology (Rep.res S.subtype (originalCoinducedQuotient A)) (n + 1)) := by
  exact (h (n + 1)).of_iso
    (@asIso _ _ _ _
      (groupCohomology.δ (originalCoinducedShortComplex_restrict_shortExact A S)
        (n + 1) (n + 2) rfl)
      (originalCoinducedSubgroupPositiveShift_isIso A S n))

/-- Vanishing subgroup H1 makes the genuine invariant sequence exact and gives all its positive connecting isomorphisms. -/
theorem originalCoinducedInvariantPositiveShift_isIso (S : Subgroup G) [S.Normal]
    (h : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1)) (n : ℕ) :
    IsIso (groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S h)
      (n + 1) (n + 2) rfl) :=
  groupCohomology.isIso_δ_of_isZero (originalCoinducedInvariantSequence_shortExact A S h) (n + 1)
    (originalCoinducedInvariant_positive_zero A S n) (originalCoinducedInvariant_positive_zero A S (n + 1))

end
end Dubon2026
