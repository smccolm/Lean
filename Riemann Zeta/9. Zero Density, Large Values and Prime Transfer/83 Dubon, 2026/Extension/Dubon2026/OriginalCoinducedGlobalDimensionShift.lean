import Dubon2026.OriginalCoinducedDimensionShift
import Dubon2026.OriginalCoinducedInvariantAcyclicity
import Dubon2026.NormalInvariantCoefficientSequence

/-! # Actual global and quotient-group cohomology dimension shifts -/

namespace Dubon2026
noncomputable section

open CategoryTheory
attribute [local instance 1100] Rep.hV2

variable {k G : Type} [CommRing k] [Group G] (A : Rep.{0} k G)

/-- The original coefficient embedding and its literal quotient form a
short exact sequence before any subgroup restriction. -/
theorem originalCoinducedShortComplex_shortExact :
    (originalCoinducedShortComplex A).ShortExact := by
  refine {
    exact := ?_
    mono_f := (Rep.mono_iff_injective _).mpr (originalCoinducedUnit_injective A)
    epi_g := (Rep.epi_iff_surjective _).mpr (Submodule.mkQ_surjective _) }
  apply ((originalCoinducedShortComplex A).exact_map_iff_of_faithful
    (forget₂ (Rep.{0} k G) (ModuleCat.{0} k))).mp
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change (originalCoinducedUnit A).hom.toLinearMap.range =
    (originalCoinducedUnit A).hom.toLinearMap.range.mkQ.ker
  rw [Submodule.ker_mkQ]

/-- The original global connecting map is an isomorphism from H1 of the
actual quotient to H2 of the original coefficients. -/
theorem originalCoinducedGlobalDimensionShift_isIso :
    IsIso (groupCohomology.δ (originalCoinducedShortComplex_shortExact A) 1 2 rfl) := by
  exact groupCohomology.isIso_δ_of_isZero (originalCoinducedShortComplex_shortExact A) 1
    (originalCoinducedFunction_positive_zero A 0) (originalCoinducedFunction_positive_zero A 1)

/-- When the original subgroup H1 vanishes, the actual quotient-group
invariant sequence is short exact. -/
theorem originalCoinducedInvariantSequence_shortExact (S : Subgroup G) [S.Normal]
    (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1)) :
    (normalInvariantCoefficientSequence (originalCoinducedShortComplex A) S).ShortExact := by
  exact normalInvariantCoefficientSequence_shortExact (originalCoinducedShortComplex A) S
    (originalCoinducedShortComplex_restrict_shortExact A S) hfirst

/-- Its actual connecting map identifies quotient-group H1 of the true
quotient invariants with quotient-group H2 of the original coefficient invariants. -/
theorem originalCoinducedInvariantDimensionShift_isIso (S : Subgroup G) [S.Normal]
    (hfirst : Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1)) :
    IsIso (groupCohomology.δ (originalCoinducedInvariantSequence_shortExact A S hfirst) 1 2 rfl) := by
  exact groupCohomology.isIso_δ_of_isZero
    (originalCoinducedInvariantSequence_shortExact A S hfirst) 1
      (originalCoinducedInvariant_positive_zero A S 0) (originalCoinducedInvariant_positive_zero A S 1)

end
end Dubon2026
