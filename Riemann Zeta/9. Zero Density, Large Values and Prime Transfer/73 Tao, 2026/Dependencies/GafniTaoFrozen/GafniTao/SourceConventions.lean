import RiemannZeta.PublicationContract

/-!
# Source conventions

This module records the exact frozen objects used by the Gafni--Tao
formalization.  It contains only definitional aliases and proved bridges; it
does not postulate any analytic estimate.
-/

open scoped BigOperators

namespace GafniTao

open RiemannZeta.GuthMaynard

/-- The frozen multiplicity-weighted symmetric zeta-zero count. -/
noncomputable abbrev zeroCount (sigma T : ℝ) : ℕ := N sigma T

/-- The finite set of distinct zeros underlying `zeroCount`; multiplicity is
carried separately by `analyticVanishingOrder`. -/
noncomputable abbrev zeroSet (sigma T : ℝ) : Finset ℂ :=
  zerosInRect sigma 1 (-T) T

/-- The analytic multiplicity used throughout the isolated formalization. -/
noncomputable abbrev zeroMultiplicity (rho : ℂ) : ℕ :=
  analyticVanishingOrder riemannZeta rho

/-- The frozen `N` is definitionally the weighted sum over the frozen zero
set.  This is the source-entry bridge used by all later finite zero sums. -/
theorem zeroCount_eq_weighted_sum (sigma T : ℝ) :
    zeroCount sigma T = ∑ rho ∈ zeroSet sigma T, zeroMultiplicity rho := by
  rfl

/-- The actual publication-facing Guth--Maynard theorem at the frozen
boundary.  Later consumers must apply this declaration, not replace it with a
new hypothesis. -/
theorem frozen_guthMaynard_zero_density :
    PublishedGuthMaynardZeroDensity zeroCount := by
  exact guthMaynardZeroDensity_published_native

end GafniTao
