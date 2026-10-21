import Dubon2026.SourceCurveResidueProbe
import Dubon2026.SourceOriginalLocalResidues
import Dubon2026.SourceOriginalCanonicalDivisors
import Dubon2026.SourceOriginalAdelicQuotients

/-! DUB-17/18 -> original regular differential dimension -> Riemann--Roch
-> residue duality. The actual original local residues give a nonzero
repartition functional. Its maximal vanishing divisor bound is precisely
the actual canonical divisor. Its vanishing on global functions is the
remaining global residue identity; no such vanishing is assumed here.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential
variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L] [IsAlgClosed L]

/-- The actual finite trace-residue sum for a nonzero original differential. -/
def originalResidueFunctional {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0) :
    Module.Dual L (adeleSpace L (modularFunctionFieldOver N L)) := by
  haveI := hasCanonicalDivisor_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  exact weilOfKaehlerK (originalCanonicalLocalResidueData N L) hω

theorem originalResidueFunctional_ne_zero
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0) :
    originalResidueFunctional N L hω ≠ 0 := by
  haveI := hasCanonicalDivisor_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  haveI := nonempty_original_places N L
  exact weilOfKaehlerK_ne_zero_of_rational_residues (originalCanonicalLocalResidueData N L)
    (original_place_residue_algebraMap_bijective N L) hω

theorem originalResidueFunctional_vanish_canonical
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0)
    {α : adeleSpace L (modularFunctionFieldOver N L)}
    (hα : (α : Place L (modularFunctionFieldOver N L) → modularFunctionFieldOver N L) ∈
      adeleBdd (originalCanonicalDivisor N L hω)) :
    originalResidueFunctional N L hω α = 0 := by
  haveI := hasCanonicalDivisor_original N L
  haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
    original_place_dCoordGenerates N L
  have he : canonicalDivisorOf hω = originalCanonicalDivisor N L hω := by
    ext v
    rw [canonicalDivisorOf_apply, originalCanonicalDivisor_apply]
  apply weilOfKaehlerK_vanish_adeleBdd_canonical (originalCanonicalLocalResidueData N L) hω
  rwa [he]

theorem originalResidueFunctional_vanish_bound_iff
    {ω : Ω[modularFunctionFieldOver N L⁄L]} (hω : ω ≠ 0)
    (D : Divisor L (modularFunctionFieldOver N L)) :
    (∀ α : adeleSpace L (modularFunctionFieldOver N L),
      (α : Place L (modularFunctionFieldOver N L) → modularFunctionFieldOver N L) ∈ adeleBdd D →
      originalResidueFunctional N L hω α = 0) ↔ D ≤ originalCanonicalDivisor N L hω := by
  constructor
  · intro hD
    haveI := hasCanonicalDivisor_original N L
    haveI : ∀ v : Place L (modularFunctionFieldOver N L), v.DCoordGenerates :=
      original_place_dCoordGenerates N L
    have he : canonicalDivisorOf hω = originalCanonicalDivisor N L hω := by
      ext v
      rw [canonicalDivisorOf_apply, originalCanonicalDivisor_apply]
    rw [← he]
    exact weilOfKaehlerK_adeleBound_le_canonical (originalCanonicalLocalResidueData N L)
      (original_place_residue_algebraMap_bijective N L) hω hD
  · intro hD α hα
    exact originalResidueFunctional_vanish_canonical N L hω (adeleBdd_mono hD hα)

end
end Dubon2026.SourceFunctionField
