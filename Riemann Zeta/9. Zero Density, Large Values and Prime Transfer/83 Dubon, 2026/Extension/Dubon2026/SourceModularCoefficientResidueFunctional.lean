import Dubon2026.SourceCurveResidueProbe
import Dubon2026.SourceModularCoefficientLocalResidues
import Dubon2026.SourceModularCoefficientCanonicalDivisors
import Dubon2026.SourceModularCoefficientGlobalSpaces

/-! DUB-17/18 -> good reduction -> reverse genus inequality -> canonical
degree and residue duality. Reuse the existing local-residue and Weil-rank
proofs on the actual modular coefficient field. The residue constants,
canonical support and finite divisor-space maxima are proved in every
characteristic. Global residue vanishing remains a separate obligation;
no such vanishing is assumed or claimed here. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [IsAlgClosed L]

/-- The actual finite trace-residue sum for a nonzero coefficient-field differential. -/
def coeffResidueFunctional {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0) :
    Module.Dual L (adeleSpace L (modularFunctionFieldCoeff N L)) := by
  haveI := hasCanonicalDivisor_coeff N L
  haveI : ∀ v : Place L (modularFunctionFieldCoeff N L), v.DCoordGenerates :=
    coeff_place_dCoordGenerates N L
  exact weilOfKaehlerK (coeffCanonicalLocalResidueData N L) hω

theorem coeffResidueFunctional_ne_zero
    {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0) :
    coeffResidueFunctional N L hω ≠ 0 := by
  haveI := hasCanonicalDivisor_coeff N L
  haveI : ∀ v : Place L (modularFunctionFieldCoeff N L), v.DCoordGenerates :=
    coeff_place_dCoordGenerates N L
  haveI := nonempty_coeff_place N L
  exact weilOfKaehlerK_ne_zero_of_rational_residues (coeffCanonicalLocalResidueData N L)
    (coeff_place_residue_algebraMap_bijective N L) hω

theorem coeffResidueFunctional_vanish_canonical
    {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0)
    {α : adeleSpace L (modularFunctionFieldCoeff N L)}
    (hα : (α : Place L (modularFunctionFieldCoeff N L) → modularFunctionFieldCoeff N L) ∈
      adeleBdd (coeffCanonicalDivisor N L hω)) :
    coeffResidueFunctional N L hω α = 0 := by
  haveI := hasCanonicalDivisor_coeff N L
  haveI : ∀ v : Place L (modularFunctionFieldCoeff N L), v.DCoordGenerates :=
    coeff_place_dCoordGenerates N L
  have he : canonicalDivisorOf hω = coeffCanonicalDivisor N L hω := by
    ext v
    rw [canonicalDivisorOf_apply, coeffCanonicalDivisor_apply]
  apply weilOfKaehlerK_vanish_adeleBdd_canonical (coeffCanonicalLocalResidueData N L) hω
  rwa [he]

theorem coeffResidueFunctional_vanish_bound_iff
    {ω : Ω[modularFunctionFieldCoeff N L⁄L]} (hω : ω ≠ 0)
    (D : Divisor L (modularFunctionFieldCoeff N L)) :
    (∀ α : adeleSpace L (modularFunctionFieldCoeff N L),
      (α : Place L (modularFunctionFieldCoeff N L) → modularFunctionFieldCoeff N L) ∈ adeleBdd D →
      coeffResidueFunctional N L hω α = 0) ↔ D ≤ coeffCanonicalDivisor N L hω := by
  constructor
  · intro hD
    haveI := hasCanonicalDivisor_coeff N L
    haveI : ∀ v : Place L (modularFunctionFieldCoeff N L), v.DCoordGenerates :=
      coeff_place_dCoordGenerates N L
    have he : canonicalDivisorOf hω = coeffCanonicalDivisor N L hω := by
      ext v
      rw [canonicalDivisorOf_apply, coeffCanonicalDivisor_apply]
    rw [← he]
    exact weilOfKaehlerK_adeleBound_le_canonical (coeffCanonicalLocalResidueData N L)
      (coeff_place_residue_algebraMap_bijective N L) hω hD
  · intro hD α hα
    exact coeffResidueFunctional_vanish_canonical N L hω (adeleBdd_mono hD hα)

end
end Dubon2026.SourceFunctionField
