import Dubon2026.SourceEllipticTorsionIntegralCoordinates
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! The residue field of a valuation subring of an algebraically closed field
is algebraically closed. Native monic lifting and root existence, followed by
integrality, suffice. This supplies the residue torsion cardinality required
for actual torsion lifting in the DUB-17/18 quotient-product reduction. -/

namespace Dubon2026.SourceEllipticReduction
open Polynomial IsLocalRing SourceEllipticFunctionField

/-- Algebraic closedness of the ambient field descends to the actual valuation residue field. -/
theorem residueField_isAlgClosed {L : Type*} [Field L] [IsAlgClosed L]
    (A : ValuationSubring L) : IsAlgClosed (ResidueField A) := by
  classical
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  have hl : p ∈ Polynomial.lifts (residue A) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact residue_surjective (p.coeff n)
  obtain ⟨q, hq, hdeg, hmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero (k := L) q
    (by rw [hdeg]; exact Polynomial.degree_pos_of_irreducible hirr |>.ne')
  have hxA : x ∈ A := mem_valuationSubring_of_integral A ⟨q, hmon, hx⟩
  have hqx : q.eval ⟨x, hxA⟩ = 0 := by
    apply A.subtype_injective
    rw [map_zero, ← Polynomial.eval_map_apply, Polynomial.eval_map]
    exact hx
  refine ⟨residue A ⟨x, hxA⟩, ?_⟩
  rw [← hq, Polynomial.eval_map_apply, hqx, map_zero]

end Dubon2026.SourceEllipticReduction
