import Dubon2026.SourceCurveLocalTateLeibniz
import Dubon2026.SourceModularCoefficientTateResidues

/-! The actual coefficient-field residue pairing satisfies the Leibniz rule.
Every finite principal-part and finite commutator premise is derived. This
is the product identity needed for the local differential factor in the
global residue argument for the reverse modular genus bound, DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- The exact differential Leibniz rule at every literal modular coefficient-field place. -/
theorem coeff_tateResidue_leibniz (v : Place K (modularFunctionFieldCoeff N K))
    (f g h : modularFunctionFieldCoeff N K) :
    v.tateResidue f (g * h) = v.tateResidue (f * g) h + v.tateResidue (f * h) g :=
  v.tateResidue_leibniz (coeff_place_residue_algebraMap_bijective N K v).surjective f g h

end Dubon2026.SourceFunctionField
