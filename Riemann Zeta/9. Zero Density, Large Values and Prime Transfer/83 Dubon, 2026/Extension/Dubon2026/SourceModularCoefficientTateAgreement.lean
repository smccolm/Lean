import Dubon2026.SourceCurveTateResidueAgreement
import Dubon2026.SourceModularCoefficientTateResidues
import Dubon2026.SourceCurveResidueSumEquiv

/-! The actual modular coefficient field's Tate residue agrees with its
existing canonical local residue. This closes the uniformizer agreement
input to the residue/trace comparison needed for the canonical-degree and
reverse-genus steps of DUB-17/18. Global residue vanishing remains open. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- Exact agreement with the existing scalar residue at every actual modular-field place. -/
theorem coeff_tateResidue_uniformizer (v : Place K (modularFunctionFieldCoeff N K))
    (f : modularFunctionFieldCoeff N K) :
    v.tateResidue f v.uniformizer = v.localResidueScalar f :=
  v.tateResidue_uniformizer (coeff_place_residue_algebraMap_bijective N K v).surjective f

/-- The actual canonical local residue used in global sums is the same normalized Tate trace. -/
theorem coeff_trace_canonicalResidue_eq_tateResidue
    (v : Place K (modularFunctionFieldCoeff N K)) (f : modularFunctionFieldCoeff N K) :
    Algebra.trace K v.ResidueField ((coeffCanonicalLocalResidueData N K v).res f) =
      v.tateResidue f v.uniformizer := by
  rw [v.trace_canonicalResidue_eq_scalar (coeffCanonicalLocalResidueData N K v)
    (coeff_place_residue_algebraMap_bijective N K v), coeff_tateResidue_uniformizer]

end Dubon2026.SourceFunctionField
