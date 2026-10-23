import Dubon2026.SourceCurveCompletionTateTrace
import Dubon2026.SourceModularCoefficientTateDifferentials

/-! The actual completed local Tate trace is exactly the original modular
canonical differential residue. No completion-compatibility assumption is
left in this local identity. The extension trace sum over places is still
required for global residues and the DUB-17/18 reverse-genus chain. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- Completion preserves every Tate pairing of literal modular coefficient-field elements. -/
theorem coeff_completion_tateResidue
    (v : Place K (modularFunctionFieldCoeff N K)) (f g : modularFunctionFieldCoeff N K) :
    v.completionPlace.tateResidue
      (algebraMap (modularFunctionFieldCoeff N K) v.adicCompletion f)
      (algebraMap (modularFunctionFieldCoeff N K) v.adicCompletion g) = v.tateResidue f g :=
  v.completion_tateResidue (coeff_place_residue_algebraMap_bijective N K v).surjective f g

/-- The completed local trace is the literal original canonical residue of `f dg`. -/
theorem coeff_completion_tateResidue_eq_canonical_differential
    (v : Place K (modularFunctionFieldCoeff N K)) (f g : modularFunctionFieldCoeff N K) :
    v.completionPlace.tateResidue
      (algebraMap (modularFunctionFieldCoeff N K) v.adicCompletion f)
      (algebraMap (modularFunctionFieldCoeff N K) v.adicCompletion g) =
        Algebra.trace K v.ResidueField ((coeffCanonicalLocalResidueData N K v).res
          (f * v.differentialCoeff (D K (modularFunctionFieldCoeff N K) g))) := by
  rw [coeff_completion_tateResidue N K]
  exact coeff_tateResidue_eq_canonical_differential N K v f g

end Dubon2026.SourceFunctionField
