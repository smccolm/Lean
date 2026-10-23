import Dubon2026.SourceCurveLocalTateDerivation
import Dubon2026.SourceModularCoefficientTateAgreement
import Dubon2026.SourceModularCoefficientLocalDifferentials

/-! The exact differential interpretation of the actual modular-field Tate
residue. Uniformizer generation and nontriviality of differentials are
derived for the literal field, and the resulting scalar is precisely its
existing canonical local residue. This closes the local differential input
to the remaining global residue/trace comparison, DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve KaehlerDifferential

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- The Tate pairing on the literal coefficient field obeys the actual differential chain rule. -/
theorem coeff_tateResidue_eq_differentialCoeff
    (v : Place K (modularFunctionFieldCoeff N K)) (f g : modularFunctionFieldCoeff N K) :
    v.tateResidue f g =
      v.tateResidue (f * v.differentialCoeff (D K (modularFunctionFieldCoeff N K) g))
        v.uniformizer := by
  haveI := coeff_place_dCoordGenerates N K v
  haveI : Nontrivial Ω[modularFunctionFieldCoeff N K⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_coeff_differentials N K)
  exact v.tateResidue_eq_differentialCoeff
    (coeff_place_residue_algebraMap_bijective N K v).surjective f g

/-- The actual Tate pairing is exactly the existing canonical local residue of `f dg`. -/
theorem coeff_tateResidue_eq_canonical_differential
    (v : Place K (modularFunctionFieldCoeff N K)) (f g : modularFunctionFieldCoeff N K) :
    v.tateResidue f g = Algebra.trace K v.ResidueField
      ((coeffCanonicalLocalResidueData N K v).res
        (f * v.differentialCoeff (D K (modularFunctionFieldCoeff N K) g))) := by
  rw [coeff_tateResidue_eq_differentialCoeff N K]
  exact (coeff_trace_canonicalResidue_eq_tateResidue N K v _).symm

end Dubon2026.SourceFunctionField
