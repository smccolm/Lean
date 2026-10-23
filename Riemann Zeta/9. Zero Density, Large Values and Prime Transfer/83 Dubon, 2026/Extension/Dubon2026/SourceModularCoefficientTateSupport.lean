import Dubon2026.SourceCurveTateCanonicalSupport
import Dubon2026.SourceModularCoefficientTateDifferentials
import Dubon2026.SourceModularCoefficientCanonicalDivisors

/-! The actual modular Tate pairing has finite global support for every
pair of functions, including when the second differential vanishes in
positive characteristic. The proved principal and canonical supports
discharge the finiteness input to the DUB-17/18 global trace transfer. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve KaehlerDifferential

/-- The literal modular Tate residue sum has finite support, in every characteristic. -/
theorem coeff_tateResidue_support_finite (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [IsAlgClosed K] (f g : modularFunctionFieldCoeff N K) :
    (Function.support (fun v : Place K (modularFunctionFieldCoeff N K) =>
      v.tateResidue f g)).Finite := by
  haveI : ∀ v : Place K (modularFunctionFieldCoeff N K), v.DCoordGenerates :=
    coeff_place_dCoordGenerates N K
  haveI : Nontrivial Ω[modularFunctionFieldCoeff N K⁄K] :=
    Module.nontrivial_of_finrank_eq_succ (n := 0) (finrank_coeff_differentials N K)
  apply tateResidue_support_finite (coeffCanonicalLocalResidueData N K)
    (coeff_place_residue_algebraMap_bijective N K) f g (finite_coeff_divisor_support N K f)
  by_cases hg : D K (modularFunctionFieldCoeff N K) g = 0
  · simp only [hg, Place.ordDifferential, Place.differentialCoeff_zero,
      Place.ord_zero, ne_eq, not_true_eq_false, Set.setOf_false, Set.finite_empty]
  · exact finite_coeff_differential_support N K hg

end Dubon2026.SourceFunctionField
