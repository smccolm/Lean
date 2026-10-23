import Dubon2026.SourceCurveGlobalTateTrace
import Dubon2026.SourceModularCoefficientTateSupport
import Dubon2026.SourceModularCoefficientCompletionSum

/-! The global Tate residue sum on the literal modular coefficient field
equals the sum on its j-coordinate field after applying the actual field
trace. All finite-support and field hypotheses are derived. The rational
base residue theorem remains the next input for DUB-17/18 canonical degree. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve

/-- The literal modular global residue sum transfers to its j-coordinate field. -/
theorem coeff_tateResidue_global_trace (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [IsAlgClosed K] :
    let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
      IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
    letI : Algebra K J := J.toSubalgebra.algebra
    letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
    letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
    letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
    ∀ (f : modularFunctionFieldCoeff N K) (g : J),
      (∑ᶠ w : Place K (modularFunctionFieldCoeff N K),
        w.tateResidue f (algebraMap J (modularFunctionFieldCoeff N K) g)) =
      ∑ᶠ v : Place K J, v.tateResidue (Algebra.trace J (modularFunctionFieldCoeff N K) f) g := by
  let J : IntermediateField K (modularFunctionFieldCoeff N K) :=
    IntermediateField.adjoin K ({jCoeff N K} : Set (modularFunctionFieldCoeff N K))
  letI : Algebra K J := J.toSubalgebra.algebra
  letI : IsScalarTower K J (modularFunctionFieldCoeff N K) := J.isScalarTower_mid'
  letI : FiniteDimensional J (modularFunctionFieldCoeff N K) := finiteDimensional_coeff_field N K
  letI : Algebra.IsIntegral J (modularFunctionFieldCoeff N K) := Algebra.IsIntegral.of_finite _ _
  letI : Algebra.IsSeparable J (modularFunctionFieldCoeff N K) := isSeparable_coeff_field N K
  refine fun f g => ?_
  exact tateResidue_global_trace (coeff_place_residue_algebraMap_bijective N K) f g
    (coeff_tateResidue_support_finite N K f (algebraMap J (modularFunctionFieldCoeff N K) g))

end Dubon2026.SourceFunctionField
