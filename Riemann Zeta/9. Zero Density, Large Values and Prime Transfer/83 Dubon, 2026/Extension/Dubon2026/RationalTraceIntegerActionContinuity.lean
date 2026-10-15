import Dubon2026.ArithmeticTraceSUnitCohomology

/-! # Continuity of the original trace-zero integer coefficient action

The underlying trace module and its topology are unchanged by restriction
to integer scalars. The existing original matrix-action theorem therefore
supplies continuity for the actual coefficient used in the source Hom
sequence, with no new action-continuity premise.
-/

namespace Dubon2026
noncomputable section
open scoped NumberField

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  (a : 𝓞 ℚ) (q : ℕ) [Fact q.Prime]
  (σ : rationalArithmeticGaloisGroup a →* Matrix.GeneralLinearGroup ι (ZMod q))

/-- The original topology of the same trace-zero coefficient module. -/
abbrev rationalTraceIntegerCoefficientTopology :
    TopologicalSpace (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  inferInstanceAs (TopologicalSpace (matrixTraceZeroSubmodule ι (ZMod q)))

/-- The integer coefficient retains the original finite trace-module topology. -/
local instance : TopologicalSpace (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  rationalTraceIntegerCoefficientTopology a q σ

/-- The original trace-zero integer coefficient is discrete with its original finite matrix topology. -/
theorem rationalTraceIntegerCoefficient_discrete :
    DiscreteTopology (rationalArithmeticTraceZeroIntegerRep a q σ) :=
  inferInstanceAs (DiscreteTopology (matrixTraceZeroSubmodule ι (ZMod q)))

/-- The original arithmetic trace-zero action remains jointly continuous after restricting scalars to the integers. -/
theorem rationalTraceIntegerAction_continuous (hσ : Continuous σ) :
    Continuous (fun z : rationalArithmeticGaloisGroup a × rationalArithmeticTraceZeroIntegerRep a q σ =>
      (rationalArithmeticTraceZeroIntegerRep a q σ).ρ z.1 z.2) :=
  matrixTraceZeroAdjointAction_continuous σ hσ

end
end Dubon2026
