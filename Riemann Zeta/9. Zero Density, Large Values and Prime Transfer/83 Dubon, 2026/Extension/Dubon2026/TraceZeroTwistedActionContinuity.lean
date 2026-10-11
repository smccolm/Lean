import Dubon2026.TraceZeroTwistedDuality
import Dubon2026.ContinuousFirstOrderDeformation

/-! # Joint continuity of the original trace-zero adjoint and its actual character twist -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

/-- The original trace-zero conjugation action is jointly continuous in the group
element and coefficient vector, using the actual matrix and subtype topologies. -/
theorem matrixTraceZeroAdjointAction_continuous
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) :
    Continuous (fun z : G × matrixTraceZeroSubmodule ι R =>
      matrixTraceZeroAdjointRepresentation ρ z.1 z.2) := by
  have hc : Continuous (fun z : G × matrixTraceZeroSubmodule ι R =>
      (ρ z.1).val * z.2.val * (ρ z.1⁻¹).val) :=
    (((Units.continuous_val (M := Matrix ι ι R)).comp (hρ.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)).mul
        ((Units.continuous_val (M := Matrix ι ι R)).comp
          (hρ.comp continuous_fst.inv))
  exact hc.subtype_mk _

/-- A genuine continuous coefficient character preserves joint continuity of the
same original trace-zero action after scalar twisting. -/
theorem matrixTraceZeroCharacterAction_continuous
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (χ : G →* R) (hχ : Continuous χ) :
    Continuous (fun z : G × matrixTraceZeroSubmodule ι R =>
      coefficientCharacterTwist (matrixTraceZeroAdjointRepresentation ρ) χ z.1 z.2) := by
  exact (hχ.comp continuous_fst).smul (matrixTraceZeroAdjointAction_continuous ρ hρ)

end
end Dubon2026
