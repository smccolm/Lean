import Dubon2026.ContinuousRepresentationCohomology
import Dubon2026.ContinuousTraceZeroCohomology
import Dubon2026.TraceZeroTwistedActionContinuity

/-! # Exact comparison with the original continuous deformation cohomology -/

namespace Dubon2026
noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
    [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

/-- Joint continuity of the same full-matrix conjugation action used by the
original first-order deformation cocycles. -/
theorem matrixAdjointAction_continuous
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) :
    Continuous (fun z : G × Matrix ι ι R => (matrixAdjointRep ρ).ρ z.1 z.2) := by
  exact (((Units.continuous_val (M := Matrix ι ι R)).comp
    (hρ.comp continuous_fst)).mul continuous_snd).mul
      ((Units.continuous_val (M := Matrix ι ι R)).comp
        (hρ.comp continuous_fst.inv))

/-- The generic continuous quotient specializes definitionally to the original
full-adjoint deformation cohomology, including the same coboundary map. -/
def continuousMatrixAdjointH1GeneralEquiv
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) :
    ContinuousMatrixAdjointH1 ρ hρ ≃ₗ[R]
      ContinuousRepresentationH1 (matrixAdjointRep ρ) (matrixAdjointAction_continuous ρ hρ) :=
  LinearEquiv.refl R _

/-- The comparison preserves the exact cohomology class of the original
continuous first-order lift, with its actual right-logarithmic cocycle. -/
theorem continuousMatrixAdjointH1GeneralEquiv_firstOrder
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixAdjointH1GeneralEquiv ρ hρ (continuousMatrixFirstOrderClass ρ hρ τ hτ) =
      (Submodule.Quotient.mk
        (⟨matrixFirstOrderCocycle ρ τ, matrixFirstOrderCocycle_continuous ρ hρ τ hτ⟩ :
          continuousRepresentationCocyclesOne (matrixAdjointRep ρ)) :
        ContinuousRepresentationH1 (matrixAdjointRep ρ)
          (matrixAdjointAction_continuous ρ hρ)) := by
  rfl

section TraceZero

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k]

/-- The generic continuous quotient also specializes to the same original
trace-zero deformation cohomology, without changing its cocycle representatives. -/
def continuousTraceZeroH1GeneralEquiv
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ) :
    ContinuousTraceZeroAdjointH1 ρ hρ ≃ₗ[k]
      ContinuousRepresentationH1 (matrixTraceZeroAdjointRep ρ)
        (matrixTraceZeroAdjointAction_continuous ρ hρ) :=
  LinearEquiv.refl k _

/-- Every original trace-zero continuous cocycle has the same quotient class
under the actual comparison, including its original function and coboundaries. -/
theorem continuousTraceZeroH1GeneralEquiv_mk
    (ρ : G →* GeneralLinearGroup ι k) (hρ : Continuous ρ)
    (c : continuousTraceZeroAdjointCocycles ρ) :
    continuousTraceZeroH1GeneralEquiv ρ hρ (Submodule.Quotient.mk c) =
      (Submodule.Quotient.mk (⟨c.val, c.property⟩ :
        continuousRepresentationCocyclesOne (matrixTraceZeroAdjointRep ρ)) :
        ContinuousRepresentationH1 (matrixTraceZeroAdjointRep ρ)
          (matrixTraceZeroAdjointAction_continuous ρ hρ)) := by
  rfl

end TraceZero
end
end Dubon2026
