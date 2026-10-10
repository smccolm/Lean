import Dubon2026.ContinuousAdjointCohomology
import Dubon2026.FixedDeterminantFirstOrderLift

/-! # Actual fixed-determinant classes in original continuous adjoint cohomology -/

namespace Dubon2026

noncomputable section
open Matrix

variable {G ι R : Type} [Group G] [Fintype ι] [DecidableEq ι] [CommRing R]
  [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace R] [IsTopologicalRing R]

/-- The actual pointwise trace of the original continuous adjoint cocycle, as a coefficient-linear map into original scalar-valued functions. -/
def continuousMatrixAdjointTrace (ρ : G →* GeneralLinearGroup ι R) :
    continuousMatrixAdjointCocycles ρ →ₗ[R] (G → R) where
  toFun c g := Matrix.trace (c.val g)
  map_add' c d := by
    funext g
    exact Matrix.trace_add (c.val g) (d.val g)
  map_smul' r c := by
    funext g
    exact Matrix.trace_smul r (c.val g)

omit [IsTopologicalGroup G] in
/-- The original continuous adjoint coboundaries have identically zero actual trace. -/
theorem continuousMatrixAdjointTrace_coboundary
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) (X : Matrix ι ι R) :
    continuousMatrixAdjointTrace ρ (continuousMatrixAdjointCoboundary ρ hρ X) = 0 := by
  funext g
  exact matrixAdjointCoboundary_trace_zero ρ X g

/-- The actual trace map on original continuous adjoint H1, descended using genuine trace-zero coboundaries. -/
def continuousMatrixAdjointH1Trace
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) :
    ContinuousMatrixAdjointH1 ρ hρ →ₗ[R] (G → R) := by
  have hb : continuousMatrixAdjointCoboundaries ρ hρ ≤ (continuousMatrixAdjointTrace ρ).ker := by
    rintro _ ⟨X, rfl⟩
    exact continuousMatrixAdjointTrace_coboundary ρ hρ X
  let traceMap := Submodule.liftQ (R := R) (R₂ := R)
    (M := continuousMatrixAdjointCocycles ρ) (M₂ := G → R) (τ₁₂ := RingHom.id R)
    (continuousMatrixAdjointCoboundaries ρ hρ) (continuousMatrixAdjointTrace ρ) hb
  exact traceMap

/-- The actual fixed-determinant submodule of original continuous adjoint classes is the kernel of their genuine descended trace. -/
def continuousFixedDeterminantClasses
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ) :
    Submodule R (ContinuousMatrixAdjointH1 ρ hρ) :=
  (continuousMatrixAdjointH1Trace ρ hρ).ker

omit [IsTopologicalGroup G] in
/-- The trace of an original first-order class is the original pointwise trace of that lifted representation's actual adjoint cocycle. -/
theorem continuousMatrixAdjointH1Trace_firstOrder
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) (g : G) :
    continuousMatrixAdjointH1Trace ρ hρ (continuousMatrixFirstOrderClass ρ hρ τ hτ) g =
      Matrix.trace (matrixFirstOrderCocycle ρ τ g) := rfl

omit [IsTopologicalGroup G] in
/-- An original continuous first-order lift class is in the actual trace-kernel submodule exactly when its whole lifted determinant is the original constant dual-number lift of the residual determinant. No characteristic-dependent identification with trace-zero coefficient cohomology is assumed. -/
theorem continuousFixedDeterminantClasses_firstOrder_iff
    (ρ : G →* GeneralLinearGroup ι R) (hρ : Continuous ρ)
    (τ : MatrixFirstOrderLift ρ) (hτ : Continuous τ.val) :
    continuousMatrixFirstOrderClass ρ hρ τ hτ ∈ continuousFixedDeterminantClasses ρ hρ ↔
      ∀ g, Matrix.det (τ.val g).val = TrivSqZeroExt.inl (Matrix.det (ρ g).val) := by
  change (fun g => Matrix.trace (matrixFirstOrderCocycle ρ τ g)) = 0 ↔ _
  rw [funext_iff]
  exact (matrixFirstOrderLift_fixedDeterminant_iff ρ τ).symm

end
end Dubon2026
