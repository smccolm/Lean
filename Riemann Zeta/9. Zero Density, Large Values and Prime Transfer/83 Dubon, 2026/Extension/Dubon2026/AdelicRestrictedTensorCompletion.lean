import Dubon2026.AdelicRestrictedTensorDensity
import Dubon2026.LinearIsometryCompletion

/-! # Completion of the genuine restricted tensor is the entire original adelic Hilbert space -/

namespace Dubon2026

noncomputable section
open UniformSpace

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- The Hilbert completion of the genuine finite-stage restricted tensor quotient, with its descended original tensor norm. -/
abbrev AdelicRestrictedHilbertTensor := Completion (AdelicRestrictedAlgebraicTensor F)

/-- The true restricted Hilbert tensor retains the original adelic isometric realization. -/
def adelicRestrictedHilbertTensorIsometry :
    AdelicRestrictedHilbertTensor F →ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  @linearIsometryCompletion (AdelicRestrictedAlgebraicTensor F) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicRestrictedAlgebraicTensorIsometry F)

/-- Completion preserves every actual finite-stage original tensor vector exactly. -/
theorem adelicRestrictedHilbertTensorIsometry_of (n : ℕ) (x : adelicRestrictedStage F.toCuspForm n) :
    adelicRestrictedHilbertTensorIsometry F ((adelicRestrictedTensorOf F n x : AdelicRestrictedAlgebraicTensor F) :
      AdelicRestrictedHilbertTensor F) = adelicRestrictedStageIsometry F n x :=
  (@linearIsometryCompletion_coe (AdelicRestrictedAlgebraicTensor F) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicRestrictedAlgebraicTensorIsometry F)
    (adelicRestrictedTensorOf F n x)).trans (adelicRestrictedAlgebraicTensorIsometry_of F n x)

/-- The actual completed restricted tensor realizes the whole original adelic Hilbert space. -/
theorem adelicRestrictedHilbertTensorIsometry_range :
    (adelicRestrictedHilbertTensorIsometry F).toLinearMap.range = ⊤ :=
  (@linearIsometryCompletion_range (AdelicRestrictedAlgebraicTensor F) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicRestrictedAlgebraicTensorIsometry F)).trans
    (adelicRestrictedAlgebraicTensorIsometry_range_closure F)

/-- The genuine restricted Hilbert tensor is isometrically equivalent to the entire original adelic cusp Hilbert space. -/
def adelicRestrictedHilbertTensorEquiv :
    AdelicRestrictedHilbertTensor F ≃ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  (adelicRestrictedHilbertTensorIsometry F).equivRange.trans
    (LinearIsometryEquiv.ofTop _ _ (adelicRestrictedHilbertTensorIsometry_range F))

/-- The completed genuine tensor equivalence uses exactly the original adelic realization. -/
theorem adelicRestrictedHilbertTensorEquiv_apply (x : AdelicRestrictedHilbertTensor F) :
    adelicRestrictedHilbertTensorEquiv F x = adelicRestrictedHilbertTensorIsometry F x := rfl

end
end Dubon2026
