import Dubon2026.AdelicSplitTensorDensity
import Dubon2026.LinearIsometryCompletion

/-! # The full restricted Hilbert tensor of the original local factors -/

namespace Dubon2026

noncomputable section
open UniformSpace

variable {N : ℕ} [NeZero N] {k : ℤ} (F : PrimitiveCuspForm N k)

/-- The genuine Hilbert completion of the fully split local tensor with its independent product norm. -/
abbrev AdelicSplitHilbertTensor := Completion (AdelicSplitAlgebraicTensor F)

/-- The full restricted tensor of original finite and real factors maps isometrically to the original cusp Hilbert space. -/
def adelicSplitHilbertTensorIsometry (hk : 0 < k) :
    AdelicSplitHilbertTensor F →ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  @linearIsometryCompletion (AdelicSplitAlgebraicTensor F) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicSplitAlgebraicTensorIsometry F hk)

/-- Completion retains every actual finite tensor and its original adelic realization. -/
theorem adelicSplitHilbertTensorIsometry_of (hk : 0 < k) (n : ℕ)
    (x : adelicSplitStage F.toCuspForm n) :
    adelicSplitHilbertTensorIsometry F hk ((adelicSplitTensorOf F n x : AdelicSplitAlgebraicTensor F) :
      AdelicSplitHilbertTensor F) = adelicSplitStageIsometry F hk n x :=
  (@linearIsometryCompletion_coe (AdelicSplitAlgebraicTensor F) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicSplitAlgebraicTensorIsometry F hk) (adelicSplitTensorOf F n x)).trans
    (adelicSplitAlgebraicTensorIsometry_of F hk n x)

/-- The genuine completed product of individual local factors realizes the entire original Hilbert space. -/
theorem adelicSplitHilbertTensorIsometry_range (hk : 0 < k) :
    (adelicSplitHilbertTensorIsometry F hk).toLinearMap.range = ⊤ :=
  (@linearIsometryCompletion_range (AdelicSplitAlgebraicTensor F) (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicSplitAlgebraicTensorIsometry F hk)).trans
    (adelicSplitAlgebraicTensorIsometry_range_closure F hk)

/-- The independently constructed restricted product of all original local factors is the original adelic cusp Hilbert space. -/
def adelicSplitHilbertTensorEquiv (hk : 0 < k) :
    AdelicSplitHilbertTensor F ≃ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  (adelicSplitHilbertTensorIsometry F hk).equivRange.trans
    (LinearIsometryEquiv.ofTop _ _ (adelicSplitHilbertTensorIsometry_range F hk))

/-- The full tensor equivalence is exactly the proved original completed realization. -/
theorem adelicSplitHilbertTensorEquiv_apply (hk : 0 < k) (x : AdelicSplitHilbertTensor F) :
    adelicSplitHilbertTensorEquiv F hk x = adelicSplitHilbertTensorIsometry F hk x := rfl

end
end Dubon2026
