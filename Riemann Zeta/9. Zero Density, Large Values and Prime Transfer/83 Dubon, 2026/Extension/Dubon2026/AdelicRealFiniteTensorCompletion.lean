import Dubon2026.AdelicRealFiniteTensorRange
import Dubon2026.LinearIsometryCompletion

/-! # The genuine real/finite Hilbert tensor equals the entire original adelic space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix.SpecialLinearGroup CongruenceSubgroup UniformSpace
open scoped MatrixGroups

variable {N : ℕ} [NeZero N] {k : ℤ} (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)

/-- The actual Hilbert completion of the original real and finite core tensor. -/
abbrev AdelicRealFiniteHilbertTensor := Completion (AdelicRealFiniteTensor f)

/-- The genuine original real/finite tensor map extended continuously to its Hilbert completion. -/
def adelicRealFiniteHilbertTensorIsometry (hf : f ≠ 0) (hk : 0 < k) :
    AdelicRealFiniteHilbertTensor f →ₗᵢ[ℂ] AdelicCyclicHilbert f :=
  @linearIsometryCompletion (AdelicRealFiniteTensor f) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicRealFiniteTensorIsometry f hf hk)

/-- Completion retains every genuine original algebraic tensor vector. -/
theorem adelicRealFiniteHilbertTensorIsometry_coe (hf : f ≠ 0) (hk : 0 < k) (x : AdelicRealFiniteTensor f) :
    adelicRealFiniteHilbertTensorIsometry f hf hk (x : AdelicRealFiniteHilbertTensor f) =
      adelicRealFiniteTensorIsometry f hf hk x :=
  linearIsometryCompletion_coe _ x

/-- The actual completed real/finite tensor map covers the entire original adelic Hilbert space. -/
theorem adelicRealFiniteHilbertTensorIsometry_range (hf : f ≠ 0) (hk : 0 < k) :
    (adelicRealFiniteHilbertTensorIsometry f hf hk).toLinearMap.range = ⊤ :=
  (@linearIsometryCompletion_range (AdelicRealFiniteTensor f) (AdelicCyclicHilbert f)
    inferInstance inferInstance inferInstance inferInstance inferInstance (adelicRealFiniteTensorIsometry f hf hk)).trans
    (adelicRealFiniteTensorIsometry_range_closure f hf hk)

/-- The genuine real and finite Hilbert tensor is isometrically equivalent to the full original adelic cusp space. -/
def adelicRealFiniteHilbertTensorEquiv (hf : f ≠ 0) (hk : 0 < k) :
    AdelicRealFiniteHilbertTensor f ≃ₗᵢ[ℂ] AdelicCyclicHilbert f :=
  (adelicRealFiniteHilbertTensorIsometry f hf hk).equivRange.trans
    (LinearIsometryEquiv.ofTop _ _ (adelicRealFiniteHilbertTensorIsometry_range f hf hk))

/-- The genuine completed equivalence has exactly the original tensor realization as its value. -/
theorem adelicRealFiniteHilbertTensorEquiv_apply (hf : f ≠ 0) (hk : 0 < k)
    (x : AdelicRealFiniteHilbertTensor f) :
    adelicRealFiniteHilbertTensorEquiv f hf hk x = adelicRealFiniteHilbertTensorIsometry f hf hk x := rfl

end
end Dubon2026
