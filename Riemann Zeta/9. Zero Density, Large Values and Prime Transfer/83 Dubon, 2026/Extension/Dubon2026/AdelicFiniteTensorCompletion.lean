import Dubon2026.AdelicFiniteTensorRange
import Dubon2026.LinearIsometryCompletion

/-! # The genuine finite-family Hilbert tensor is the entire original full adelic cusp Hilbert space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UniformSpace
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}

/-- The actual Hilbert completion of the original finite local/full-complement algebraic tensor. -/
abbrev AdelicFiniteFullHilbertTensor (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
    (v : Fin n → HeightOneSpectrum ℤ) :=
  Completion (AdelicFiniteLocalTensor f v ⊗[ℂ] adelicFiniteFamilyAwayCore f v)

variable (F : PrimitiveCuspForm N k) (v : Fin n → HeightOneSpectrum ℤ) (hv : Function.Injective v)

/-- The genuine finite-family tensor isometry extended to the actual Hilbert tensor completion. -/
def adelicFiniteFullHilbertTensorIsometry (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    AdelicFiniteFullHilbertTensor F.toCuspForm v →ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  @linearIsometryCompletion
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v)
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteFullTensorIsometry F v hv hgood)

/-- The genuine completed map agrees with its original finite algebraic tensor map on every vector. -/
theorem adelicFiniteFullHilbertTensorIsometry_coe (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (x : AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v) :
    adelicFiniteFullHilbertTensorIsometry F v hv hgood (x : AdelicFiniteFullHilbertTensor F.toCuspForm v) =
      adelicFiniteFullTensorIsometry F v hv hgood x :=
  linearIsometryCompletion_coe _ x

/-- Every original finite pure orbit tensor retains its exact genuine full adelic orbit image in the Hilbert completion. -/
theorem adelicFiniteFullHilbertTensorIsometry_family (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (a : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    adelicFiniteFullHilbertTensorIsometry F v hv hgood
      (adelicFiniteFullTensorFamily F.toCuspForm v a : AdelicFiniteFullHilbertTensor F.toCuspForm v) =
      adelicFiniteFullMixedFamily F.toCuspForm v hv a :=
  (adelicFiniteFullHilbertTensorIsometry_coe F v hv hgood _).trans
    (adelicFiniteFullTensorIsometry_family F v hv hgood a)

/-- The actual completed finite-family tensor map has the entire original full adelic Hilbert space as its range. -/
theorem adelicFiniteFullHilbertTensorIsometry_range (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    (adelicFiniteFullHilbertTensorIsometry F v hv hgood).toLinearMap.range = ⊤ :=
  (@linearIsometryCompletion_range
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v)
    (AdelicCyclicHilbert F.toCuspForm) inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteFullTensorIsometry F v hv hgood)).trans
    (adelicFiniteFullTensorIsometry_range_closure F v hv hgood)

/-- The genuine finite local/full-complement Hilbert tensor is isometrically equivalent to the entire original full adelic cusp Hilbert space. -/
def adelicFiniteFullHilbertTensorEquiv (hgood : ∀ i, IsGoodAdelicPlace N (v i)) :
    AdelicFiniteFullHilbertTensor F.toCuspForm v ≃ₗᵢ[ℂ] AdelicCyclicHilbert F.toCuspForm :=
  (adelicFiniteFullHilbertTensorIsometry F v hv hgood).equivRange.trans
    (LinearIsometryEquiv.ofTop _ _ (adelicFiniteFullHilbertTensorIsometry_range F v hv hgood))

/-- The actual finite-family Hilbert equivalence retains the literal original completed tensor map. -/
theorem adelicFiniteFullHilbertTensorEquiv_apply (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (x : AdelicFiniteFullHilbertTensor F.toCuspForm v) :
    adelicFiniteFullHilbertTensorEquiv F v hv hgood x =
      adelicFiniteFullHilbertTensorIsometry F v hv hgood x := rfl

end
end Dubon2026
