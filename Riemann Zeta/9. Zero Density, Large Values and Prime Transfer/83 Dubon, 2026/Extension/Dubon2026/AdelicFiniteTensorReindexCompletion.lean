import Dubon2026.AdelicFiniteTensorReindex
import Dubon2026.AdelicFiniteTensorCompletion
import Dubon2026.LinearIsometryCompletionFunctor

/-! # Completed genuine tensor permutations preserve the original full adelic Hilbert space -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup
open scoped MatrixGroups TensorProduct

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k)
  (v : Fin n → HeightOneSpectrum ℤ) (e : Equiv.Perm (Fin n))

/-- The completion of the genuine finite tensor permutation retains the original Hilbert tensor norm. -/
def adelicFiniteFullHilbertTensorReindex :
    AdelicFiniteFullHilbertTensor f (fun i => v (e i)) →ₗᵢ[ℂ] AdelicFiniteFullHilbertTensor f v :=
  linearIsometryCompletionFunctor (adelicFiniteFullTensorReindex f v e)

/-- The completed permutation extends exactly the genuine algebraic tensor permutation. -/
theorem adelicFiniteFullHilbertTensorReindex_coe
    (x : AdelicFiniteLocalTensor f (fun i => v (e i)) ⊗[ℂ] adelicFiniteFamilyAwayCore f (fun i => v (e i))) :
    adelicFiniteFullHilbertTensorReindex f v e (x : AdelicFiniteFullHilbertTensor f (fun i => v (e i))) =
      (adelicFiniteFullTensorReindex f v e x : AdelicFiniteFullHilbertTensor f v) :=
  linearIsometryCompletionFunctor_coe (adelicFiniteFullTensorReindex f v e) x

variable (F : PrimitiveCuspForm N k)

/-- Every genuine completed finite tensor permutation preserves exactly its original full adelic Hilbert realization. -/
theorem adelicFiniteFullHilbertTensorIsometry_reindex (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i))
    (x : AdelicFiniteFullHilbertTensor F.toCuspForm (fun i => v (e i))) :
    adelicFiniteFullHilbertTensorIsometry F v hv hgood (adelicFiniteFullHilbertTensorReindex F.toCuspForm v e x) =
      adelicFiniteFullHilbertTensorIsometry F (fun i => v (e i)) (hv.comp e.injective) (fun i => hgood (e i)) x :=
  @linearIsometryCompletion_diagram
    (AdelicFiniteLocalTensor F.toCuspForm (fun i => v (e i)) ⊗[ℂ]
      adelicFiniteFamilyAwayCore F.toCuspForm (fun i => v (e i)))
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v)
    (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteFullTensorReindex F.toCuspForm v e)
    (adelicFiniteFullTensorIsometry F v hv hgood)
    (adelicFiniteFullTensorIsometry F (fun i => v (e i)) (hv.comp e.injective) (fun i => hgood (e i)))
    (adelicFiniteFullTensorIsometry_reindex v e F hv hgood) x

end
end Dubon2026
