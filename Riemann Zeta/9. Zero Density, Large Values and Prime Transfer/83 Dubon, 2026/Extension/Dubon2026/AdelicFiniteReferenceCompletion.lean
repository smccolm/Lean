import Dubon2026.AdelicFiniteReferenceDiagram
import Dubon2026.AdelicFiniteTensorCompletion
import Dubon2026.LinearIsometryCompletionFunctor

/-! # Actual finite tensor reference diagrams remain exact after Hilbert completion -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix Matrix.SpecialLinearGroup CongruenceSubgroup UniformSpace
open scoped MatrixGroups TensorProduct

/-- Two genuine isometric realization routes agreeing on every original vector also agree on the actual completion. -/
theorem linearIsometryCompletion_compare {V W W' H : Type*}
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    [NormedAddCommGroup W'] [NormedSpace ℂ W'] [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (J : V →ₗᵢ[ℂ] W) (T : W →ₗᵢ[ℂ] H) (J' : V →ₗᵢ[ℂ] W') (T' : W' →ₗᵢ[ℂ] H)
    (h : ∀ x, T (J x) = T' (J' x)) (x : Completion V) :
    linearIsometryCompletion T (linearIsometryCompletionFunctor J x) =
      linearIsometryCompletion T' (linearIsometryCompletionFunctor J' x) := by
  have he : T.comp J = T'.comp J' := by
    ext y
    exact h y
  exact (linearIsometryCompletion_diagram J T (T.comp J) (fun _ => rfl) x).trans
    ((congrArg (fun S : V →ₗᵢ[ℂ] H => linearIsometryCompletion S x) he).trans
      (linearIsometryCompletion_diagram J' T' (T'.comp J') (fun _ => rfl) x).symm)

variable {N : ℕ} [NeZero N] {k : ℤ} {n : ℕ}
  (f : CuspForm ((Gamma0 N).map (mapGL ℝ)) k) (v : Fin (n + 1) → HeightOneSpectrum ℤ)

/-- The reference comparison uses the genuine completion of the common original tensor domain. -/
abbrev AdelicFiniteReferenceHilbertDomain := Completion (AdelicFiniteReferenceDomain f v)

/-- Complete the actual common-complement inclusion into the original shorter Hilbert tensor. -/
def adelicFiniteReferenceHilbertToShorter : AdelicFiniteReferenceHilbertDomain f v →ₗᵢ[ℂ]
    AdelicFiniteFullHilbertTensor f (fun i : Fin n => v i.castSucc) :=
  linearIsometryCompletionFunctor (adelicFiniteReferenceToShorter f v)

/-- Complete the genuine insertion of the original new local unit reference. -/
def adelicFiniteReferenceHilbertToLonger (hf : f ≠ 0) :
    AdelicFiniteReferenceHilbertDomain f v →ₗᵢ[ℂ] AdelicFiniteFullHilbertTensor f v :=
  linearIsometryCompletionFunctor (adelicFiniteReferenceToLonger f v hf)

variable (F : PrimitiveCuspForm N k)

/-- Appending the genuine original local unit reference preserves the original full adelic realization on every common Hilbert tensor vector. -/
theorem adelicFiniteHilbertTensorIsometry_reference_extension (hv : Function.Injective v)
    (hgood : ∀ i, IsGoodAdelicPlace N (v i)) (x : AdelicFiniteReferenceHilbertDomain F.toCuspForm v) :
    adelicFiniteFullHilbertTensorIsometry F (fun i : Fin n => v i.castSucc)
      (hv.comp (Fin.castSucc_injective n)) (fun i => hgood i.castSucc)
      (adelicFiniteReferenceHilbertToShorter F.toCuspForm v x) =
      adelicFiniteFullHilbertTensorIsometry F v hv hgood
        (adelicFiniteReferenceHilbertToLonger F.toCuspForm v (primitiveCuspForm_ne_zero F) x) :=
  @linearIsometryCompletion_compare (AdelicFiniteReferenceDomain F.toCuspForm v)
    (AdelicFiniteLocalTensor F.toCuspForm (fun i : Fin n => v i.castSucc) ⊗[ℂ]
      adelicFiniteFamilyAwayCore F.toCuspForm (fun i : Fin n => v i.castSucc))
    (AdelicFiniteLocalTensor F.toCuspForm v ⊗[ℂ] adelicFiniteFamilyAwayCore F.toCuspForm v)
    (AdelicCyclicHilbert F.toCuspForm)
    inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
    (adelicFiniteReferenceToShorter F.toCuspForm v)
    (adelicFiniteFullTensorIsometry F (fun i : Fin n => v i.castSucc)
      (hv.comp (Fin.castSucc_injective n)) (fun i => hgood i.castSucc))
    (adelicFiniteReferenceToLonger F.toCuspForm v (primitiveCuspForm_ne_zero F))
    (adelicFiniteFullTensorIsometry F v hv hgood)
    (adelicFiniteTensorIsometry_reference_extension v F hv hgood) x

end
end Dubon2026
