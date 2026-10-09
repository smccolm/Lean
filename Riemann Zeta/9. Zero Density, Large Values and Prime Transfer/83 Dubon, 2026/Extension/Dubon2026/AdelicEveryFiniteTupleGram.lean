import Dubon2026.AdelicEveryFiniteTupleCoefficients
import Dubon2026.AdelicFiniteTupleGram

/-! # Actual finite-family tensor Gram identity including all bad places -/

namespace Dubon2026

noncomputable section
open IsDedekindDomain Matrix

variable {N : ℕ} [NeZero N] {k : ℤ}

variable {I : Type*} [Fintype I] (v : I → HeightOneSpectrum ℤ) (hv : Function.Injective v)
  (F : PrimitiveCuspForm N k)

/-- The entire genuine finite-family mixed Gram matrix is the product of its original local Gram matrices and its full remaining-coordinate Gram matrix. -/
theorem adelicCyclicUnitReference_every_finiteFamily_gram
    (hk : 0 < k)
    (b₁ b₂ : (∀ i, GeneralLinearGroup (Fin 2) ((v i).adicCompletion ℚ)) × adelicFiniteFamilyAwayGroup v) :
    inner ℂ
      (adelicCyclicHilbertRepresentation F.toCuspForm (adelicFiniteFamilyEquiv v hv b₁)
        (adelicCyclicUnitReference F.toCuspForm))
      (adelicCyclicHilbertRepresentation F.toCuspForm (adelicFiniteFamilyEquiv v hv b₂)
        (adelicCyclicUnitReference F.toCuspForm)) =
      (∏ i, inner ℂ
        (adelicCyclicHilbertRepresentation F.toCuspForm
          (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b₁.1 i)))
          (adelicCyclicUnitReference F.toCuspForm))
        (adelicCyclicHilbertRepresentation F.toCuspForm
          (rationalAdelicFiniteGL2Embedding (finiteAdelicLocalGL2 (v i) (b₂.1 i)))
          (adelicCyclicUnitReference F.toCuspForm))) *
      inner ℂ
        (adelicCyclicHilbertRepresentation F.toCuspForm b₁.2.val (adelicCyclicUnitReference F.toCuspForm))
        (adelicCyclicHilbertRepresentation F.toCuspForm b₂.2.val (adelicCyclicUnitReference F.toCuspForm)) := by
  have he := groupHom_relative (adelicFiniteFamilyEquiv v hv).toMonoidHom b₁ b₂
  have h := adelicNormalizedCuspCoefficient_every_finiteFamilyEquiv v hv F hk (b₁⁻¹ * b₂)
  have hleft := adelicCyclicUnitReference_orbit_inner F.toCuspForm
    (adelicFiniteFamilyEquiv v hv b₁) (adelicFiniteFamilyEquiv v hv b₂)
  apply hleft.trans ((congrArg (adelicNormalizedCuspCoefficient F.toCuspForm) he.symm).trans (h.trans _))
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro i _
    have hi := groupHom_relative
      (rationalAdelicFiniteGL2Embedding.comp (finiteAdelicLocalGL2Hom (v i))) (b₁.1 i) (b₂.1 i)
    exact (congrArg (adelicNormalizedCuspCoefficient F.toCuspForm) hi).trans
      (adelicCyclicUnitReference_orbit_inner F.toCuspForm _ _).symm
  · exact (congrArg (adelicNormalizedCuspCoefficient F.toCuspForm)
      (groupHom_relative (adelicFiniteFamilyAwayGroup v).subtype b₁.2 b₂.2)).trans
      (adelicCyclicUnitReference_orbit_inner F.toCuspForm _ _).symm

end
end Dubon2026
