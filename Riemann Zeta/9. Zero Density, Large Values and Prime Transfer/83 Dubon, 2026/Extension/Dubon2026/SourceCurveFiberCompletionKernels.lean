import Dubon2026.SourceCurveCompletionSpectralNorm
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! Distinct original places give distinct maximal component kernels in
the completed tensor algebra. A map between components fixing original
elements preserves their minimal polynomials and hence the native spectral
norm, which recovers the original valuation rings. This supplies the
Chinese-remainder input for the DUB-17/18 global trace sum. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open scoped TensorProduct Valued

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] [FiniteDimensional F E] (v : Place K F)

/-- A base-completion map fixing the original field identifies the actual fiber places. -/
theorem fiberCompletion_eq_of_algHom (w z : {w : Place K E // w.restrict F = v})
    (σ : w.1.adicCompletion →ₐ[v.adicCompletion] z.1.adicCompletion)
    (hσ : ∀ g : E, σ (algebraMap E w.1.adicCompletion g) = algebraMap E z.1.adicCompletion g) :
    w = z := by
  letI := v.completionRankOne
  have hnorm (y : w.1.adicCompletion) :
      spectralNorm v.adicCompletion z.1.adicCompletion (σ y) =
        spectralNorm v.adicCompletion w.1.adicCompletion y := by
    unfold spectralNorm
    congr 1
    exact minpoly.algHom_eq σ σ.toRingHom.injective y
  apply Subtype.ext
  apply Place.ext
  apply SetLike.ext
  intro g
  rw [← fiberCompletion_spectralNorm_le_one_iff v w g,
    ← fiberCompletion_spectralNorm_le_one_iff v z g, ← hσ g, hnorm]

/-- Distinct places over the same base place have distinct tensor-component kernels. -/
theorem fiberCompletionComponent_ker_ne
    (w z : {w : Place K E // w.restrict F = v}) (h : w ≠ z) :
    RingHom.ker (v.fiberCompletionComponent w).toRingHom ≠
      RingHom.ker (v.fiberCompletionComponent z).toRingHom := by
  intro heq
  let σ := AlgHom.liftOfSurjective (v.fiberCompletionComponent w)
    (v.fiberCompletionComponent_surjective w) (v.fiberCompletionComponent z) heq.le
  apply h
  apply v.fiberCompletion_eq_of_algHom w z σ
  intro g
  have hσ := AlgHom.liftOfSurjective_apply (v.fiberCompletionComponent w)
    (v.fiberCompletionComponent_surjective w) (v.fiberCompletionComponent z) heq.le
    ((1 : v.adicCompletion) ⊗ₜ[F] g)
  simpa only [fiberCompletionComponent_tmul, map_one, one_mul] using hσ

end Dubon2026.SourceCurve.Place
