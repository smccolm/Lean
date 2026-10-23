import Dubon2026.SourceCurveLocalRetractionTrace
import Dubon2026.SourceModularCoefficientTateDifferentials

/-! The actual canonical modular-field residue can be computed with any
integral retraction when the differentiated function is integral. This is
the precise interface for an integral-basis trace calculation in the
remaining residue/field-trace compatibility step of DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve SourceCurve.ResidueTrace KaehlerDifferential

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]

/-- The actual canonical residue is unchanged by replacing its local integral projection. -/
theorem coeff_canonicalResidue_retraction_trace
    (v : Place K (modularFunctionFieldCoeff N K))
    (s : modularFunctionFieldCoeff N K →ₗ[K] v.integralFunctions)
    (hs : ∀ a : v.integralFunctions, s a = a) (f g : modularFunctionFieldCoeff N K)
    (hg : g ∈ v.toValuationSubring) :
    FiniteDimensional K (LinearMap.range
      (projectedEnd v.integralFunctions s (Algebra.lmul K (modularFunctionFieldCoeff N K) f) ∘ₗ
          projectedEnd v.integralFunctions s (Algebra.lmul K (modularFunctionFieldCoeff N K) g) -
        projectedEnd v.integralFunctions s (Algebra.lmul K (modularFunctionFieldCoeff N K) g) ∘ₗ
          projectedEnd v.integralFunctions s (Algebra.lmul K (modularFunctionFieldCoeff N K) f))) ∧
    Algebra.trace K v.ResidueField ((coeffCanonicalLocalResidueData N K v).res
        (f * v.differentialCoeff (D K (modularFunctionFieldCoeff N K) g))) =
      finrankTrace
        (projectedEnd v.integralFunctions s (Algebra.lmul K (modularFunctionFieldCoeff N K) f) ∘ₗ
            projectedEnd v.integralFunctions s (Algebra.lmul K (modularFunctionFieldCoeff N K) g) -
          projectedEnd v.integralFunctions s (Algebra.lmul K (modularFunctionFieldCoeff N K) g) ∘ₗ
            projectedEnd v.integralFunctions s (Algebra.lmul K (modularFunctionFieldCoeff N K) f)) := by
  obtain ⟨hfin, ht⟩ := v.tateResidue_eq_retraction_trace
    (coeff_place_residue_algebraMap_bijective N K v).surjective s hs f g hg
  exact ⟨hfin, (coeff_tateResidue_eq_canonical_differential N K v f g).symm.trans ht⟩

end Dubon2026.SourceFunctionField
