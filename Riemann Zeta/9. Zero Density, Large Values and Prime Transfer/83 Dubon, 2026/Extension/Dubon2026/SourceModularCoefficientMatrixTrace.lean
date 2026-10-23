import Dubon2026.SourceCurveLocalMatrixTrace
import Dubon2026.SourceModularCoefficientTateDifferentials

/-! Actual modular coefficient-field residues of matrix traces. This is the
matrix step required by integral-basis residue/field-trace comparison;
the integral basis and comparison across the fiber are still required. -/

noncomputable section

namespace Dubon2026.SourceFunctionField

open SourceCurve SourceCurve.ResidueTrace KaehlerDifferential

variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual canonical residue of a matrix trace is the finite integral commutator trace. -/
theorem coeff_canonicalResidue_matrix_trace
    (v : Place K (modularFunctionFieldCoeff N K))
    (s : modularFunctionFieldCoeff N K →ₗ[K] v.integralFunctions)
    (hs : ∀ a : v.integralFunctions, s a = a)
    (M : Matrix ι ι (modularFunctionFieldCoeff N K))
    (g : modularFunctionFieldCoeff N K) (hg : g ∈ v.toValuationSubring) :
    FiniteDimensional K (LinearMap.range
      (v.integralMatrixEnd s M ∘ₗ diagonalEnd
          (projectedEnd v.integralFunctions s (Algebra.lmul K (modularFunctionFieldCoeff N K) g)) -
        diagonalEnd (projectedEnd v.integralFunctions s
          (Algebra.lmul K (modularFunctionFieldCoeff N K) g)) ∘ₗ v.integralMatrixEnd s M)) ∧
    finrankTrace
      (v.integralMatrixEnd s M ∘ₗ diagonalEnd
          (projectedEnd v.integralFunctions s (Algebra.lmul K (modularFunctionFieldCoeff N K) g)) -
        diagonalEnd (projectedEnd v.integralFunctions s
          (Algebra.lmul K (modularFunctionFieldCoeff N K) g)) ∘ₗ v.integralMatrixEnd s M) =
      Algebra.trace K v.ResidueField ((coeffCanonicalLocalResidueData N K v).res
        (Matrix.trace M * v.differentialCoeff (D K (modularFunctionFieldCoeff N K) g))) := by
  obtain ⟨hfin, he⟩ := v.integralMatrixEnd_trace
    (coeff_place_residue_algebraMap_bijective N K v).surjective s hs M g hg
  exact ⟨hfin, he.trans (coeff_tateResidue_eq_canonical_differential N K v (Matrix.trace M) g)⟩

end Dubon2026.SourceFunctionField
