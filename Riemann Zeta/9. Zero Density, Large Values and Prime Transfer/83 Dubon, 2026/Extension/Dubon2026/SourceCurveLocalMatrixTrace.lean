import Dubon2026.SourceCurveMatrixCommutatorTrace
import Dubon2026.SourceCurveLocalRetractionTrace
import Dubon2026.SourceCurveLocalTateDerivation

/-! The integral-basis matrix step of residue/field-trace compatibility.
Local principal parts prove finiteness of every entry commutator. Thus the
matrix commutator computes the residue of the literal matrix trace.
The eventual field-trace consumer still has to construct the integral basis
and identify its multiplication matrix over the actual extension. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open ResidueTrace LinearMap

variable {K F ι : Type*} [Field K] [Field F] [Algebra K F]
  [Fintype ι] [DecidableEq ι] (v : Place K F)

/-- A matrix acting on integral coordinates through an actual integral retraction. -/
def integralMatrixEnd (s : F →ₗ[K] v.integralFunctions) (M : Matrix ι ι F) :
    (ι → v.integralFunctions) →ₗ[K] (ι → v.integralFunctions) :=
  blockEnd (fun i j => projectedEnd v.integralFunctions s (Algebra.lmul K F (M i j)))

/-- The finite commutator of integral-coordinate matrices computes the residue of their trace. -/
theorem integralMatrixEnd_trace
    (hres : Function.Surjective (algebraMap K v.ResidueField))
    (s : F →ₗ[K] v.integralFunctions) (hs : ∀ a : v.integralFunctions, s a = a)
    (M : Matrix ι ι F) (g : F) (hg : g ∈ v.toValuationSubring) :
    FiniteDimensional K (LinearMap.range
      (v.integralMatrixEnd s M ∘ₗ diagonalEnd (projectedEnd v.integralFunctions s (Algebra.lmul K F g)) -
        diagonalEnd (projectedEnd v.integralFunctions s (Algebra.lmul K F g)) ∘ₗ
          v.integralMatrixEnd s M)) ∧
    finrankTrace
      (v.integralMatrixEnd s M ∘ₗ diagonalEnd (projectedEnd v.integralFunctions s (Algebra.lmul K F g)) -
        diagonalEnd (projectedEnd v.integralFunctions s (Algebra.lmul K F g)) ∘ₗ
          v.integralMatrixEnd s M) = v.tateResidue (Matrix.trace M) g := by
  let T := fun i j => projectedEnd v.integralFunctions s (Algebra.lmul K F (M i j))
  let u := projectedEnd v.integralFunctions s (Algebra.lmul K F g)
  have ht (i j : ι) := v.tateResidue_eq_retraction_trace hres s hs (M i j) g hg
  haveI : ∀ i j, FiniteDimensional K (LinearMap.range (T i j ∘ₗ u - u ∘ₗ T i j)) :=
    fun i j => (ht i j).1
  obtain ⟨hfin, htrace⟩ := blockEnd_commutator_trace T u
  refine ⟨hfin, htrace.trans ?_⟩
  calc ∑ i, finrankTrace (T i i ∘ₗ u - u ∘ₗ T i i) = ∑ i, v.tateResidue (M i i) g :=
      Finset.sum_congr rfl (fun i _ => (ht i i).2.symm)
    _ = v.tateResidue (Matrix.trace M) g := by
      exact (map_sum (residueDualLinearMap K F (v.tateResidueFunctional hres g))
        (fun i => M i i) Finset.univ).symm

end Dubon2026.SourceCurve.Place
