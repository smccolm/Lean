import Dubon2026.SourceCurveCompletionEmbedding
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! The actual extension completion is finite-dimensional over the actual
base completion. The original finite basis has dense span after completing;
native finite-dimensional closedness makes that span all of the completion.
This discharges the finite-degree input to its integral basis and local
field-trace comparison, on the DUB-17/18 reverse-genus dependency path. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open WithZero Topology
open scoped NNReal

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- Completed scalar multiplication preserves the original scalar multiplication. -/
theorem completion_algebraMap_smul (c : F) (b : E) :
    algebraMap F (w.restrict F).adicCompletion c • algebraMap E w.adicCompletion b =
      algebraMap E w.adicCompletion (c • b) := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply F E w.adicCompletion]

/-- Linear combinations of the actual original basis in the extension completion. -/
def completionLinearCombination {ι : Type*} [Fintype ι] (b : Module.Basis ι F E) :
    (ι → (w.restrict F).adicCompletion) →ₗ[(w.restrict F).adicCompletion] w.adicCompletion :=
  Fintype.linearCombination (w.restrict F).adicCompletion
    (fun i => algebraMap E w.adicCompletion (b i))

/-- The original basis has dense span over the completed base field. -/
theorem denseRange_completionLinearCombination {ι : Type*} [Fintype ι]
    (b : Module.Basis ι F E) : DenseRange (w.completionLinearCombination b) := by
  apply (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap E w.heightOneSpectrum).mono
  rintro _ ⟨x, rfl⟩
  refine ⟨fun i => algebraMap F (w.restrict F).adicCompletion (b.repr x i), ?_⟩
  simp only [completionLinearCombination, Fintype.linearCombination_apply,
    w.completion_algebraMap_smul, ← map_sum]
  congr 1
  exact b.sum_repr x

/-- The original basis spans the whole extension completion over the completed base. -/
theorem completionLinearCombination_surjective {ι : Type*} [Fintype ι]
    (b : Module.Basis ι F E) : Function.Surjective (w.completionLinearCombination b) := by
  let v := w.restrict F
  letI := v.completionValuation_nontrivial
  letI : (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).RankOne :=
    Valuation.IsRankOneDiscrete.rankOne _ (one_lt_two (α := ℝ≥0))
  letI : NontriviallyNormedField v.adicCompletion :=
    Valued.toNontriviallyNormedField v.adicCompletion ℤᵐ⁰
  rw [← Set.range_eq_univ, ← LinearMap.coe_range,
    ← (LinearMap.range (w.completionLinearCombination b)).closed_of_finiteDimensional.closure_eq]
  exact (w.denseRange_completionLinearCombination b).closure_range

/-- Completing a finite extension gives a finite extension of the actual completed base. -/
theorem finiteDimensional_completion [FiniteDimensional F E] :
    FiniteDimensional (w.restrict F).adicCompletion w.adicCompletion :=
  Module.Finite.of_surjective (w.completionLinearCombination (Module.finBasis F E))
    (w.completionLinearCombination_surjective (Module.finBasis F E))

end Dubon2026.SourceCurve.Place
