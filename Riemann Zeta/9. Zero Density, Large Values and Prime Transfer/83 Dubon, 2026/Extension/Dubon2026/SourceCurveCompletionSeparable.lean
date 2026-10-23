import Dubon2026.SourceCurveCompletionFinite
import Mathlib.FieldTheory.SeparableClosure

/-! Separability of the actual completion extension follows directly from
the completed spanning basis and the native separable closure. This avoids
first constructing a semilocal tensor decomposition solely to prove local
separability. It supplies the separability input to integral-basis finiteness
for the residue/field-trace comparison, hence the DUB-17/18 reverse-genus path. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- The image of a separable original element remains separable over the completed base. -/
theorem isSeparable_algebraMap_completion [Algebra.IsSeparable F E] (g : E) :
    IsSeparable (w.restrict F).adicCompletion (algebraMap E w.adicCompletion g) := by
  have hroot : Polynomial.aeval (R := (w.restrict F).adicCompletion)
      (algebraMap E w.adicCompletion g)
      ((minpoly F g).map (algebraMap F (w.restrict F).adicCompletion)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap,
      show algebraMap E w.adicCompletion g = IsScalarTower.toAlgHom F E w.adicCompletion g from rfl,
      Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  exact (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable F g)).of_dvd
    (minpoly.dvd (w.restrict F).adicCompletion _ hroot)

/-- Every element of the actual completed finite extension is separable. -/
theorem isSeparable_completion [FiniteDimensional F E] [Algebra.IsSeparable F E] :
    Algebra.IsSeparable (w.restrict F).adicCompletion w.adicCompletion := by
  refine ⟨fun x => ?_⟩
  let b := Module.finBasis F E
  obtain ⟨c, rfl⟩ := w.completionLinearCombination_surjective b x
  let S := separableClosure (w.restrict F).adicCompletion w.adicCompletion
  apply mem_separableClosure_iff.mp
  change w.completionLinearCombination b c ∈ S
  rw [completionLinearCombination, Fintype.linearCombination_apply]
  apply S.toSubmodule.sum_mem
  intro i _
  exact S.toSubmodule.smul_mem (c i)
    (mem_separableClosure_iff.mpr (w.isSeparable_algebraMap_completion (b i)))

end Dubon2026.SourceCurve.Place
