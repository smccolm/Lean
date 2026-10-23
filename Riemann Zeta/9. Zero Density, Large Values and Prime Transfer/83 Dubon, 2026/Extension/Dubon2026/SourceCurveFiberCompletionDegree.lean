import Dubon2026.SourceCurveFiberCompletions
import Dubon2026.SourceCurveCompletionDegree
import Dubon2026.SourceCurveFiberDegreeSum

/-! The product of the actual completions has exactly the original
extension degree. This reuses the proved original fiber ramification sum
and the completed local degree calculation, supplying the dimension step
for the DUB-17/18 sum of field traces. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] [FiniteDimensional F E] (v : Place K F)

omit [FiniteDimensional F E] in
/-- Each actual fiber completion carries its induced base-completion module structure. -/
instance fiberCompletionModule (w : {w : Place K E // w.restrict F = v}) :
    Module v.adicCompletion w.1.adicCompletion := Algebra.toModule

/-- Each actual fiber completion is finite over the fixed base completion. -/
instance fiberCompletionFinite (w : {w : Place K E // w.restrict F = v}) :
    FiniteDimensional v.adicCompletion w.1.adicCompletion := by
  rcases w with ⟨w, hw⟩
  subst v
  exact w.finiteDimensional_completion (F := F)

variable [Algebra.IsSeparable F E]

/-- A rational fiber place has completed degree equal to its original ramification order. -/
theorem fiberCompletion_finrank (w : {w : Place K E // w.restrict F = v})
    (hres : Function.Surjective (algebraMap K w.1.ResidueField)) :
    Module.finrank v.adicCompletion w.1.adicCompletion = w.1.ramificationIndex (F := F) := by
  rcases w with ⟨w, hw⟩
  subst v
  exact w.completion_finrank_eq_ramificationIndex hres

/-- The sum of the actual completed local degrees is the original extension degree. -/
theorem sum_fiberCompletion_finrank
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField)) :
    ∑ᶠ w : {w : Place K E // w.restrict F = v},
      Module.finrank v.adicCompletion w.1.adicCompletion = Module.finrank F E := by
  classical
  letI := Fintype.ofFinite {w : Place K E // w.restrict F = v}
  have h := v.sum_fiber_ramification hbase htop
  rw [finsum_eq_sum_of_fintype] at h ⊢
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_sum]
  calc
    _ = ∑ w : {w : Place K E // w.restrict F = v},
        w.1.ord (algebraMap F E v.uniformizer) := by
      apply Finset.sum_congr rfl
      intro w _
      rw [v.fiberCompletion_finrank w (htop w.1).surjective, w.1.ramificationIndex_cast, w.2]
    _ = _ := h

/-- The actual product of the fiber completions has the full original extension dimension. -/
theorem finrank_fiberCompletion_product
    (hbase : Function.Bijective (algebraMap K v.ResidueField))
    (htop : ∀ w : Place K E, Function.Bijective (algebraMap K w.ResidueField)) :
    Module.finrank v.adicCompletion
      ((w : {w : Place K E // w.restrict F = v}) → w.1.adicCompletion) = Module.finrank F E := by
  classical
  letI := Fintype.ofFinite {w : Place K E // w.restrict F = v}
  rw [Module.finrank_pi_fintype]
  exact (finsum_eq_sum_of_fintype _).symm.trans (v.sum_fiberCompletion_finrank hbase htop)

end Dubon2026.SourceCurve.Place
