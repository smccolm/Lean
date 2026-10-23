import Dubon2026.SourceCurveCompletionRamification
import Dubon2026.SourceCurveCompletionResidueExtension

/-! Rational residues and native ramification--inertia give the exact
degree of the actual completed extension. Together with the existing
original fiber-degree sum this is the dimension comparison needed to
assemble completed field traces over all places, serving DUB-17/18. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open IsLocalRing

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- The native field degree of the actual completed extension. -/
def completedExtensionDegree : ℕ := Module.finrank (w.restrict F).adicCompletion w.adicCompletion

/-- Rational original upper residues force completed inertia degree one. -/
theorem completion_inertiaDeg_eq_one
    (hres : Function.Surjective (algebraMap K w.ResidueField)) :
    (maximalIdeal (w.restrict F).adicCompletionIntegers).inertiaDeg
      (maximalIdeal w.adicCompletionIntegers) = 1 := by
  letI := w.completionIntegralExtensionIsLocalHom (F := F)
  rw [Ideal.inertiaDeg_algebraMap]
  apply Module.finrank_of_bijective_algebraMap
  refine ⟨(algebraMap (IsLocalRing.ResidueField (w.restrict F).adicCompletionIntegers)
    (IsLocalRing.ResidueField w.adicCompletionIntegers)).injective, ?_⟩
  exact w.completion_residue_extension_surjective (F := F) hres

/-- The actual completed extension degree equals the original ramification index at a rational place. -/
theorem completion_finrank_eq_ramificationIndex [FiniteDimensional F E] [Algebra.IsSeparable F E]
    (hres : Function.Surjective (algebraMap K w.ResidueField)) :
    Module.finrank (w.restrict F).adicCompletion w.adicCompletion =
      w.ramificationIndex (F := F) := by
  letI : IsDiscreteValuationRing (w.restrict F).adicCompletionIntegers :=
    inferInstanceAs (IsDiscreteValuationRing (w.restrict F).completionPlace.toValuationSubring)
  letI : IsDiscreteValuationRing w.adicCompletionIntegers :=
    inferInstanceAs (IsDiscreteValuationRing w.completionPlace.toValuationSubring)
  letI : FiniteDimensional (w.restrict F).adicCompletion w.adicCompletion :=
    w.finiteDimensional_completion (F := F)
  letI : Algebra.IsSeparable (w.restrict F).adicCompletion w.adicCompletion :=
    w.isSeparable_completion (F := F)
  letI : IsIntegralClosure w.adicCompletionIntegers (w.restrict F).adicCompletionIntegers
      w.adicCompletion := w.isIntegralClosure_completionIntegers (F := F)
  letI : Module.Finite (w.restrict F).adicCompletionIntegers w.adicCompletionIntegers :=
    (w.completionIntegers_finite_free (F := F)).1
  have hp : maximalIdeal (w.restrict F).adicCompletionIntegers ≠ ⊥ := by
    intro h
    exact IsDiscreteValuationRing.not_isField (w.restrict F).adicCompletionIntegers
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mpr h)
  have he := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing w.adicCompletionIntegers
    (w.restrict F).adicCompletion w.adicCompletion hp
  rw [w.completion_ramificationIdx, w.completion_inertiaDeg_eq_one hres, mul_one] at he
  exact he.symm

end Dubon2026.SourceCurve.Place
