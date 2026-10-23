import Dubon2026.SourceCurveCompletionEmbeddingValuation

/-! Construct the actual embedding of completed curve fields, retaining
the original field values and the normalized ramification law. This is
the scalar map for the integral-basis residue/trace calculation. Native
completion functoriality replaces the archived completion equivalence
wrappers, which are unnecessary with the pinned Mathlib representation. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open WithZero Topology UniformSpace IsDedekindDomain

variable {K F E : Type*} [Field K] [Field F] [Field E]
  [Algebra K F] [Algebra K E] [Algebra F E] [IsScalarTower K F E]
  [Algebra.IsIntegral F E] (w : Place K E)

/-- The continuous original field embedding extended to the actual completions. -/
def adicCompletionComap : (w.restrict F).adicCompletion →+* w.adicCompletion :=
  Completion.mapRingHom
    (WithVal.map ((w.restrict F).heightOneSpectrum.valuation F)
      (w.heightOneSpectrum.valuation E) (algebraMap F E))
    (w.uniformContinuous_withValMapAlgebraMap (F := F)).continuous

/-- The constructed completion embedding is continuous. -/
theorem continuous_adicCompletionComap : Continuous (w.adicCompletionComap (F := F)) :=
  Completion.continuous_map

/-- On original valued-field elements the completed map is the literal field embedding. -/
theorem adicCompletionComap_coe (x : WithVal ((w.restrict F).heightOneSpectrum.valuation F)) :
    w.adicCompletionComap (x : (w.restrict F).adicCompletion) =
      (WithVal.map ((w.restrict F).heightOneSpectrum.valuation F)
        (w.heightOneSpectrum.valuation E) (algebraMap F E) x : w.adicCompletion) :=
  Completion.mapRingHom_coe (w.uniformContinuous_withValMapAlgebraMap (F := F)).continuous x

open WithZeroTopology in
/-- The actual completion embedding retains the original ramification exponent everywhere. -/
theorem valued_adicCompletionComap (x : (w.restrict F).adicCompletion) :
    Valued.v (w.adicCompletionComap x) = Valued.v x ^ w.ramificationIndex (F := F) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((Valued.continuous_valuation_of_surjective
        (w.heightOneSpectrum.valuedAdicCompletion_surjective E)).comp
          w.continuous_adicCompletionComap)
      ((Valued.continuous_valuation_of_surjective
        ((w.restrict F).heightOneSpectrum.valuedAdicCompletion_surjective F)).pow _)
  | ih x =>
    rw [w.adicCompletionComap_coe]
    simp only [Valued.valuedCompletion_apply]
    exact w.valued_withValMapAlgebraMap x

/-- Original field inclusions commute with the actual completion embedding. -/
theorem adicCompletionComap_algebraMap (x : F) :
    w.adicCompletionComap (algebraMap F (w.restrict F).adicCompletion x) =
      algebraMap E w.adicCompletion (algebraMap F E x) :=
  w.adicCompletionComap_coe (WithVal.toVal ((w.restrict F).heightOneSpectrum.valuation F) x)

/-- The actual completion embedding sends integral elements to integral elements. -/
theorem adicCompletionComap_mem_integers {x : (w.restrict F).adicCompletion}
    (hx : x ∈ (w.restrict F).adicCompletionIntegers) :
    w.adicCompletionComap x ∈ w.adicCompletionIntegers := by
  change Valued.v (w.adicCompletionComap x) ≤ 1
  rw [w.valued_adicCompletionComap]
  exact pow_le_one' hx _

/-- The scalar action on the extension completion is induced by the proved completion embedding. -/
instance completionExtensionAlgebra : Algebra (w.restrict F).adicCompletion w.adicCompletion :=
  (w.adicCompletionComap (F := F)).toAlgebra

/-- The completed scalar map is exactly the constructed embedding. -/
theorem algebraMap_completionExtension :
    algebraMap (w.restrict F).adicCompletion w.adicCompletion = w.adicCompletionComap := rfl

/-- The original base field and its completion give compatible scalar actions. -/
instance completionExtensionTower : IsScalarTower F (w.restrict F).adicCompletion w.adicCompletion :=
  IsScalarTower.of_algebraMap_eq fun x => (w.adicCompletionComap_algebraMap x).symm

/-- Scalar multiplication through the completed embedding is continuous. -/
instance completionExtensionContinuousSMul :
    ContinuousSMul (w.restrict F).adicCompletion w.adicCompletion :=
  continuousSMul_of_algebraMap _ _ w.continuous_adicCompletionComap

end Dubon2026.SourceCurve.Place
