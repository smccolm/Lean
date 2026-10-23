import Dubon2026.SourceCurvePlaceRestriction

/-! The actual completion of a curve place, used for the finite-extension
integral basis in residue/field-trace compatibility (DUB-17/18 -> good
reduction -> reverse genus -> global residues). Native discrete valuation
theory constructs its place directly; no completion geometry is assumed.
The verified FLT PlaceCompletion source supplies the intended objects. -/

noncomputable section

namespace Dubon2026.SourceCurve.Place

open IsDedekindDomain WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

/-- The completion at the actual discrete valuation of the place. -/
abbrev adicCompletion := v.heightOneSpectrum.adicCompletion F

/-- The actual valuation ring in the completion. -/
abbrev adicCompletionIntegers : ValuationSubring v.adicCompletion :=
  v.heightOneSpectrum.adicCompletionIntegers F

/-- Completing preserves the original normalized valuation on field elements. -/
theorem valued_completion_algebraMap (x : F) :
    Valued.v (algebraMap F v.adicCompletion x) = v.adicValuation x :=
  v.heightOneSpectrum.valuedAdicCompletion_eq_valuation' x

/-- An original field element is integral in the completion exactly when it was integral. -/
theorem completion_integer_iff (x : F) :
    algebraMap F v.adicCompletion x ∈ v.adicCompletionIntegers ↔ x ∈ v.toValuationSubring := by
  change Valued.v (algebraMap F v.adicCompletion x) ≤ 1 ↔ _
  rw [v.valued_completion_algebraMap, v.adicValuation_le_one_iff]

/-- The completed valuation ring is still a proper subring of its field. -/
theorem completionIntegers_ne_top : v.adicCompletionIntegers ≠ ⊤ := by
  intro h
  apply v.ne_top'
  apply SetLike.ext
  intro x
  constructor
  · intro _
    exact ValuationSubring.mem_top x
  · intro _
    exact (v.completion_integer_iff x).mp (h ▸ ValuationSubring.mem_top _)

/-- The completed valuation is nontrivial, as witnessed by the original field. -/
theorem completionValuation_nontrivial :
    (Valued.v : Valuation v.adicCompletion ℤᵐ⁰).IsNontrivial := by
  by_contra h
  apply v.completionIntegers_ne_top
  exact (Valuation.valuationSubring_eq_top_iff (v := (Valued.v : Valuation v.adicCompletion ℤᵐ⁰))).mpr h

/-- The completed discrete valuation defines an actual place over the same constants. -/
def completionPlace : Place K v.adicCompletion where
  toValuationSubring := v.adicCompletionIntegers
  algebraMap_mem' c := by
    change Valued.v (algebraMap K v.adicCompletion c) ≤ 1
    rw [IsScalarTower.algebraMap_apply K F v.adicCompletion, v.valued_completion_algebraMap]
    exact v.adicValuation_le_one_iff.mpr (v.algebraMap_mem' c)
  ne_top' := v.completionIntegers_ne_top
  isPrincipalIdealRing' := by
    letI := v.completionValuation_nontrivial
    exact Valuation.valuationSubring_isPrincipalIdealRing (Valued.v : Valuation v.adicCompletion ℤᵐ⁰)

/-- Integrality at the constructed completed place retains the literal original condition. -/
theorem completionPlace_integral_iff (x : F) :
    algebraMap F v.adicCompletion x ∈ v.completionPlace.toValuationSubring ↔
      x ∈ v.toValuationSubring := v.completion_integer_iff x

end Dubon2026.SourceCurve.Place
