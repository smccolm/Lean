import Dubon2026.SourceModularCoefficientFieldFinite
import Dubon2026.SourceCurveCoordinateExchange

/-! DUB-17/18 -> original Frobenius/inertia -> good curve reduction ->
finite coordinates on the residue-characteristic field. Reuses the proved
transcendence-basis exchange and native essential-finite-type theorem.
No separability of an arbitrary coordinate is asserted. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open IntermediateField

theorem finite_divisorExpansionsCoeff (N : ℕ) [NeZero N]
    (K : Type*) [Field K] : (divisorExpansionsCoeff N K).Finite := by
  classical
  refine ((Set.finite_Iic N).image
    (fun d : ℕ => if h : d = 0 then 0 else @qExpand K _ d ⟨h⟩ (jqModC K))).subset ?_
  rintro x ⟨d, hd, hdvd, rfl⟩
  exact ⟨d, Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne N)) hdvd, dif_neg hd.ne⟩

theorem essFiniteType_coeff_field (N : ℕ) [NeZero N] (K : Type*) [Field K] :
    Algebra.EssFiniteType K (modularFunctionFieldCoeff N K) := by
  apply IntermediateField.essFiniteType_iff.mpr
  exact IntermediateField.fg_adjoin_of_finite (finite_divisorExpansionsCoeff N K)

theorem finiteDimensional_coeff_over_transcendental
    (N : ℕ) [NeZero N] (K : Type*) [Field K]
    {t : modularFunctionFieldCoeff N K} (ht : Transcendental K t) :
    FiniteDimensional (IntermediateField.adjoin K {t}) (modularFunctionFieldCoeff N K) := by
  let F := modularFunctionFieldCoeff N K
  letI : Algebra K F := inferInstance
  let E := IntermediateField.adjoin K ({t} : Set F)
  let J := IntermediateField.adjoin K ({jCoeff N K} : Set F)
  letI : Algebra K E := inferInstance
  letI : Algebra K J := inferInstance
  haveI : FiniteDimensional J F := finiteDimensional_coeff_field N K
  haveI : Algebra.IsAlgebraic J F := Algebra.IsAlgebraic.of_finite J F
  haveI : Algebra.IsAlgebraic E F :=
    SourceCurve.isAlgebraic_adjoin_of_transcendental (jCoeff N K) ht
  haveI : Algebra.EssFiniteType K F := essFiniteType_coeff_field N K
  haveI : Algebra.EssFiniteType E F := Algebra.EssFiniteType.of_comp K E F
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

end
end Dubon2026.SourceFunctionField
