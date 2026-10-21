import Dubon2026.SourceOriginalDifferentialInjectivity

/-! DUB-17/18 -> matching cusp-form lower dimension bound -> regular
differential realization -> local differential coordinates.
The actual original j coordinate and its proved finite extension give the
one-dimensional differential space. This supplies the necessary original-field
rank without a general function-field change-of-transcendence-coordinate theory.
-/
namespace Dubon2026.SourceFunctionField
noncomputable section
open KaehlerDifferential SourceDifferential

variable (N : ℕ) [NeZero N] (L : Type*) [Field L] [Algebra ℚ L]

omit [NeZero N] in
theorem D_jOver_ne_zero :
    D L (modularFunctionFieldOver N L) (jOver N L) ≠ 0 := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  intro h
  have he := congrArg (diffQExp (modularFunctionFieldOver N L)) h
  rw [diffQExp_D, map_zero] at he
  exact qEuler_jOver_ne_zero N L he

theorem span_D_jOver :
    Submodule.span (modularFunctionFieldOver N L)
      ({D L (modularFunctionFieldOver N L) (jOver N L)} :
        Set Ω[modularFunctionFieldOver N L⁄L]) = ⊤ := by
  let K := IntermediateField.adjoin L ({jOver N L} : Set (modularFunctionFieldOver N L))
  letI : Algebra L (modularFunctionFieldOver N L) := inferInstance
  letI : Algebra L K := inferInstance
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap L K).injective
  haveI : FiniteDimensional K (modularFunctionFieldOver N L) := finiteDimensional_original N L
  haveI : Algebra.IsSeparable K (modularFunctionFieldOver N L) := inferInstance
  exact span_D_eq_top_of_transcendental L (jOver N L) (transcendental_jOver N L)

/-- The actual original function field has a one-dimensional space of relative differentials. -/
theorem finrank_original_differentials :
    Module.finrank (modularFunctionFieldOver N L) Ω[modularFunctionFieldOver N L⁄L] = 1 :=
  (finrank_eq_one_iff_of_nonzero _ (D_jOver_ne_zero N L)).mpr (span_D_jOver N L)

omit [NeZero N] in
theorem D_original_eq_zero_iff (x : modularFunctionFieldOver N L) :
    D L (modularFunctionFieldOver N L) x = 0 ↔
      ∃ c : L, x = algebraMap L (modularFunctionFieldOver N L) c := by
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  constructor
  · intro h
    have he := congrArg (diffQExp (modularFunctionFieldOver N L)) h
    rw [diffQExp_D, map_zero] at he
    exact ⟨(x : LaurentSeries L).coeff 0, Subtype.ext ((qEuler_eq_zero_iff _).mp he)⟩
  · rintro ⟨c, rfl⟩
    exact (D L (modularFunctionFieldOver N L)).map_algebraMap c

end
end Dubon2026.SourceFunctionField
