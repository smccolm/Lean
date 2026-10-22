import Dubon2026.SourceOriginalComplexConstantAutomorphisms
import Dubon2026.SourceTranscendentalTranslation

/-! DUB-17/18 -> arithmetic torsion comparison -> finite torsion descent.
Every complex constant outside Qbar can be translated by any
arithmetic constant using an actual coefficient automorphism fixing the arithmetic field
and all lifted arithmetic places. This is the orbit-producing automorphism
needed to exclude nonarithmetic places from an invariant reduced divisor.
-/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
attribute [local instance] complexAlgebra
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar

theorem exists_original_complex_translation {t : ℂ} (ht : t ∉ Set.range sigma) (a : Qbar) :
    ∃ τ : ℂ ≃ₐ[Qbar] ℂ, τ t = t + sigma a ∧
      (∀ f : FQ, originalArithmeticRingAut N (complexAutRestrict τ) (fieldMap N f) = fieldMap N f) ∧
      ∀ P : Place Qbar FQ,
        originalArithmeticPlace N (complexAutRestrict τ) (liftPlace N P) = liftPlace N P := by
  have htr : Transcendental Qbar t := by
    intro halg
    have hint : IsIntegral Qbar t := halg.isIntegral
    exact ht (minpoly.mem_range_of_degree_eq_one Qbar t
      (IsAlgClosed.degree_eq_one_of_irreducible Qbar (minpoly.irreducible hint)))
  obtain ⟨τ, hτ⟩ := ConstantField.exists_translation_of_transcendental Qbar ℂ t htr a
  exact ⟨τ, hτ, complexAut_fixes_arithmetic N τ, complexAut_fixes_liftPlace N τ⟩

end
end Dubon2026.SourceFunctionField.OriginalConstantField
