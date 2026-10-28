import Dubon2026.SourceGammaOneComplexConstantAutomorphisms
import Dubon2026.SourceTranscendentalTranslation

/-! DUB-17/18 -> arithmetic torsion comparison -> finite torsion descent.
Every complex constant outside Qbar can be translated by any
arithmetic constant using an actual coefficient automorphism fixing the arithmetic field
and all lifted arithmetic places. This is the orbit-producing automorphism
needed to exclude nonarithmetic places from an invariant reduced divisor.
-/
namespace Dubon2026.SourceFunctionField.GammaOne.ConstantField
noncomputable section
open SourceCurve CongruenceSubgroup
local notation "Qbar" => AlgebraicClosure ℚ
attribute [local instance] complexAlgebra
variable (N : ℕ) [NeZero N]
local notation "FQ" => functionFieldOver (Gamma1 N) Qbar

theorem exists_complex_translation {t : ℂ} (ht : t ∉ Set.range OriginalConstantField.sigma) (a : Qbar) :
    ∃ τ : ℂ ≃ₐ[Qbar] ℂ, τ t = t + OriginalConstantField.sigma a ∧
      (∀ f : FQ, arithmeticRingAut (Gamma1 N) (OriginalConstantField.complexAutRestrict τ) (fieldMap N f) = fieldMap N f) ∧
      ∀ P : Place Qbar FQ,
        arithmeticPlace (Gamma1 N) (OriginalConstantField.complexAutRestrict τ) (liftPlace N P) = liftPlace N P := by
  have htr : Transcendental Qbar t := by
    intro halg
    have hint : IsIntegral Qbar t := halg.isIntegral
    exact ht (minpoly.mem_range_of_degree_eq_one Qbar t
      (IsAlgClosed.degree_eq_one_of_irreducible Qbar (minpoly.irreducible hint)))
  obtain ⟨τ, hτ⟩ := SourceCurve.ConstantField.exists_translation_of_transcendental Qbar ℂ t htr a
  exact ⟨τ, hτ, complexAut_fixes_arithmetic N τ, complexAut_fixes_liftPlace N τ⟩

end
end Dubon2026.SourceFunctionField.GammaOne.ConstantField
