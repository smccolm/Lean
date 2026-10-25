import Dubon2026.SourceOriginalWeilComplexEvaluation
import Dubon2026.SourceOriginalWeilDatum

/-! DUB-17/18 -> arithmetic Weil detection. Extend the actual disjoint
divisors and their defining functions using the proved constant-field maps.
Exact orders on and off the arithmetic place image preserve the datum;
literal evaluation compatibility preserves its Weil ratio. -/
namespace Dubon2026.SourceFunctionField.OriginalConstantField
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N]
local notation "FQ" => modularFunctionFieldOver N Qbar
variable {n : ℕ}

theorem ord_fieldMap_of_multiple (f : FQ) (D : Divisor Qbar FQ)
    (h : ∀ v : Place Qbar FQ, v.ord f = n * D v)
    (w : Place ℂ (modularFunctionFieldOver N ℂ)) :
    w.ord (fieldMap N f) = n * conorm N D w := by
  by_cases hw : ∃ v, w = liftPlace N v
  · obtain ⟨v, rfl⟩ := hw
    rw [ord_liftPlace, conorm_apply_liftPlace, h]
  · push Not at hw
    rw [ord_phi_of_forall_ne N hw, conorm_apply_of_forall_ne N D hw, mul_zero]

theorem conorm_disjoint (D E : Divisor Qbar FQ)
    (h : ∀ v, D v = 0 ∨ E v = 0)
    (w : Place ℂ (modularFunctionFieldOver N ℂ)) :
    conorm N D w = 0 ∨ conorm N E w = 0 := by
  by_cases hw : ∃ v, w = liftPlace N v
  · obtain ⟨v, rfl⟩ := hw
    rw [conorm_apply_liftPlace, conorm_apply_liftPlace]
    exact h v
  · push Not at hw
    exact Or.inl (conorm_apply_of_forall_ne N D hw)

/-- The literal arithmetic Weil datum extended to the complex original field. -/
def originalWeilComplexDatum (d : OriginalWeilDatum N Qbar n) : OriginalWeilDatum N ℂ n where
  D₁ := conorm N d.D₁
  D₂ := conorm N d.D₂
  f₁ := fieldMap N d.f₁
  f₂ := fieldMap N d.f₂
  f₁_ne_zero := (map_ne_zero _).mpr d.f₁_ne_zero
  f₂_ne_zero := (map_ne_zero _).mpr d.f₂_ne_zero
  ord_f₁ := ord_fieldMap_of_multiple N d.f₁ d.D₁ d.ord_f₁
  ord_f₂ := ord_fieldMap_of_multiple N d.f₂ d.D₂ d.ord_f₂
  disjoint := conorm_disjoint N d.D₁ d.D₂ d.disjoint

theorem originalWeilComplexDatum_pairing (d : OriginalWeilDatum N Qbar n) :
    (originalWeilComplexDatum N d).pairing = sigma d.pairing := by
  change originalDivisorEval N ℂ (fieldMap N d.f₁) (conorm N d.D₂) /
    originalDivisorEval N ℂ (fieldMap N d.f₂) (conorm N d.D₁) = sigma (_ / _)
  rw [originalDivisorEval_conorm, originalDivisorEval_conorm, map_div₀]

end
end Dubon2026.SourceFunctionField.OriginalConstantField
