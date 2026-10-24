import Dubon2026.SourceEllipticAbscissaQuotientX
import Dubon2026.SourceEllipticOddVariableCoefficients

/-! The finite-kernel quotient coefficients under the original Weierstrass
variable change. Reuse the proved Velu transformation and native b-invariant
formulas. These identities feed actual quotient and image-subgroup transport,
then the all-level cyclic-root bijection and DUB-17/18 inertia census. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve Polynomial SourceEllipticVariableChange OddDiscriminant
noncomputable section
variable {F : Type*} [Field F] (C : VariableChange F) (W : WeierstrassCurve F)

/-- The intrinsic T coefficient obeys the already proved Velu transformation. -/
theorem variableChange_abscissaVeluT (x : F) :
    abscissaVeluT (C • W) (vcXInv C x) =
      ((C.u⁻¹ : Fˣ) : F) ^ 4 * abscissaVeluT W x := by
  rw [abscissaVeluT_eq (C • W) _ (vcYInv C x 0), variableChange_veluT,
    ← abscissaVeluT_eq W x 0]

/-- The actual squared second division polynomial transforms at its original abscissa. -/
theorem variableChange_secondDivision_eval (x : F) :
    (C • W).Ψ₂Sq.eval (vcXInv C x) =
      ((C.u⁻¹ : Fˣ) : F) ^ 6 * W.Ψ₂Sq.eval x := by
  simp only [Ψ₂Sq, eval_add, eval_mul, eval_pow, eval_C, eval_X,
    variableChange_b₂, variableChange_b₄, variableChange_b₆, vcXInv]
  ring

/-- The intrinsic W coefficient transforms without an ordinate choice. -/
theorem variableChange_abscissaVeluW (x : F) :
    abscissaVeluW (C • W) (vcXInv C x) =
      ((C.u⁻¹ : Fˣ) : F) ^ 6 * (abscissaVeluW W x - C.r * abscissaVeluT W x) := by
  rw [abscissaVeluW, variableChange_secondDivision_eval, variableChange_abscissaVeluT,
    abscissaVeluW, vcXInv]
  ring

/-- Away from characteristic two the degree-two coefficient is half the intrinsic T coefficient. -/
theorem twoAbscissaG_eq_half (h2 : (2 : F) ≠ 0) (x : F) :
    twoAbscissaG W x = abscissaVeluT W x / 2 := by
  simp only [twoAbscissaG, veluGx, abscissaVeluT, b₂, b₄]
  field_simp
  ring

/-- The actual degree-two coefficient has the same fourth-power scaling. -/
theorem variableChange_twoAbscissaG (h2 : (2 : F) ≠ 0) (x : F) :
    twoAbscissaG (C • W) (vcXInv C x) =
      ((C.u⁻¹ : Fˣ) : F) ^ 4 * twoAbscissaG W x := by
  rw [twoAbscissaG_eq_half _ h2, variableChange_abscissaVeluT,
    twoAbscissaG_eq_half _ h2]
  ring

end
end Dubon2026.SourceEllipticVelu
