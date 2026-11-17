import Dubon2026.SourceOriginalSupportBottomOdd

/-! DUB-17/18 -> actual CM deformation dimensions. Isolate the exact
finite linear bounds on the literal support/bottom pullback, reusing the two
proved surjectivity comparisons without new image or coefficient assumptions. -/
namespace Dubon2026.SourceDickson
noncomputable section
open Matrix
open scoped NumberField

/-- Preserve the original rational scalar structure. -/
private local instance originalSupportBottomBoundsAlgebra (a : 𝓞 ℚ) :
    Algebra ℚ (rationalUnramifiedExtension a) := (rationalUnramifiedExtension a).algebra'

/-- The original finite linear subfield bounds survive the exact composite
support and bottom restriction used by the native CM deformation representation. -/
theorem original_support_bottom_finite_linear_bounds
    (a : 𝓞 ℚ) (p : ℕ) [Fact p.Prime] {L : Type} [Field L]
    (j : L →+* K p)
    (ρ : rationalArithmeticGaloisGroup a →* GeneralLinearGroup (Fin 2) L)
    (h : HasFiniteLinearSubfieldBounds p j ρ) :
    HasFiniteLinearSubfieldBounds p j
      (ρ.comp ((rationalArithmeticSupportRestriction a (4 * a) (dvd_mul_left a 4)).comp
        (originalRationalBottomRestriction (4 * a))).toMonoidHom) := by
  exact finite_linear_bounds_precomp_surjective p j ρ
    ((rationalArithmeticSupportRestriction a (4 * a) (dvd_mul_left a 4)).comp
      (originalRationalBottomRestriction (4 * a))).toMonoidHom
    ((rationalArithmeticSupportRestriction_surjective a (4 * a) (dvd_mul_left a 4)).comp
      (originalRationalBottomRestriction_surjective (4 * a))) h

end
end Dubon2026.SourceDickson
