import Dubon2026.SourceEllipticPeriodCurve
import Dubon2026.SourceEllipticPeriodInvariants
import Dubon2026.SourceAnalyticJTransformation

/-! The actual period curve is elliptic and has the existing analytic j-value.
This discharges the invariant normalization needed to compare the literal odd
quotients with analytic modular-polynomial roots, on the DUB-17/18 chain.
The downstream uniformization and complex quotient-product modules assemble these inputs. -/

namespace Dubon2026.SourceEllipticPeriod
open Complex UpperHalfPlane ModularForm
open Dubon2026.SourceFunctionField
open scoped Real

theorem periodCurve_ofTau_discriminant (τ : ℍ) :
    (periodCurve (PeriodLattice.ofTau τ)).Δ =
      (64 * (π : ℂ) ^ 12 / 27) * (E₄ τ ^ 3 - E₆ τ ^ 2) := by
  rw [periodCurve_discriminant, gTwo_ofTau, gThree_ofTau]
  ring

instance periodCurve_ofTau_isElliptic (τ : ℍ) :
    (periodCurve (PeriodLattice.ofTau τ)).IsElliptic := by
  constructor
  rw [isUnit_iff_ne_zero, periodCurve_ofTau_discriminant]
  exact mul_ne_zero (div_ne_zero (mul_ne_zero (by norm_num)
    (pow_ne_zero _ (by exact_mod_cast Real.pi_ne_zero))) (by norm_num))
    (JOrbitSeparation.E₄_cube_sub_E₆_sq_ne_zero τ)

theorem periodCurve_ofTau_j (τ : ℍ) :
    (periodCurve (PeriodLattice.ofTau τ)).j = JMultiplicity.jf τ := by
  rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ',
    periodCurve_ofTau_discriminant, periodCurve_cFour, gTwo_ofTau,
    JMultiplicity.jf, discriminant_eq_E₄_cube_sub_E₆_sq]
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hE := JOrbitSeparation.E₄_cube_sub_E₆_sq_ne_zero τ
  field_simp
  ring

end Dubon2026.SourceEllipticPeriod
