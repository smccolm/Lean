import Dubon2026.SourceEllipticPeriodPointAddition
import Dubon2026.SourceEllipticPeriodPointSurjectivity
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! The actual Weierstrass-function uniformization as an additive quotient
isomorphism. The addition law, surjectivity and exact lattice kernel are all
proved, and its values on representatives are the actual analytic points.
This discharges the group uniformization input to the odd-prime product
identity required for the DUB-17/18 cyclic-root and inertia interpretation.
SourceEllipticOddQuotientScalar and SourceIntegralComplexOddQuotientProduct
assemble quotient compatibility and the complex product identity. -/

namespace Dubon2026.SourceEllipticPeriod
noncomputable section
variable (L : PeriodPair) [(periodCurve L).IsElliptic]

/-- The actual Weierstrass-function map, with its proved additive structure. -/
def periodHom : ℂ →+ (periodCurve L).toAffine.Point where
  toFun := periodPoint L
  map_zero' := periodPoint_zero L
  map_add' := periodPoint_add L

theorem periodHom_surjective : Function.Surjective (periodHom L) := periodPoint_surjective L

theorem ker_periodHom : (periodHom L).ker = L.lattice.toAddSubgroup := by
  ext z
  exact periodPoint_eq_zero_iff L z

/-- The lattice quotient is isomorphic to the actual period curve's point group. -/
def periodQuotientEquiv : (ℂ ⧸ L.lattice.toAddSubgroup) ≃+ (periodCurve L).toAffine.Point :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_periodHom L).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (periodHom L) (periodHom_surjective L))

theorem periodQuotientEquiv_mk (z : ℂ) :
    periodQuotientEquiv L (QuotientAddGroup.mk z) = periodPoint L z := rfl

end
end Dubon2026.SourceEllipticPeriod
