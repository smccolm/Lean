import Dubon2026.SourceEllipticTwoCyclicAbscissae
import Dubon2026.SourceEllipticPrimeCyclicRootMap

/-! The actual prime quotient curve determined by the subgroup itself.
Both coefficient branches are identified with the already proved literal
quotients, deriving ellipticity. This is the first step of composite cyclic
quotients on the DUB-17/18 all-level exceptional-fiber dependency chain. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceFunctionField.IntegralJCoordinate OddDiscriminant
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] (W : WeierstrassCurve F)

/-- The literal prime quotient coefficients computed from the whole finite cyclic kernel. -/
def primeAbscissaQuotient (p : ℕ) [hp : Fact p.Prime]
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    WeierstrassCurve F :=
  letI : Finite H.1 := Nat.finite_of_card_ne_zero (H.2.2.symm ▸ hp.out.ne_zero)
  if p = 2 then twoAbscissaQuotient W (cyclicAbscissae W H.1)
  else abscissaQuotient W (cyclicAbscissae W H.1)

/-- At degree two the intrinsic curve equals the original quotient by every actual generator. -/
theorem primeAbscissaQuotient_two_eq (h2 : (2 : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = 2})
    {P : W.toAffine.Point} (hP : addOrderOf P = 2) (hPH : AddSubgroup.zmultiples P = H.1) :
    primeAbscissaQuotient W 2 H = veluQuotient2 W (coordsOrZero P).1 (coordsOrZero P).2 := by
  letI : Finite H.1 := Nat.finite_of_card_ne_zero (by rw [H.2.2]; decide)
  simp only [primeAbscissaQuotient]
  exact twoAbscissaQuotient_eq W h2 H.1 hP hPH

/-- At odd prime degree the intrinsic curve equals every original half-orbit quotient. -/
theorem primeAbscissaQuotient_odd_eq (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p})
    {P : W.toAffine.Point} (hP : addOrderOf P = 2 * (p / 2) + 1)
    (hPH : AddSubgroup.zmultiples P = H.1) :
    primeAbscissaQuotient W p H = veluQuotient W (oddOrderSummingSet W P (p / 2)) := by
  letI : Finite H.1 := Nat.finite_of_card_ne_zero (H.2.2.symm ▸ hp.out.ne_zero)
  simp only [primeAbscissaQuotient, if_neg hp2]
  exact (oddQuotient_eq_abscissaQuotient W H.1 hP hPH).symm

/-- The intrinsic prime quotient is elliptic, with every discriminant condition derived. -/
theorem primeAbscissaQuotient_isElliptic [W.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hp : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    (primeAbscissaQuotient W p H).IsElliptic := by
  by_cases hp2 : p = 2
  · subst p
    rw [primeAbscissaQuotient_two_eq W hp H (primeKernelGenerator_order W 2 H)
      (primeKernelGenerator_zmultiples W 2 H)]
    exact twoQuotient_isElliptic W (primeKernelGenerator_order W 2 H)
  · rw [primeAbscissaQuotient_odd_eq W p hp2 H (primeKernelGenerator_oddOrder W p hp2 H)
      (primeKernelGenerator_zmultiples W p H)]
    exact odd_quotient_isElliptic W _ (primeKernelGenerator_oddOrder W p hp2 H)

end
end Dubon2026.SourceEllipticVelu
