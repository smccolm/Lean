import Dubon2026.SourceEllipticPrimeAbscissaHom

/-! Connect the intrinsic prime quotient model to the original integral
modular-polynomial root map. This makes the exact polynomial relation an
output of each composite cyclic quotient step (DUB-17/18 inertia census). -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve SourceFunctionField.IntegralJCoordinate OddDiscriminant
noncomputable section
variable {F : Type*} [Field F] [DecidableEq F] [IsAlgClosed F]
variable (W : WeierstrassCurve F) [W.IsElliptic]

/-- The intrinsic quotient j-value is exactly the original cyclic-root map value. -/
theorem primeAbscissaQuotient_j_eq (p : ℕ) [Fact p.Prime] (hp : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    letI := primeAbscissaQuotient_isElliptic W p hp H
    (primeAbscissaQuotient W p H).j = (primeCyclicRootMap W p hp H).1 := by
  letI := primeAbscissaQuotient_isElliptic W p hp H
  by_cases hp2 : p = 2
  · subst p
    change (primeAbscissaQuotient W 2 H).j =
      twoQuotientJ W (primeKernelGenerator_order W 2 H)
    have he := primeAbscissaQuotient_two_eq W hp H
      (primeKernelGenerator_order W 2 H) (primeKernelGenerator_zmultiples W 2 H)
    simp only [twoQuotientJ, WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ']
    rw [he]
  · simp only [primeCyclicRootMap, dif_neg hp2, oddPrimeCyclicRootMap]
    have he := primeAbscissaQuotient_odd_eq W p hp2 H
      (primeKernelGenerator_oddOrder W p hp2 H) (primeKernelGenerator_zmultiples W p H)
    simp only [oddQuotientJ, WeierstrassCurve.j, Units.val_inv_eq_inv_val, coe_Δ']
    rw [he]

/-- The literal intrinsic prime quotient satisfies the exact original modular polynomial. -/
theorem primeAbscissaQuotient_isRoot (p : ℕ) [Fact p.Prime] (hp : (p : F) ≠ 0)
    (H : {H : AddSubgroup W.toAffine.Point // IsAddCyclic H ∧ Nat.card H = p}) :
    letI := primeAbscissaQuotient_isElliptic W p hp H
    (SourceFunctionField.relationAtSeed (modularPolynomial p) W.j).IsRoot
      (primeAbscissaQuotient W p H).j := by
  letI := primeAbscissaQuotient_isElliptic W p hp H
  rw [primeAbscissaQuotient_j_eq W p hp H]
  exact (primeCyclicRootMap W p hp H).2

end
end Dubon2026.SourceEllipticVelu
