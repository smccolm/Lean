import Dubon2026.PrimeWittIntertwiner

/-! # The actual inverse of the changed-uniformizer series

The pinned substitution inverse applies because the constructed linear
coefficient is an actual Witt unit. This supplies the inverse needed when
passing between the two primitive torsion points on DUB-17's ramified
cyclotomic reciprocity route. No new inversion infrastructure is required.
-/
namespace Dubon2026
noncomputable section
variable (p : ℕ) [Fact p.Prime]
  (u : (WittVector p (AlgebraicClosure (ZMod p)))ˣ)

/-- The actual constructed series has invertible linear coefficient. -/
theorem primeWittIntertwiner_linear_isUnit :
    IsUnit (PowerSeries.coeff 1 (primeWittIntertwiner p u)) := by
  rw [primeWittIntertwiner_coeff_one]
  exact (primeWittLinearCoefficient p u).isUnit

/-- The pinned formal substitution inverse of the actual constructed series. -/
def primeWittIntertwinerInverse : PowerSeries (WittVector p (AlgebraicClosure (ZMod p))) :=
  (primeWittIntertwiner p u).substInvOfIsUnit (primeWittIntertwiner_linear_isUnit p u)

/-- The actual inverse has zero constant coefficient. -/
theorem primeWittIntertwinerInverse_constantCoeff :
    PowerSeries.constantCoeff (primeWittIntertwinerInverse p u) = 0 :=
  PowerSeries.constantCoeff_substInvOfIsUnit _ _

/-- Substitution of the actual inverse into the actual series gives X. -/
theorem primeWittIntertwinerInverse_right :
    PowerSeries.subst (primeWittIntertwinerInverse p u) (primeWittIntertwiner p u) =
      PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_right _ (primeWittIntertwiner_constantCoeff p u) _

/-- Substitution of the actual series into its actual inverse gives X. -/
theorem primeWittIntertwinerInverse_left :
    PowerSeries.subst (primeWittIntertwiner p u) (primeWittIntertwinerInverse p u) =
      PowerSeries.X :=
  PowerSeries.subst_substInvOfIsUnit_left _ (primeWittIntertwiner_constantCoeff p u) _

end
end Dubon2026
