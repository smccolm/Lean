import Dubon2026.SourceCurveClosedSeparatingPrincipalDivisors
import Dubon2026.SourceModularCoefficientDifferentials
import Dubon2026.SourceModularCoefficientResidue

/-! DUB-17/18 -> original Frobenius/inertia -> actual modular-curve good
reduction -> residue-curve geometry. The literal all-divisor coefficient
field is now proved to have finite principal divisors of degree zero,
finite place residues and a one-dimensional differential module over
algebraically closed constants, in every characteristic. This closes the
IsCurveOver premise of the later exact-degree and genus/reduction arguments.
Those comparisons and the original Frobenius/inertia identities are still
separate unresolved obligations; this theorem is not a good-reduction claim. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve

theorem hasPrincipalDivisors_coeff_field (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [IsAlgClosed K] : HasPrincipalDivisors K (modularFunctionFieldCoeff N K) := by
  haveI := finiteDimensional_coeff_field N K
  haveI := isSeparable_coeff_field N K
  exact hasPrincipalDivisors_closed_of_separating_coordinate
    (jCoeff N K) (transcendental_jCoeff N K)

theorem isCurveOver_coeff_field (N : ℕ) [NeZero N]
    (K : Type*) [Field K] [IsAlgClosed K] : IsCurveOver K (modularFunctionFieldCoeff N K) where
  toHasPrincipalDivisors := hasPrincipalDivisors_coeff_field N K
  finiteResidue := finite_coeff_place_residue N K
  kaehler_free_rank_one := ⟨inferInstance, finrank_coeff_differentials N K⟩

end
end Dubon2026.SourceFunctionField
