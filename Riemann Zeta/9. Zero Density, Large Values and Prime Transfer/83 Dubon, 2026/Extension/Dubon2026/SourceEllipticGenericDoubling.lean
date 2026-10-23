import Dubon2026.SourceEllipticGenericJacobian

/-! Integral descent of the actual generic multiplication formula.
The native Jacobian group law identifies the division-polynomial triple,
then injectivity of the coordinate ring into its fraction field descends
the doubling and addition identities. This serves DUB-17 Theorem 2.6 and
DUB-18 Corollary 8.2 through actual point multiplication, elliptic torsion,
the finite exceptional-fiber census, reverse genus and good reduction.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, EDSEngine. -/
namespace Dubon2026.SourceEllipticUniversal.JacobianFormula
open WeierstrassCurve Polynomial Dubon2026.SourceEllipticDivision
open WeierstrassCurve.Jacobian
open WeierstrassCurve (ψ φ)
open Dubon2026.SourceEllipticSequence
open scoped Polynomial.Bivariate nonZeroDivisors
noncomputable section
variable {m n : ℤ}
theorem dblZ_smulPoly : dblZ curvePoly (smulPoly n) = curve.ψ (2 * n) := by
  simp_rw [dblZ, smulPoly, negY, fin3_def_ext, curvePoly, WeierstrassCurve.baseChange, WeierstrassCurve.map, coe_algebraMap_eq_CC]
  rw [← ψc_spec _ n]; congr; convert ωe_spec curve n using 1; ring

theorem nonsingular_smulField : Nonsingular curveField (smulField n) := by
  simpa only [zsmul_point_eq_smulField, WeierstrassCurve.Jacobian.nonsingularLift_iff] using (n • jacobianPoint).nonsingular

theorem dblXYZ_smulField : dblXYZ curveField (smulField n) = smulField (2 * n) := by
  obtain rfl | hn := eq_or_ne n 0
  ·

    rw [mul_zero]
    have h0 : smulField (0 : ℤ) = ![1, 1, 0] := by
      ext i
      fin_cases i <;> simp [smulField, smulPoly, φ_zero, ωe_zero, ψ_zero]
    rw [h0, dblXYZ_of_Z_eq_zero equation_zero rfl]
    simp

  have h2 : ((2 : ℤ) • (n • jacobianPoint)).point =
      ⟦dblXYZ curveField (smulField n)⟧ := by
    rw [two_zsmul, Point.add_point, zsmul_point_eq_smulField, addMap_eq, add_self]
  refine (equiv_iff_eq_of_Z_eq ?_ (ψᵤ_ne_zero <| mul_ne_zero two_ne_zero hn)).mp
    (Quotient.exact ?_)
  · simp only [smulField, smulPoly, fin3_def_ext, Function.comp, ← dblZ_smulPoly, ← map_dblZ]
    rfl
  rw [← h2, ← mul_zsmul]
  exact zsmul_point_eq_smulField

theorem dblXYZ_smulRing : dblXYZ curveRing (smulRing n) = smulRing (2 * n) :=
  (IsFractionRing.injective _ FunctionField).comp_left <| by
    simp_rw [← map_dblXYZ]; exact dblXYZ_smulField


end
end Dubon2026.SourceEllipticUniversal.JacobianFormula
