import Dubon2026.SourceEllipticGenericDoubling

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
theorem addZ_smulPoly : addZ (smulPoly m) (smulPoly n) = curve.ψ (n + m) * curve.ψ (n - m) := by
  have hES : IsEllSequence (WeierstrassCurve.ψ curve) := normalized_isEllSequence _ _ _
  simp_rw [addZ, smulPoly, φ]; convert (hES n m 1).symm using 1
  · simp only [fin3_def_ext]; ring
  · rw [ψ_one]; ring

theorem ωe_neg_eq_neg_negY : (ωe curve) (-n) = -negY curvePoly (smulPoly n) := by

  simp_rw [AffineFormula.ωe_neg' (n := n), negY, smulPoly, fin3_def_ext, curvePoly, WeierstrassCurve.baseChange, WeierstrassCurve.map,
    coe_algebraMap_eq_CC]
  ring

theorem smulPoly_neg : smulPoly (-n) = (-1 : Poly) • neg curvePoly (smulPoly n) := by
  simp [smulPoly, ωe_neg_eq_neg_negY, neg, smul_fin3, (show Odd 3 by decide).neg_pow]

theorem smulRing_neg : smulRing (-n) = (-1 : Coord) • neg curveRing (smulRing n) := by
  simp_rw [smulRing, smulPoly_neg, WeierstrassCurve.Jacobian.comp_smul, ← WeierstrassCurve.Jacobian.map_neg, map_neg, map_one]; rfl

theorem smulField_neg : smulField (-n) = (-1 : FunctionField) • neg curveField (smulField n) := by
  simp_rw [smulField, smulPoly_neg, WeierstrassCurve.Jacobian.comp_smul, ← WeierstrassCurve.Jacobian.map_neg, map_neg, map_one]; rfl

theorem smulPoly_zero : smulPoly 0 = ![1, 1, 0] := by simp [smulPoly]
theorem smulField_zero : smulField 0 = ![1, 1, 0] := by simp [smulField, smulPoly_zero, comp_fin3]

theorem addXYZ_smulField :
    addXYZ curveField (smulField m) (smulField n) =
      polyToField (curve.ψ (n - m)) • smulField (n + m) := by
  obtain rfl | h := eq_or_ne m n
  · rw [sub_self, ψ_zero, map_zero, smul_fin3,
      addXYZ_self nonsingular_smulField.1, zero_pow two_ne_zero, zero_pow (by decide)]
    simp_rw [zero_mul]
  obtain rfl | ne_neg := eq_or_ne n (-m)
  · rw [← one_smul (M := FunctionField) (smulField m), smulField_neg, neg_add_cancel,
      addXYZ_smul, one_mul, neg_one_sq (R := FunctionField), addXYZ_neg nonsingular_smulField.1,
      one_smul, ← neg_add', ← two_mul, ψ_neg, map_neg, ← dblZ_smulPoly, ← map_dblZ, smulField_zero]
    rfl
  have hne : ¬ smulField m ≈ smulField n := fun heq ↦ zsmul_point_ne h <| by
    rw [Point.ext_iff, zsmul_point_eq_smulField, zsmul_point_eq_smulField]
    exact Quotient.sound heq
  have key : (m • jacobianPoint + n • jacobianPoint).point =
      ⟦addXYZ curveField (smulField m) (smulField n)⟧ := by
    rw [Point.add_point, zsmul_point_eq_smulField, zsmul_point_eq_smulField, addMap_eq,
      add_of_not_equiv hne]
  erw [← equiv_iff_eq_of_Z_eq]
  · exact Quotient.exact (by
      rw [smul_eq _ (ψᵤ_ne_zero <| sub_ne_zero_of_ne h.symm).isUnit,
        ← zsmul_point_eq_smulField, add_comm, add_zsmul, key])
  · conv_rhs => rw [smulField, comp_fin3, smul_fin3, (fin3_def_ext _ _ _).2.2, mul_comm]
    simp_rw [addXYZ, fin3_def_ext, ← map_mul, ← addZ_smulPoly, ← map_addZ]
  · rw [(smul_fin3_ext _ _).2.2]
    apply mul_ne_zero <;> apply ψᵤ_ne_zero <;> omega

theorem addXYZ_smulRing :
    addXYZ curveRing (smulRing m) (smulRing n) =
      AdjoinRoot.mk curve.polynomial (curve.ψ (n - m)) • smulRing (n + m) :=
  (IsFractionRing.injective Coord FunctionField).comp_left <| by
    simp_rw [← map_addXYZ, WeierstrassCurve.Jacobian.comp_smul]; exact addXYZ_smulField

theorem addXYZ_smulField₁ :
    addXYZ curveField (smulField n) (smulField (n + 1)) = smulField (2 * n + 1) := by
  rw [addXYZ_smulField, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm, add_assoc]

theorem addXYZ_smulRing₁ :
    addXYZ curveRing (smulRing n) (smulRing (n + 1)) = smulRing (2 * n + 1) := by
  rw [addXYZ_smulRing, add_sub_cancel_left, ψ_one, map_one, one_smul, two_mul, add_comm, add_assoc]


end
end Dubon2026.SourceEllipticUniversal.JacobianFormula
