import Dubon2026.SourceEllipticGenericMultiplication

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
open Point in
theorem zsmul_point_ne_zero (h0 : n ≠ 0) : n • jacobianPoint ≠ 0 := by
  rw [jacobianPoint, ← toAffineAddEquiv_symm_apply, ← map_zsmul (toAffineAddEquiv _).symm,
    Ne, map_eq_zero_iff _ (toAffineAddEquiv _).symm.injective]
  exact AffineFormula.zsmul_point_ne_zero h0

theorem zsmul_point_ne (h : m ≠ n) : m • jacobianPoint ≠ n • jacobianPoint := by
  rw [← sub_ne_zero, sub_eq_add_neg, ← sub_zsmul]
  exact zsmul_point_ne_zero (sub_ne_zero.mpr h)

theorem point_point : jacobianPoint.point = ⟦![polyToField (C X), polyToField Y, 1]⟧ := rfl

/-- The integral division-polynomial triple for generic multiplication. -/
abbrev smulPoly (n : ℤ) : Fin 3 → Poly := ![curve.φ n, (ωe curve) n, curve.ψ n]

/-- The division-polynomial triple in the actual universal coordinate ring. -/
abbrev smulRing (n : ℤ) : Fin 3 → Coord := AdjoinRoot.mk _ ∘ smulPoly n

/-- The division-polynomial triple in the actual universal function field. -/
abbrev smulField (n : ℤ) : Fin 3 → FunctionField := polyToField ∘ smulPoly n

theorem algebraMap_comp_smulRing (n : ℤ) : algebraMap _ _ ∘ smulRing n = smulField n := by
  ext i; fin_cases i <;> rfl

theorem zsmul_point_eq_smulField : (n • jacobianPoint).point = ⟦smulField n⟧ := by
  rw [← fin3_def (smulField n), smulField, smulPoly]
  simp_rw [Function.comp, fin3_def_ext]
  obtain rfl | hn := eq_or_ne n 0
  · simp_rw [zero_zsmul, φ_zero, ωe_zero, ψ_zero, map_zero, map_one]; rfl
  obtain ⟨ns, eq⟩ := AffineFormula.zsmul_point_eq_smulX_smulY hn
  change (n • (Point.toAffineAddEquiv _).symm affinePoint).point = _
  rw [← map_zsmul, eq]
  have := ψᵤ_ne_zero hn
  refine Quotient.sound ⟨.mk0 _ (inv_ne_zero this), ?_⟩
  simp_rw [Units.smul_def, WeierstrassCurve.Jacobian.smul_fin3]
  ext i; fin_cases i <;>
    simp only [Units.val_mk0, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] <;>
    field_simp [AffineFormula.smulX, AffineFormula.smulY, this] <;> rfl


end
end Dubon2026.SourceEllipticUniversal.JacobianFormula
