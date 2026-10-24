import Dubon2026.SourceEllipticPointCoordinates
import Dubon2026.SourceEllipticVeluTwoQuotientFibers

/-! Attach the already proved literal degree-two quotient to an actual point
of order two. Its coordinate equation, vanishing Velu y derivative and quotient
ellipticity are derived from that order. This supplies the degree-two branch
of the same cyclic-root map used by the DUB-17/18 inertia argument. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K)

/-- The actual coordinates of a point of order two satisfy the curve equation and Velu derivative condition. -/
theorem two_torsion_coordinates {P : W.toAffine.Point} (hP : addOrderOf P = 2) :
    W.toAffine.Equation (coordsOrZero P).1 (coordsOrZero P).2 ∧
      veluGy W (coordsOrZero P).1 (coordsOrZero P).2 = 0 := by
  rcases P with _ | ⟨x, y, h⟩
  · change addOrderOf (0 : W.toAffine.Point) = 2 at hP
    simp only [addOrderOf_zero] at hP
    omega
  · change W.toAffine.Equation x y ∧ veluGy W x y = 0
    refine ⟨h.1, ?_⟩
    have hkill : (Affine.Point.some x y h : W.toAffine.Point) + Affine.Point.some x y h = 0 := by
      rw [← two_nsmul, ← hP]
      exact addOrderOf_nsmul_eq_zero _
    have he := eq_neg_of_add_eq_zero_left hkill
    rw [Affine.Point.neg_some, Affine.Point.some.injEq] at he
    have hy := he.2
    simp only [Affine.negY] at hy
    simp only [veluGy]
    linear_combination -hy

/-- The literal degree-two quotient is elliptic, with its discriminant derived from the point order. -/
theorem twoQuotient_isElliptic [W.IsElliptic] {P : W.toAffine.Point}
    (hP : addOrderOf P = 2) :
    (veluQuotient2 W (coordsOrZero P).1 (coordsOrZero P).2).IsElliptic :=
  isElliptic_veluQuotient2_of_isElliptic (two_torsion_coordinates W hP).1
    (two_torsion_coordinates W hP).2

/-- The j-value of the actual degree-two quotient by the original point. -/
def twoQuotientJ [W.IsElliptic] {P : W.toAffine.Point} (hP : addOrderOf P = 2) : K :=
  @WeierstrassCurve.j K _ (veluQuotient2 W (coordsOrZero P).1 (coordsOrZero P).2)
    (twoQuotient_isElliptic W hP)

end
end Dubon2026.SourceEllipticVelu
