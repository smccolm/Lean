import Dubon2026.SourceEllipticDivisionCoordinates

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> modular good reduction ->
reverse genus -> finite exceptional-fiber census -> elliptic cyclic-subgroup
inertia -> actual torsion cardinality -> actual point multiplication formula.
These are identities for the native division polynomials of the actual
Weierstrass equation. Adapted from anthropics/fermats-last-theorem, Apache-2.0,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2, EDSEngine. The point
multiplication formula and torsion cardinality remain to be proved. -/
namespace Dubon2026.SourceEllipticDivision
open WeierstrassCurve Polynomial
open scoped Polynomial.Bivariate
variable {R S : Type*} [CommRing R] [CommRing S] (W : WeierstrassCurve R)
noncomputable section
variable (f : R →+* S)

theorem map_ψc (n : ℤ) : (ψc (W.map f)) n = ((ψc W) n).map (mapRingHom f) := by
  simp only [ψc, ← coe_mapRingHom, map_complEDS₂, map_ψ₂, map_Ψ₃, map_preΨ₄]
  simp only [coe_mapRingHom, map_C]

theorem map_invar : (invar (W.map f)) = (invar W).map f := by
  simp only [invar, map_b₂, map_b₄]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_ofNat,
    map_C, map_X]

open WeierstrassCurve.Affine Dubon2026.SourceEllipticSequence in
theorem map_ωe (n : ℤ) : (ωe (W.map f)) n = ((ωe W) n).map (mapRingHom f) := by
  simp_rw [ωe, ← coe_mapRingHom, map_add, map_sub, map_mul, map_redInvarDenom,
    map_complEDS₂Aux, map_polynomial, map_polynomialX, map_polynomialY, map_negPolynomial,
    map_ψ₂, map_Ψ₃, map_preΨ₄, map_Ψ₂Sq, map_ψ]; simp

end
end Dubon2026.SourceEllipticDivision
