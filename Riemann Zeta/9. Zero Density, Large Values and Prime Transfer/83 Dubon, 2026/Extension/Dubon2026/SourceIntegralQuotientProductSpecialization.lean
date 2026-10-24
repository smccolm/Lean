import Dubon2026.SourceIntegralPrimeConjugateProduct
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-! Specialization of the actual integral modular-polynomial product through
integral elliptic curve models. The generic equality is descended using the
injective coefficient map, then transported along the residue map. The later
odd-prime application must construct those integral quotient models and prove
the generic product identity; neither input is claimed here. This removes the
polynomial descent step from that application on the DUB-17/18 cyclic-root,
inertia census and good-reduction dependency chain. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial WeierstrassCurve

variable {R L K : Type*} [CommRing R] [Field L] [Field K]
variable {ι : Type*} [Fintype ι]

/-- An actual integral family specializes its generic modular-polynomial identity. -/
theorem modularPolynomial_quotient_product_specializes
    (f : R →+* L) (hf : Function.Injective f) (g : R →+* K)
    (W : WeierstrassCurve R) [W.IsElliptic]
    (V : ι → WeierstrassCurve R) [∀ i, (V i).IsElliptic]
    (p : ℕ) [NeZero p]
    (hprod : relationAtSeed (modularPolynomial p) (W.map f).j =
      ∏ i, (X - C ((V i).map f).j)) :
    relationAtSeed (modularPolynomial p) (W.map g).j =
      ∏ i, (X - C ((V i).map g).j) := by
  have hR : relationAtSeed (modularPolynomial p) W.j = ∏ i, (X - C (V i).j) := by
    apply Polynomial.map_injective f hf
    rw [relationAtSeed_map, Polynomial.map_prod]
    simpa only [WeierstrassCurve.map_j, Polynomial.map_sub, Polynomial.map_X,
      Polynomial.map_C] using hprod
  rw [WeierstrassCurve.map_j, ← relationAtSeed_map, hR, Polynomial.map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, WeierstrassCurve.map_j]

end Dubon2026.SourceFunctionField.IntegralJCoordinate
