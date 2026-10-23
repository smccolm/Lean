import Dubon2026.SourceCurveSeparatingPrincipalDivisor
import Dubon2026.SourceRationalSeparatingCoordinates
import Dubon2026.SourceCurveDivisorDegree

/-! DUB-17/18 -> original Frobenius/inertia -> residue principal divisors ->
rational-function base case for Galois descent. These are literal finite
order divisors on RatFunc. Linear factors have degree zero in all
characteristics by the separating-coordinate degree calculation. -/
namespace Dubon2026.SourceCurve
noncomputable section
attribute [local instance] rational_coordinate_finite rational_coordinate_separable

/-- The literal finite normalized-order divisor of a rational function. -/
def rationalPrincipalDivisor (K : Type*) [Field K] (f : RatFunc K) : Divisor K (RatFunc K) :=
  separatingPrincipalDivisor RatFunc.X RatFunc.transcendental_X f

theorem rationalPrincipalDivisor_apply (K : Type*) [Field K] (f : RatFunc K)
    (v : Place K (RatFunc K)) : rationalPrincipalDivisor K f v = v.ord f := rfl

theorem rationalPrincipalDivisor_mul (K : Type*) [Field K] {f g : RatFunc K}
    (hf : f ≠ 0) (hg : g ≠ 0) :
    rationalPrincipalDivisor K (f * g) = rationalPrincipalDivisor K f + rationalPrincipalDivisor K g :=
  separatingPrincipalDivisor_mul RatFunc.X RatFunc.transcendental_X hf hg

theorem rationalPrincipalDivisor_inv (K : Type*) [Field K] (f : RatFunc K) :
    rationalPrincipalDivisor K f⁻¹ = -rationalPrincipalDivisor K f :=
  separatingPrincipalDivisor_inv RatFunc.X RatFunc.transcendental_X f

theorem rationalPrincipalDivisor_const (K : Type*) [Field K] (c : K) :
    rationalPrincipalDivisor K (algebraMap K (RatFunc K) c) = 0 :=
  separatingPrincipalDivisor_algebraMap RatFunc.X RatFunc.transcendental_X c

theorem degree_rationalPrincipalDivisor_linear (K : Type*) [Field K] (c : K) :
    Divisor.degree (rationalPrincipalDivisor K (RatFunc.X - algebraMap K (RatFunc K) c)) = 0 := by
  rw [Divisor.degree_eq_finsum]
  exact sum_orders_rational_X_sub_const K c

end
end Dubon2026.SourceCurve
