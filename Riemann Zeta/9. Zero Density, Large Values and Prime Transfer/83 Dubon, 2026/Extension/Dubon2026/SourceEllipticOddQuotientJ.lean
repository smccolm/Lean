import Dubon2026.SourceEllipticOddQuotientBaseChange

/-! The j-invariant of the literal odd quotient, with its ellipticity supplied
by the proved discriminant identity. Its field-embedding compatibility fixes
the factors in the odd-prime product used by the DUB-17/18 cyclic-root argument.
-/

namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]

/-- The j-value of the actual odd quotient, with no ellipticity certificate assumed. -/
def oddQuotientJ (W : WeierstrassCurve F) [W.IsElliptic]
    {Q : W.toAffine.Point} {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1) : F :=
  @WeierstrassCurve.j F _ (veluQuotient W (oddOrderSummingSet W Q n))
    (odd_quotient_isElliptic W Q hQ)

/-- The same actual quotient j-value after a field embedding. -/
theorem oddQuotientJ_map (f : F →+* K) (W : WeierstrassCurve F) [W.IsElliptic]
    {Q : W.toAffine.Point} {n : ℕ} (hQ : addOrderOf Q = 2 * n + 1)
    (hQ' : addOrderOf (pointMapHom f W Q) = 2 * n + 1) :
    oddQuotientJ (W.map f) hQ' = f (oddQuotientJ W hQ) := by
  letI := odd_quotient_isElliptic W Q hQ
  letI := odd_quotient_isElliptic (W.map f) (pointMapHom f W Q) hQ'
  exact oddQuotient_j_map f W Q n

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
