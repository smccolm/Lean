import Dubon2026.SourceEllipticTwoQuotientJ
import Dubon2026.SourceEllipticOddBaseChange

/-! The degree-two branch of field-map compatibility for the actual cyclic
root map. This is needed for its inertia equivariance on the DUB-17/18
exceptional-fiber census chain. Reuse the original coordinate map and literal
Velu coefficients; no new quotient or curve-isomorphism framework is needed. -/

namespace Dubon2026.SourceEllipticVelu
open WeierstrassCurve OddDiscriminant
noncomputable section

/-- The literal degree-two quotient commutes with coefficient specialization. -/
theorem veluQuotient2_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (W : WeierstrassCurve R) (x y : R) :
    veluQuotient2 (W.map f) (f x) (f y) = (veluQuotient2 W x y).map f := by
  ext <;> simp [veluQuotient2, veluGx, map_b₂, map_ofNat]

/-- The actual order-two quotient j-value is preserved by a field embedding. -/
theorem twoQuotientJ_map {F K : Type*} [Field F] [Field K]
    [DecidableEq F] [DecidableEq K]
    (f : F →+* K) (W : WeierstrassCurve F) [W.IsElliptic]
    {P : W.toAffine.Point} (hP : addOrderOf P = 2)
    (hP' : addOrderOf (pointMapHom f W P) = 2) :
    twoQuotientJ (W.map f) hP' = f (twoQuotientJ W hP) := by
  letI := twoQuotient_isElliptic W hP
  have he : veluQuotient2 (W.map f)
      (coordsOrZero (pointMapHom f W P)).1 (coordsOrZero (pointMapHom f W P)).2 =
      (veluQuotient2 W (coordsOrZero P).1 (coordsOrZero P).2).map f := by
    rw [coordsOrZero_pointMapHom]
    exact veluQuotient2_map f W _ _
  have hj : ∀ (V : WeierstrassCurve K)
      (hV : V = (veluQuotient2 W (coordsOrZero P).1 (coordsOrZero P).2).map f)
      (h : V.IsElliptic), @WeierstrassCurve.j K _ V h =
        f (veluQuotient2 W (coordsOrZero P).1 (coordsOrZero P).2).j := by
    rintro V rfl h
    exact WeierstrassCurve.map_j _ f
  exact hj _ he (twoQuotient_isElliptic (W.map f) hP')

end
end Dubon2026.SourceEllipticVelu
