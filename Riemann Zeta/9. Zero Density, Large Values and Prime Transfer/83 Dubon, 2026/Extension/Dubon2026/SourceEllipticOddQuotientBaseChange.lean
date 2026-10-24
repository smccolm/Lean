import Dubon2026.SourceEllipticOddQuotient

/-! Base change of the literal odd quotient and its j-invariant. The existing
native point map and finite-sum coefficient identities do the work. This
transports the actual factors of the odd-prime modular-polynomial product,
needed for cyclic-root correspondence and the DUB-17/18 inertia census. -/

namespace Dubon2026.SourceEllipticVelu.OddDiscriminant
open WeierstrassCurve
noncomputable section

variable {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
variable (f : F →+* K) (W : WeierstrassCurve F)

/-- The actual finite odd quotient commutes with a field embedding. -/
theorem oddQuotient_map (Q : W.toAffine.Point) (n : ℕ) :
    veluQuotient (W.map f) (oddOrderSummingSet (W.map f) (pointMapHom f W Q) n) =
      (veluQuotient W (oddOrderSummingSet W Q n)).map f := by
  rw [map_oddOrderSummingSet, Finset.map_eq_image]
  exact (veluQuotient_map f W _ (f.injective.prodMap f.injective).injOn).symm

/-- The actual odd quotient j-value commutes with a field embedding. -/
theorem oddQuotient_j_map (Q : W.toAffine.Point) (n : ℕ)
    [hE : (veluQuotient W (oddOrderSummingSet W Q n)).IsElliptic]
    [hE' : (veluQuotient (W.map f)
      (oddOrderSummingSet (W.map f) (pointMapHom f W Q) n)).IsElliptic] :
    (veluQuotient (W.map f)
      (oddOrderSummingSet (W.map f) (pointMapHom f W Q) n)).j =
      f (veluQuotient W (oddOrderSummingSet W Q n)).j := by
  have hj : ∀ (V : WeierstrassCurve K)
      (hV : V = (veluQuotient W (oddOrderSummingSet W Q n)).map f)
      (h : V.IsElliptic), @WeierstrassCurve.j K _ V h =
        f (veluQuotient W (oddOrderSummingSet W Q n)).j := by
    rintro V rfl h
    exact WeierstrassCurve.map_j _ f
  exact hj _ (oddQuotient_map f W Q n) hE'

end
end Dubon2026.SourceEllipticVelu.OddDiscriminant
