import Dubon2026.SourceIntegralResidueOddQuotientProduct
import Dubon2026.SourceEllipticWittModel

/-! The exact odd-prime quotient product in positive characteristic over a
perfect field. The original points pass through an actual field embedding and
the constructed Witt model. All torsion lifts and integral quotient models
are supplied by the proved residue product theorem. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open WeierstrassCurve IsLocalRing SourceWittLift SourceEllipticVelu.OddDiscriminant
noncomputable section

/-- The original odd-prime quotient product over any perfect field of positive characteristic. -/
theorem modularPolynomial_eq_oddQuotientProduct_perfect
    {K : Type*} [Field K] [DecidableEq K] (q : ℕ) [Fact q.Prime]
    [CharP K q] [PerfectRing K q]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    (Q : Fin (p + 1) → W.toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i))) :
    relationAtSeed (modularPolynomial p) W.j = oddQuotientProduct W hQ := by
  classical
  letI := fractionClosure_charZero q K
  obtain ⟨A, V, ι, hV, he⟩ := exists_good_integral_model (p := q) W
  letI : V.IsElliptic := hV
  have hpA : IsUnit (p : A) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast, map_zero] using ι.injective.ne hp
  let e := AddEquiv.cast (M := fun E : WeierstrassCurve (ResidueField A) => E.toAffine.Point)
    he.symm
  let f := e.toAddMonoidHom.comp (pointMapHom ι W)
  have hf : Function.Injective f := e.injective.comp (pointMapHom_injective ι W)
  let R := fun i => f (Q i)
  have hR : ∀ i, addOrderOf (R i) = 2 * (p / 2) + 1 := by
    intro i
    exact (addOrderOf_injective f hf (Q i)).trans (hQ i)
  have hRinj : Function.Injective (fun i => AddSubgroup.zmultiples (R i)) := by
    intro i j hij
    apply hinj
    apply AddSubgroup.map_injective (f := f) hf
    simpa only [AddMonoidHom.map_zmultiples] using hij
  have hQi : ∀ i, addOrderOf (pointMapHom ι W (Q i)) = 2 * (p / 2) + 1 := by
    intro i
    exact (addOrderOf_injective _ (pointMapHom_injective ι W) (Q i)).trans (hQ i)
  have hs := modularPolynomial_eq_oddQuotientProduct_residue A V p hp2 hpA R hR hRinj
  have hc := oddQuotientProduct_cast he.symm hQi hR
  apply (modularPolynomial_eq_oddQuotientProduct_map_iff ι W hQ hQi p).mp
  simpa only [he] using hs.trans hc

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
