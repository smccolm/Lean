import Dubon2026.SourceIntegralCountableOddQuotientProduct
import Dubon2026.SourceEllipticSubfieldPointLift

/-! Map the proved countable-field product to the original curve.
Coordinate membership gives genuine point lifts; injectivity then derives
their exact orders and distinct cyclic subgroups. These hypotheses are not
independent descent certificates. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open WeierstrassCurve SourceEllipticVelu SourceEllipticVelu.OddDiscriminant

/-- Transfer the actual quotient product from a countable model containing the point coordinates. -/
theorem modularPolynomial_eq_oddQuotientProduct_countable_model
    {F K : Type*} [Field F] [Field K] [DecidableEq F] [DecidableEq K]
    [Algebra ℚ K] [Countable K] (f : K →+* F)
    (V : WeierstrassCurve K) [V.IsElliptic] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Q : Fin (p + 1) → (V.map f).toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i)))
    (hx : ∀ i, (coordsOrZero (Q i)).1 ∈ Set.range f)
    (hy : ∀ i, (coordsOrZero (Q i)).2 ∈ Set.range f) :
    relationAtSeed (modularPolynomial p) (V.map f).j = oddQuotientProduct (V.map f) hQ := by
  classical
  choose R hR using fun i => exists_pointMapHom_of_coordinates f V (Q i) (hx i) (hy i)
  have hRi : ∀ i, addOrderOf (R i) = 2 * (p / 2) + 1 := by
    intro i
    rw [← addOrderOf_injective _ (pointMapHom_injective f V), hR, hQ]
  have hRinj : Function.Injective (fun i => AddSubgroup.zmultiples (R i)) := by
    intro i j h
    apply hinj
    have he := congrArg (AddSubgroup.map (pointMapHom f V)) h
    simpa only [AddMonoidHom.map_zmultiples, hR] using he
  have hQ' : ∀ i, addOrderOf (pointMapHom f V (R i)) = 2 * (p / 2) + 1 := by
    intro i
    rw [hR, hQ]
  have hprod := (modularPolynomial_eq_oddQuotientProduct_map_iff f V hRi hQ' p).mpr
    (modularPolynomial_eq_oddQuotientProduct_countable V p hp2 R hRi hRinj)
  have he : (fun i => pointMapHom f V (R i)) = Q := funext hR
  simpa only [he] using hprod

/-- The actual quotient product respects equality transport of the original curve and points. -/
theorem oddQuotientProduct_cast {F : Type*} [Field F] [DecidableEq F]
    {W V : WeierstrassCurve F} [W.IsElliptic] [V.IsElliptic] (h : W = V)
    {ι : Type*} [Fintype ι] {n : ℕ} {Q : ι → W.toAffine.Point}
    (hQ : ∀ i, addOrderOf (Q i) = 2 * n + 1)
    (hQ' : ∀ i, addOrderOf
      (AddEquiv.cast (M := fun E : WeierstrassCurve F => E.toAffine.Point) h (Q i)) =
        2 * n + 1) :
    oddQuotientProduct V hQ' = oddQuotientProduct W hQ := by
  subst V
  rfl

end Dubon2026.SourceFunctionField.IntegralJCoordinate
