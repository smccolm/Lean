import Dubon2026.SourceIntegralCountableModelProduct

/-! The exact odd-prime quotient product over every characteristic-zero
coefficient field. The proof restricts the actual finite coefficient data,
constructs the complex embedding, and returns to the original curve and
points. This removes general coefficient descent from the DUB-17/18
modular-curve reduction chain. Integral lifts and reduction remain needed. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open WeierstrassCurve SourceEllipticVelu SourceEllipticVelu.OddDiscriminant

/-- The exact integral modular polynomial factors into the actual odd-prime quotient j-factors
over an arbitrary characteristic-zero field. No complex embedding or coefficient model is supplied. -/
theorem modularPolynomial_eq_oddQuotientProduct_charZero
    {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (W : WeierstrassCurve F) [W.IsElliptic] (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (Q : Fin (p + 1) → W.toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i))) :
    relationAtSeed (modularPolynomial p) W.j = oddQuotientProduct W hQ := by
  classical
  let K := Subfield.closure (curvePointCoefficients W Q)
  have hc : {W.a₁, W.a₂, W.a₃, W.a₄, W.a₆} ⊆ (K : Set F) := by
    intro a ha
    apply Subfield.subset_closure
    exact Or.inl (Or.inl ha)
  let V := curveOverSubfield W K hc
  letI : Countable K := countable_curvePointField W Q
  have hv : V.map K.subtype = W := curveOverSubfield_map W K hc
  let e := AddEquiv.cast (M := fun E : WeierstrassCurve F => E.toAffine.Point) hv.symm
  let Q' := fun i => e (Q i)
  have hQ' : ∀ i, addOrderOf (Q' i) = 2 * (p / 2) + 1 := by
    intro i
    rw [show Q' i = e (Q i) from rfl, e.addOrderOf_eq, hQ]
  have hi' : Function.Injective (fun i => AddSubgroup.zmultiples (Q' i)) := by
    intro i j hij
    apply hinj
    apply AddSubgroup.map_injective (f := e.toAddMonoidHom) e.injective
    simpa only [AddMonoidHom.map_zmultiples] using hij
  have hcoords : ∀ i, coordsOrZero (Q' i) = coordsOrZero (Q i) :=
    fun i => coordsOrZero_cast hv.symm (Q i)
  have hx : ∀ i, (coordsOrZero (Q' i)).1 ∈ Set.range K.subtype := by
    intro i
    rw [hcoords]
    refine ⟨⟨_, Subfield.subset_closure ?_⟩, rfl⟩
    exact Or.inl (Or.inr ⟨i, rfl⟩)
  have hy : ∀ i, (coordsOrZero (Q' i)).2 ∈ Set.range K.subtype := by
    intro i
    rw [hcoords]
    refine ⟨⟨_, Subfield.subset_closure ?_⟩, rfl⟩
    exact Or.inr ⟨i, rfl⟩
  have hp := modularPolynomial_eq_oddQuotientProduct_countable_model
    K.subtype V p hp2 Q' hQ' hi' hx hy
  have hprod : oddQuotientProduct (V.map K.subtype) hQ' = oddQuotientProduct W hQ :=
    oddQuotientProduct_cast hv.symm hQ hQ'
  rw [hprod] at hp
  simpa only [hv] using hp

end Dubon2026.SourceFunctionField.IntegralJCoordinate
