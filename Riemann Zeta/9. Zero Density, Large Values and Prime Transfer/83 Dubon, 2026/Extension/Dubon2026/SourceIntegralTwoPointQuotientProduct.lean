import Dubon2026.SourceEllipticTwoQuotientJ
import Dubon2026.SourceIntegralPrimeTwoIdentification
import Dubon2026.SourcePrimeTwoProduct

/-! The already proved integral degree-two identity, indexed by the actual
three distinct cyclic generators. Point coordinates and quotient ellipticity
are derived, so the same point-based root interface as for odd primes applies.
All fields of characteristic different from two, including three, are retained. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial WeierstrassCurve SourceEllipticVelu SourceEllipticFunctionField
open SourcePrimeTwoPolynomial
noncomputable section

/-- The exact degree-two modular polynomial factors through the original three cyclic generators. -/
theorem modularPolynomial_two_eq_pointQuotientProduct
    {K : Type*} [Field K] [DecidableEq K] (W : WeierstrassCurve K) [W.IsElliptic]
    (h2 : (2 : K) ≠ 0) (Q : Fin 3 → W.toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = 2)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i))) :
    relationAtSeed (modularPolynomial 2) W.j = ∏ i, (X - C (twoQuotientJ W (hQ i))) := by
  have hne (i) : Q i ≠ 0 := by
    intro h
    have ho := hQ i
    rw [h, addOrderOf_zero] at ho
    omega
  have hcoords : Function.Injective (fun i => coordsOrZero (Q i)) := by
    intro i j hij
    apply hinj
    apply congrArg AddSubgroup.zmultiples
    rw [← some_coordsOrZero (hne i), ← some_coordsOrZero (hne j), Affine.Point.some.injEq]
    exact ⟨congrArg Prod.fst hij, congrArg Prod.snd hij⟩
  have heq (i) := (two_torsion_coordinates W (hQ i)).1
  have hgy (i) := (two_torsion_coordinates W (hQ i)).2
  have hΔ (i) : (veluQuotient2 W (coordsOrZero (Q i)).1 (coordsOrZero (Q i)).2).Δ ≠ 0 :=
    (@WeierstrassCurve.isUnit_Δ _ _ _ (twoQuotient_isElliptic W (hQ i))).ne_zero
  change fibrePoly (modularPolynomial 2) W.j = _
  rw [modularPolynomial_two_eq_phiTwo]
  exact fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j h2 W (Fintype.card_fin 3)
    (fun i => coordsOrZero (Q i)) hcoords heq hgy hΔ

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
