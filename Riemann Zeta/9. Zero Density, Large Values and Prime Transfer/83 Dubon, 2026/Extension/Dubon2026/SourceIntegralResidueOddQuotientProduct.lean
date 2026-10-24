import Dubon2026.SourceIntegralCharZeroOddQuotientProduct
import Dubon2026.SourceEllipticIntegralOddQuotientReduction
import Dubon2026.SourceEllipticCyclicTorsionLift
import Dubon2026.SourceIntegralQuotientProductSpecialization

/-! The actual odd-prime quotient product on the residue field of a good
integral elliptic model in an algebraically closed characteristic-zero field.
The actual torsion generators lift, their exact orders and distinct kernels
are derived, and all integral quotient models and their good reduction are
constructed. The generic product identity is the proved characteristic-zero
theorem. No lifting, quotient model or product certificate remains assumed. -/

namespace Dubon2026.SourceFunctionField.IntegralJCoordinate
open Polynomial WeierstrassCurve IsLocalRing SourceEllipticReduction
open SourceEllipticVelu SourceEllipticVelu.OddDiscriminant
noncomputable section

/-- The full odd-prime modular-polynomial product specializes with all quotient models constructed. -/
theorem modularPolynomial_eq_oddQuotientProduct_residue
    {L : Type*} [Field L] [CharZero L] [IsAlgClosed L] [DecidableEq L]
    (A : ValuationSubring L) [DecidableEq (ResidueField A)]
    (W : WeierstrassCurve A) [W.IsElliptic]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : A))
    (Q : Fin (p + 1) → (W.map (residue A)).toAffine.Point)
    (hQ : ∀ i, addOrderOf (Q i) = 2 * (p / 2) + 1)
    (hinj : Function.Injective (fun i => AddSubgroup.zmultiples (Q i))) :
    relationAtSeed (modularPolynomial p) (W.map (residue A)).j =
      oddQuotientProduct (W.map (residue A)) hQ := by
  classical
  have hpodd : p = 2 * (p / 2) + 1 := by
    have ho := (Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2
    obtain ⟨m, hm⟩ := ho
    omega
  have hN : IsUnit ((2 * (p / 2) + 1 : ℕ) : A) := hpodd ▸ hp
  have hΔ : (W.map (residue A)).Δ ≠ 0 := (W.map (residue A)).isUnit_Δ.ne_zero
  obtain ⟨R, hR, hred, hRinj⟩ := exists_cyclic_generator_lifts hΔ hN Q hQ hinj
  let V := fun i => integralOddQuotientModel A W hN (R i)
    (hR i ▸ addOrderOf_nsmul_eq_zero (R i)) (p / 2)
  letI (i : Fin (p + 1)) : (V i).IsElliptic :=
    integralOddQuotientModel_isElliptic hΔ hN (R i) (hR i)
  have hgen (i : Fin (p + 1)) :
      ((V i).map A.subtype).j = oddQuotientJ (W.map A.subtype) (hR i) := by
    have he := integralOddQuotientModel_map A W hN (R i)
      (hR i ▸ addOrderOf_nsmul_eq_zero (R i)) (p / 2)
    change ((integralOddQuotientModel A W hN (R i) _ (p / 2)).map A.subtype).j = _
    simp only [he, oddQuotientJ]
  have hres (i : Fin (p + 1)) :
      ((V i).map (residue A)).j = oddQuotientJ (W.map (residue A)) (hQ i) := by
    have he := integralOddQuotientModel_residue hΔ hN (R i) (hR i)
    change ((integralOddQuotientModel A W hN (R i) _ (p / 2)).map (residue A)).j = _
    simp only [he, hred, oddQuotientJ]
  have hg : relationAtSeed (modularPolynomial p) (W.map A.subtype).j =
      ∏ i, (X - C ((V i).map A.subtype).j) := by
    simpa only [hgen, oddQuotientProduct] using
      modularPolynomial_eq_oddQuotientProduct_charZero (W.map A.subtype) p hp2 R hR hRinj
  have hs := modularPolynomial_quotient_product_specializes A.subtype A.subtype_injective
    (residue A) W V p hg
  simpa only [hres, oddQuotientProduct] using hs

end
end Dubon2026.SourceFunctionField.IntegralJCoordinate
