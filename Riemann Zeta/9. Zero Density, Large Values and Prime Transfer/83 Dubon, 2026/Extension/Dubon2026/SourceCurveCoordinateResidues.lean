import Dubon2026.SourceCurveRamificationOrders
import Mathlib.RingTheory.Polynomial.Quotient

/-! DUB-17/18 -> original principal-divisor degree zero. The residue field
at the zero coordinate on the polynomial base is the actual constant field.
Consequently the pinned inertia degree is the actual place residue degree.
-/
namespace Dubon2026.SourceCurve
noncomputable section
open Polynomial IsDedekindDomain

variable (K : Type*) [Field K]

/-- The zero-coordinate ideal in the polynomial chart. -/
def coordinateZeroIdeal : Ideal K[X] := Ideal.span {X}

theorem coordinateZeroIdeal_ne_bot : coordinateZeroIdeal K ≠ ⊥ := by
  simpa only [coordinateZeroIdeal, ne_eq, Ideal.span_singleton_eq_bot] using (X_ne_zero (R := K))

instance coordinateZeroIdeal_isMaximal : (coordinateZeroIdeal K).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible irreducible_X

/-- Evaluation at zero identifies the polynomial chart's zero residue with constants. -/
def coordinateZeroResidueEquiv : (K[X] ⧸ coordinateZeroIdeal K) ≃ₐ[K] K := by
  exact (Ideal.quotientEquivAlgOfEq K
    (show coordinateZeroIdeal K = Ideal.span {X - C (0 : K)} by
      simp [coordinateZeroIdeal])).trans (quotientSpanXSubCAlgEquiv (0 : K))

variable {K} {F : Type*} [Field F] [Algebra K F]
variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable [Algebra K R] [Algebra K[X] R] [IsScalarTower K K[X] R]
variable [Algebra R F] [IsFractionRing R F] [IsScalarTower K R F]

theorem coordinateZero_inertiaDeg_eq_finrank (P : HeightOneSpectrum R)
    [P.asIdeal.LiesOver (coordinateZeroIdeal K)] :
    (coordinateZeroIdeal K).inertiaDeg P.asIdeal =
      Module.finrank K (Place.ofHeightOneSpectrum (K := K) (F := F) P).ResidueField := by
  rw [Place.finrank_primeResidue, Ideal.inertiaDeg_algebraMap]
  symm
  apply Algebra.finrank_eq_of_equiv_equiv
    (coordinateZeroResidueEquiv K).symm.toRingEquiv (RingEquiv.refl (R ⧸ P.asIdeal))
  ext a
  change algebraMap (K[X] ⧸ coordinateZeroIdeal K) (R ⧸ P.asIdeal)
      ((coordinateZeroResidueEquiv K).symm a) = algebraMap K (R ⧸ P.asIdeal) a
  rw [show (coordinateZeroResidueEquiv K).symm a =
    algebraMap K (K[X] ⧸ coordinateZeroIdeal K) a from
      (coordinateZeroResidueEquiv K).symm.commutes a]
  change algebraMap (K[X] ⧸ coordinateZeroIdeal K) (R ⧸ P.asIdeal)
      (Ideal.Quotient.mk _ (algebraMap K K[X] a)) = _
  exact (IsScalarTower.algebraMap_apply K[X] (K[X] ⧸ coordinateZeroIdeal K)
    (R ⧸ P.asIdeal) (algebraMap K K[X] a)).symm.trans
      (IsScalarTower.algebraMap_apply K K[X] (R ⧸ P.asIdeal) a).symm

end
end Dubon2026.SourceCurve
