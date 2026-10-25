import Dubon2026.SourceResidueGeometricFrobeniusPlaces
import Dubon2026.SourceResidueCoefficientDivisors

/-! DUB-17/18 -> original Frobenius quadratic relation -> geometric
Frobenius on finite residue divisors. The literal geometric place map gives
finite-support pushforward. Its equality with the coefficient permutation
proves degree and principal-divisor preservation. Over the actual closed
constant field all place residue degrees are one. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) (K : Type*) [Field K] (p : ℕ)
  [Fact p.Prime] [CharP K p] [PerfectRing K p]
local notation "FF" => modularFunctionFieldCoeff N K

/-- Finite divisor pushforward along the literal geometric Frobenius place map. -/
def residueGeometricFrobeniusDivisor : Divisor K FF →+ Divisor K FF :=
  Finsupp.mapDomain.addMonoidHom (residueGeometricFrobeniusPlace N K p)

theorem residueGeometricFrobeniusDivisor_eq_coefficient (D : Divisor K FF) :
    residueGeometricFrobeniusDivisor N K p D =
      residueCoefficientDivisorEquiv N K (frobeniusEquiv K p) D := by
  induction D using Finsupp.induction with
  | zero => rw [map_zero, map_zero]
  | single_add P n D _ _ ih =>
    rw [map_add, map_add, ih]
    congr 1
    change Finsupp.mapDomain (residueGeometricFrobeniusPlace N K p) (Finsupp.single P n) =
      Finsupp.equivMapDomain (residueCoefficientPlaceEquiv N K (frobeniusEquiv K p))
        (Finsupp.single P n)
    rw [Finsupp.mapDomain_single, Finsupp.equivMapDomain_single,
      residueGeometricFrobeniusPlace_eq_coefficient]
    rfl

theorem residueGeometricFrobeniusDivisor_degree [NeZero N] [IsAlgClosed K]
    (D : Divisor K FF) :
    Divisor.degree (residueGeometricFrobeniusDivisor N K p D) = Divisor.degree D := by
  rw [residueGeometricFrobeniusDivisor_eq_coefficient, residueCoefficientDivisor_degree]

theorem residueGeometricFrobeniusDivisor_principal (D : Divisor K FF)
    (hD : Divisor.IsPrincipal D) :
    Divisor.IsPrincipal (residueGeometricFrobeniusDivisor N K p D) := by
  rw [residueGeometricFrobeniusDivisor_eq_coefficient]
  exact residueCoefficientDivisor_principal N K (frobeniusEquiv K p) D hD

end
end Dubon2026.SourceFunctionField
