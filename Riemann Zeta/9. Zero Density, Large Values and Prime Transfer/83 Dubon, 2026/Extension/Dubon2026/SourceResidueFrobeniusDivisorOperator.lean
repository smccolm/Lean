import Dubon2026.SourceResidueGeometricFrobeniusDivisors

/-! DUB-17/18 -> Hecke reduction on torsion -> residue principal orders.
The actual geometric place restriction is bijective with ramification p.
Its pullback is therefore the inverse place permutation weighted by p.
The existing literal pushforward plus this pullback gives the exact
Frobenius divisor operator required by the original norm residue formula. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) (K : Type*) [Field K]
local notation "FF" => modularFunctionFieldCoeff N K

theorem residueCoefficientDivisorEquiv_order (e : K ≃+* K)
    (D : Divisor K FF) (f : FF) (hD : ∀ P, D P = P.ord f) (P : Place K FF) :
    residueCoefficientDivisorEquiv N K e D P = P.ord (residueCoefficientRingAut N K e f) := by
  obtain ⟨Q, rfl⟩ := (residueCoefficientPlaceEquiv N K e).surjective P
  change residueCoefficientDivisorEquiv N K e D (residueCoefficientPlace N K e Q) =
    (residueCoefficientPlace N K e Q).ord (residueCoefficientRingAut N K e f)
  rw [residueCoefficientDivisorEquiv_apply, residueCoefficientPlace_ord_action, hD]

variable (p : ℕ) [Fact p.Prime] [CharP K p] [PerfectRing K p]

/-- Pullback under the actual bijective geometric place restriction, weighted by its ramification p. -/
def residueGeometricFrobeniusPullbackDivisor : Divisor K FF →+ Divisor K FF :=
  p • (residueCoefficientDivisorEquiv N K (frobeniusEquiv K p)).symm.toAddMonoidHom

theorem residueGeometricFrobeniusPullbackDivisor_apply (D : Divisor K FF) (P : Place K FF) :
    residueGeometricFrobeniusPullbackDivisor N K p D P =
      (p : ℤ) * D (residueGeometricFrobeniusPlace N K p P) := by
  change (p • ((residueCoefficientDivisorEquiv N K (frobeniusEquiv K p)).symm D)) P = _
  rw [Finsupp.smul_apply, nsmul_eq_mul, residueGeometricFrobeniusPlace_eq_coefficient]
  congr 1

theorem residueGeometricFrobeniusPullbackDivisor_order
    (D : Divisor K FF) (f : FF) (hD : ∀ P, D P = P.ord f) (P : Place K FF) :
    residueGeometricFrobeniusPullbackDivisor N K p D P =
      P.ord (residueGeometricFrobenius N K p f) := by
  rw [residueGeometricFrobeniusPullbackDivisor_apply, hD, residueGeometricFrobenius_place_order]

/-- The sum of the actual geometric Frobenius pushforward and ramified pullback. -/
def residueFrobeniusDivisorOperator : Divisor K FF →+ Divisor K FF :=
  residueGeometricFrobeniusDivisor N K p + residueGeometricFrobeniusPullbackDivisor N K p

theorem residueFrobeniusDivisorOperator_order
    (D : Divisor K FF) (f : FF) (hf : f ≠ 0) (hD : ∀ P, D P = P.ord f) (P : Place K FF) :
    residueFrobeniusDivisorOperator N K p D P =
      P.ord (residueCoefficientRingAut N K (frobeniusEquiv K p) f *
        residueGeometricFrobenius N K p f) := by
  change residueGeometricFrobeniusDivisor N K p D P +
    residueGeometricFrobeniusPullbackDivisor N K p D P = _
  rw [residueGeometricFrobeniusDivisor_eq_coefficient,
    residueCoefficientDivisorEquiv_order N K _ D f hD,
    residueGeometricFrobeniusPullbackDivisor_order N K p D f hD,
    P.ord_mul ((map_ne_zero _).mpr hf) ((map_ne_zero _).mpr hf)]

end
end Dubon2026.SourceFunctionField
