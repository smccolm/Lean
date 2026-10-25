import Dubon2026.SourceResidueGeometricFrobenius
import Dubon2026.SourceResidueCoefficientPlaceOrders

/-! DUB-17/18 -> original Frobenius quadratic relation -> geometric
Frobenius on residue places. Restriction is the literal valuation-ring
comap along q -> q^p. Its equality with the already constructed coefficient
place supplies discreteness directly, avoiding an unnecessary finiteness
dependency for this comparison. Normalized orders give ramification p.
Adapted from anthropics/fermats-last-theorem, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_reductionModL_smul_of_isFrobeniusAt, Frobenius section. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) (K : Type*) [Field K] (p : ℕ)
  [Fact p.Prime] [CharP K p] [PerfectRing K p]
local notation "FF" => modularFunctionFieldCoeff N K

theorem residueGeometricFrobenius_comap_eq (P : Place K FF) :
    P.toValuationSubring.comap (residueGeometricFrobenius N K p).toRingHom =
      (residueCoefficientPlace N K (frobeniusEquiv K p) P).toValuationSubring := by
  ext f
  change residueGeometricFrobenius N K p f ∈ P.toValuationSubring ↔
    residueCoefficientRingAut N K (frobeniusEquiv K p).symm f ∈ P.toValuationSubring
  rw [residueGeometricFrobenius_eq_inverse_coefficient_pow,
    ← ValuationSubring.valuation_le_one_iff, ← ValuationSubring.valuation_le_one_iff,
    Valuation.map_pow, pow_le_one_iff (Fact.out : p.Prime).ne_zero]

/-- The literal restriction of a residue place along geometric Frobenius. -/
def residueGeometricFrobeniusPlace (P : Place K FF) : Place K FF where
  toValuationSubring := P.toValuationSubring.comap (residueGeometricFrobenius N K p).toRingHom
  algebraMap_mem' a := by
    change residueGeometricFrobenius N K p (algebraMap K FF a) ∈ P.toValuationSubring
    rw [AlgHom.commutes]
    exact P.algebraMap_mem' a
  ne_top' := by
    rw [residueGeometricFrobenius_comap_eq]
    exact (residueCoefficientPlace N K (frobeniusEquiv K p) P).ne_top'
  isPrincipalIdealRing' := by
    rw [residueGeometricFrobenius_comap_eq]
    exact (residueCoefficientPlace N K (frobeniusEquiv K p) P).isPrincipalIdealRing'

theorem residueGeometricFrobeniusPlace_eq_coefficient (P : Place K FF) :
    residueGeometricFrobeniusPlace N K p P =
      residueCoefficientPlace N K (frobeniusEquiv K p) P := by
  apply Place.ext
  exact residueGeometricFrobenius_comap_eq N K p P

theorem residueGeometricFrobenius_place_order (P : Place K FF) (f : FF) :
    P.ord (residueGeometricFrobenius N K p f) =
      (p : ℤ) * (residueGeometricFrobeniusPlace N K p P).ord f := by
  rw [residueGeometricFrobeniusPlace_eq_coefficient, residueCoefficientPlace_ord,
    residueGeometricFrobenius_eq_inverse_coefficient_pow, ← zpow_natCast, P.ord_zpow]

end
end Dubon2026.SourceFunctionField
