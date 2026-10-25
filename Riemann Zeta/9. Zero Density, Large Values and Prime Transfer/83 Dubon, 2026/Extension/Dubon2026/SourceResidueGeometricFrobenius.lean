import Dubon2026.SourceArithmeticFrobeniusResidue
import Dubon2026.SourceLaurentFrobenius
import Dubon2026.SourceLaurentCoefficientReindex

/-! DUB-17/18 -> original Frobenius quadratic relation -> geometric
and arithmetic residue Frobenius. The actual geometric field map is inverse
coefficient Frobenius followed by pth power. Its literal Laurent expansion
is q -> q^p, and every element satisfies its explicit monic polynomial.
The short Laurent comparison is adapted from anthropics/fermats-last-theorem,
Apache-2.0, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_reductionModL_smul_of_isFrobeniusAt, Frobenius section. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
variable (N : ℕ) (K : Type*) [Field K] (p : ℕ)
  [Fact p.Prime] [CharP K p] [PerfectRing K p]
local notation "FF" => modularFunctionFieldCoeff N K

/-- The actual geometric Frobenius of the residue modular function field. -/
def residueGeometricFrobenius : FF →ₐ[K] FF :=
  { (frobenius FF p).comp
      (residueCoefficientRingAut N K (frobeniusEquiv K p).symm).toRingHom with
    commutes' := fun a => by
      change (residueCoefficientRingAut N K (frobeniusEquiv K p).symm
        (algebraMap K FF a)) ^ p = algebraMap K FF a
      rw [residueCoefficientRingAut_constants, ← map_pow]
      exact congrArg (algebraMap K FF) ((frobeniusEquiv K p).apply_symm_apply a) }

theorem residueGeometricFrobenius_eq_inverse_coefficient_pow (f : FF) :
    residueGeometricFrobenius N K p f =
      (residueCoefficientRingAut N K (frobeniusEquiv K p).symm f) ^ p := rfl

theorem residueGeometricFrobenius_coe (f : FF) :
    (residueGeometricFrobenius N K p f : LaurentSeries K) = qExpand K p f.val := by
  change (coeffMap (frobeniusEquiv K p).symm.toRingHom f.val) ^ p = qExpand K p f.val
  rw [pow_char_eq_coeffMap_frobenius_qExpand, ← coeffMap_qExpand, coeffMap_coeffMap]
  have he : (frobenius K p).comp (frobeniusEquiv K p).symm.toRingHom = RingHom.id K := by
    ext a
    exact (frobeniusEquiv K p).apply_symm_apply a
  rw [he, coeffMap_id]

theorem residueGeometricFrobenius_coefficient (f : FF) :
    residueGeometricFrobenius N K p (residueCoefficientRingAut N K (frobeniusEquiv K p) f) =
      f ^ p := by
  rw [residueGeometricFrobenius_eq_inverse_coefficient_pow]
  congr 1
  apply Subtype.ext
  ext n
  exact (frobeniusEquiv K p).symm_apply_apply (f.val.coeff n)

theorem residueGeometricFrobenius_isIntegral :
    (residueGeometricFrobenius N K p).toRingHom.IsIntegral := by
  intro f
  refine ⟨Polynomial.X ^ p - Polynomial.C (residueCoefficientRingAut N K (frobeniusEquiv K p) f),
    Polynomial.monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero, ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero]
  exact (residueGeometricFrobenius_coefficient N K p f).symm

end
end Dubon2026.SourceFunctionField
