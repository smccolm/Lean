import Dubon2026.SourceResidueFrobeniusDivisorOperator
import Dubon2026.SourceResidueCoefficientPicard

/-! DUB-17/18 -> original Tate quadratic relation -> reduction on actual
Picard classes. Descend the already identified Frobenius divisor operator.
Its composition with coefficient Frobenius is F squared plus p, using the
inverse permutation on divisors. These are the quotient identities required
to compare the actual original Hecke and arithmetic Frobenius actions. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) (K : Type*) [Field K]
local notation "FF" => modularFunctionFieldCoeff N K

theorem residueCoefficientDivisorEquiv_symm (e : K ≃+* K) (D : Divisor K FF) :
    (residueCoefficientDivisorEquiv N K e).symm D =
      residueCoefficientDivisorEquiv N K e.symm D := by
  ext P
  rfl

variable [NeZero N] [IsAlgClosed K]

theorem residueCoefficientPicard_inverse (e : K ≃+* K) (x : Pic0 K FF) :
    residueCoefficientPicard N K e.symm (residueCoefficientPicard N K e x) = x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [residueCoefficientPicard_mk, residueCoefficientPicard_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  change residueCoefficientDivisorEquiv N K e.symm
    (residueCoefficientDivisorEquiv N K e D.val) = D.val
  rw [← residueCoefficientDivisorEquiv_symm, AddEquiv.symm_apply_apply]

variable (p : ℕ) [Fact p.Prime] [CharP K p]

omit [NeZero N] in
theorem residueFrobeniusDivisorOperator_eq (D : Divisor K FF) :
    residueFrobeniusDivisorOperator N K p D =
      residueCoefficientDivisorEquiv N K (frobeniusEquiv K p) D +
        p • residueCoefficientDivisorEquiv N K (frobeniusEquiv K p).symm D := by
  change residueGeometricFrobeniusDivisor N K p D +
    p • (residueCoefficientDivisorEquiv N K (frobeniusEquiv K p)).symm D = _
  rw [residueGeometricFrobeniusDivisor_eq_coefficient, residueCoefficientDivisorEquiv_symm]

theorem residueFrobeniusDivisorOperator_mem_degZero
    (D : Divisor.degZero (K := K) (F := FF)) :
    residueFrobeniusDivisorOperator N K p D.val ∈ Divisor.degZero := by
  change Divisor.degree (residueFrobeniusDivisorOperator N K p D.val) = 0
  rw [residueFrobeniusDivisorOperator_eq, map_add, map_nsmul,
    residueCoefficientDivisor_degree, residueCoefficientDivisor_degree,
    (show Divisor.degree D.val = 0 from D.property), nsmul_zero, add_zero]

/-- The actual residue Frobenius divisor correspondence descended to degree-zero classes. -/
def residueFrobeniusPicardOperator : Pic0 K FF →+ Pic0 K FF :=
  residueCoefficientPicard N K (frobeniusEquiv K p) +
    p • residueCoefficientPicard N K (frobeniusEquiv K p).symm

theorem residueFrobeniusPicardOperator_mk (D : Divisor.degZero (K := K) (F := FF)) :
    residueFrobeniusPicardOperator N K p (Pic0.mk D) =
      Pic0.mk ⟨residueFrobeniusDivisorOperator N K p D.val,
        residueFrobeniusDivisorOperator_mem_degZero N K p D⟩ := by
  change residueCoefficientPicard N K (frobeniusEquiv K p) (Pic0.mk D) +
    p • residueCoefficientPicard N K (frobeniusEquiv K p).symm (Pic0.mk D) = _
  rw [residueCoefficientPicard_mk, residueCoefficientPicard_mk, ← map_nsmul, ← map_add]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact (residueFrobeniusDivisorOperator_eq N K p D.val).symm

theorem residueFrobeniusPicardOperator_coefficient (x : Pic0 K FF) :
    residueFrobeniusPicardOperator N K p
        (residueCoefficientPicard N K (frobeniusEquiv K p) x) =
      residueCoefficientPicard N K (frobeniusEquiv K p)
        (residueCoefficientPicard N K (frobeniusEquiv K p) x) + p • x := by
  change _ + p • residueCoefficientPicard N K (frobeniusEquiv K p).symm
    (residueCoefficientPicard N K (frobeniusEquiv K p) x) = _
  rw [residueCoefficientPicard_inverse]

end
end Dubon2026.SourceFunctionField
