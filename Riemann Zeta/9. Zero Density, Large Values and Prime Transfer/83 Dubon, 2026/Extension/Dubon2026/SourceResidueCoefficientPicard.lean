import Dubon2026.SourceResidueCoefficientDivisors
import Dubon2026.SourceCurvePicardGroup

/-! DUB-17/18 -> original Frobenius/Picard comparison -> the actual
residue Picard action. The degree and principal-divisor equations proved
for the coefficient permutation give a native quotient map. No Picard
equivariance certificate is assumed. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) (K : Type*) [Field K] [NeZero N] [IsAlgClosed K]
local notation "FF" => modularFunctionFieldCoeff N K

/-- The genuine arithmetic action restricted to residue degree-zero divisors. -/
def residueCoefficientDegZero (e : K ≃+* K) :
    Divisor.degZero (K := K) (F := FF) →+ Divisor.degZero (K := K) (F := FF) where
  toFun D := ⟨residueCoefficientDivisorEquiv N K e D.val, by
    change Divisor.degree (residueCoefficientDivisorEquiv N K e D.val) = 0
    rw [residueCoefficientDivisor_degree]
    exact D.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' D E := Subtype.ext (map_add _ D.val E.val)

/-- Arithmetic transport descends through the actual principal-divisor relation. -/
def residueCoefficientPicard (e : K ≃+* K) : Pic0 K FF →+ Pic0 K FF :=
  QuotientAddGroup.map _ _ (residueCoefficientDegZero N K e) (by
    intro D hD
    exact residueCoefficientDivisor_principal N K e D.val hD)

theorem residueCoefficientPicard_mk (e : K ≃+* K)
    (D : Divisor.degZero (K := K) (F := FF)) :
    residueCoefficientPicard N K e (Pic0.mk D) = Pic0.mk (residueCoefficientDegZero N K e D) := rfl


end
end Dubon2026.SourceFunctionField
