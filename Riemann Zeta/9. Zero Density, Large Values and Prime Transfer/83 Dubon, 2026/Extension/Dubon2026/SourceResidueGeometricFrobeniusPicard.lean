import Dubon2026.SourceResidueGeometricFrobeniusDivisors
import Dubon2026.SourceResidueCoefficientPicard

/-! DUB-17/18 -> original Frobenius quadratic relation -> geometric
Frobenius on the actual residue Picard quotient. The literal geometric
divisor pushforward descends by its proved degree and principal-divisor
identities and agrees with coefficient Frobenius on every Picard class. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open SourceCurve
variable (N : ℕ) [NeZero N] (K : Type*) [Field K] [IsAlgClosed K]
  (p : ℕ) [Fact p.Prime] [CharP K p]
local notation "FF" => modularFunctionFieldCoeff N K

/-- The geometric divisor pushforward restricted to actual degree-zero divisors. -/
def residueGeometricFrobeniusDegZero :
    Divisor.degZero (K := K) (F := FF) →+ Divisor.degZero (K := K) (F := FF) where
  toFun D := ⟨residueGeometricFrobeniusDivisor N K p D.val, by
    change Divisor.degree (residueGeometricFrobeniusDivisor N K p D.val) = 0
    rw [residueGeometricFrobeniusDivisor_degree]
    exact D.property⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' D E := Subtype.ext (map_add _ D.val E.val)

/-- The literal geometric Frobenius pushforward on degree-zero divisor classes. -/
def residueGeometricFrobeniusPicard : Pic0 K FF →+ Pic0 K FF :=
  QuotientAddGroup.map _ _ (residueGeometricFrobeniusDegZero N K p) (by
    intro D hD
    exact residueGeometricFrobeniusDivisor_principal N K p D.val hD)

theorem residueGeometricFrobeniusPicard_mk (D : Divisor.degZero (K := K) (F := FF)) :
    residueGeometricFrobeniusPicard N K p (Pic0.mk D) =
      Pic0.mk (residueGeometricFrobeniusDegZero N K p D) := rfl

theorem residueGeometricFrobeniusPicard_eq_coefficient (x : Pic0 K FF) :
    residueGeometricFrobeniusPicard N K p x =
      residueCoefficientPicard N K (frobeniusEquiv K p) x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [residueGeometricFrobeniusPicard_mk, residueCoefficientPicard_mk]
  apply congrArg Pic0.mk
  apply Subtype.ext
  exact residueGeometricFrobeniusDivisor_eq_coefficient N K p D.val

end
end Dubon2026.SourceFunctionField
