import Dubon2026.SourceOriginalCoefficientWeilNondegeneracy
import Dubon2026.SourceOriginalRationalWeilLaws
import Dubon2026.SourceBilinearBaseChangeAlternating

/-! DUB-17/18 -> primitive determinant -> the coefficient-field original
Weil pairing. Alternation, good-prime adjointness and the actual cyclotomic
multiplier are transported through its literal second scalar extension. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open OriginalChart
open scoped TensorProduct
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
variable (E : Type*) [Field E] [Algebra ℚ_[p] E]
local notation "VE" => E ⊗[ℚ_[p]] originalRationalTateModule N p

theorem originalCoefficientWeilBilinear_self (x : VE) :
    originalCoefficientWeilBilinear N p E x x = 0 :=
  sourceBilinear_baseChange_alternating (originalRationalWeilBilinear N p)
    (originalRationalWeilBilinear_self N p) x

theorem originalCoefficientWeilBilinear_hecke (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (x y : VE) :
    originalCoefficientWeilBilinear N p E
      (((TateModule.tateMap p (originalHeckePicard Qbar N ℓ)).baseChange ℚ_[p]).baseChange E x) y =
    originalCoefficientWeilBilinear N p E x
      (((TateModule.tateMap p (originalHeckePicard Qbar N ℓ)).baseChange ℚ_[p]).baseChange E y) :=
  sourceBilinear_baseChange_adjoint (originalRationalWeilBilinear N p) _
    (originalRationalWeilBilinear_hecke N p ℓ hℓN) x y

theorem originalCoefficientWeilBilinear_cyclotomic (σ : Qbar ≃ₐ[ℚ] Qbar)
    (x y : VE) :
    originalCoefficientWeilBilinear N p E
      ((originalRationalTateGaloisRep N p σ).baseChange E x)
      ((originalRationalTateGaloisRep N p σ).baseChange E y) =
      algebraMap ℚ_[p] E
        (algebraMap ℤ_[p] ℚ_[p] (cyclotomicCharacter Qbar p σ.toRingEquiv : ℤ_[p])) •
        originalCoefficientWeilBilinear N p E x y :=
  sourceBilinear_baseChange_multiplier (originalRationalWeilBilinear N p)
    (originalRationalTateGaloisRep N p σ) _
    (originalRationalWeilBilinear_cyclotomic N p σ) x y

end
end Dubon2026.SourceFunctionField
