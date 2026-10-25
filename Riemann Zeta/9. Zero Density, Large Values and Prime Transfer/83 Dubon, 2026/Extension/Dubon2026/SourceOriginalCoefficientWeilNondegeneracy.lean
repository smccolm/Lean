import Dubon2026.SourceFiniteBilinearBaseChange
import Dubon2026.SourceOriginalRationalWeilNondegeneracy
import Dubon2026.SourceOriginalContinuousRankTwoGalois

/-! DUB-17/18 -> primitive determinant -> the original pairing over the
common coefficient field. The actual rational Tate source is finite;
native Hom base change preserves its pairing's injectivity with the
literal root-valued tensor target. No perfect-pairing premise is supplied. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open OriginalChart
open scoped TensorProduct
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]
variable (E : Type*) [Field E] [Algebra ℚ_[p] E]

/-- The original Weil pairing after rational and coefficient-field scalar extension. -/
def originalCoefficientWeilBilinear :
    (E ⊗[ℚ_[p]] originalRationalTateModule N p) →ₗ[E]
    (E ⊗[ℚ_[p]] originalRationalTateModule N p) →ₗ[E]
    E ⊗[ℚ_[p]] (ℚ_[p] ⊗[ℤ_[p]] TateModule p (Additive Qbarˣ)) :=
  LinearMap.BilinMap.baseChange E (originalRationalWeilBilinear N p)

theorem originalCoefficientWeilBilinear_injective :
    Function.Injective (originalCoefficientWeilBilinear N p E) := by
  letI := originalRationalTate_finite N p
  exact finite_bilinear_baseChange_injective (originalRationalWeilBilinear N p)
    (originalRationalWeilBilinear_injective N p)

end
end Dubon2026.SourceFunctionField
