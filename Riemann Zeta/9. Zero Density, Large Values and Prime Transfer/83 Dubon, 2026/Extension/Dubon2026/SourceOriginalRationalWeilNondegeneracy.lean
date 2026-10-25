import Dubon2026.SourceFractionBilinearInjective
import Dubon2026.SourceTateRationalInjection
import Dubon2026.SourceOriginalTateWeilNondegeneracy
import Dubon2026.SourceOriginalRationalTate

/-! DUB-17/18 -> primitive determinant -> required Hecke-component pairing.
The actual integral Weil pairing remains nondegenerate after the precise
rational scalar extension used by the existing original rank-two realization. -/
namespace Dubon2026.SourceFunctionField
noncomputable section
open OriginalChart
open scoped TensorProduct
local notation "Qbar" => AlgebraicClosure ℚ
variable (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime]

/-- The literal scalar extension of the original arithmetic Tate Weil pairing. -/
def originalRationalWeilBilinear : originalRationalTateModule N p →ₗ[ℚ_[p]]
    originalRationalTateModule N p →ₗ[ℚ_[p]]
      ℚ_[p] ⊗[ℤ_[p]] TateModule p (Additive Qbarˣ) :=
  LinearMap.BilinMap.baseChange ℚ_[p] (originalTateWeilBilinear N p)

theorem originalRationalWeilBilinear_injective :
    Function.Injective (originalRationalWeilBilinear N p) :=
  sourceFraction_bilinear_baseChange_injective (originalTateWeilBilinear N p)
    (originalTateWeilBilinear_injective N p)
    (TateModule.rational_one_tmul_injective p (Additive Qbarˣ))

end
end Dubon2026.SourceFunctionField
