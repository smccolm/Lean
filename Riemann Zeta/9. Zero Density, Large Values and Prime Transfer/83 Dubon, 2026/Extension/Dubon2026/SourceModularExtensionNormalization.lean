import Dubon2026.SourceReductionAlgebraicNormalization
import Dubon2026.SourceModularReductionDimension

/-! DUB-17/18 -> Picard torsion injectivity -> original Kummer-power
lifting -> extending regular reductions. Every valuation extending the
actual arithmetic modular Gauss valuation admits normalization by an
actual algebraic constant, for every nonzero algebraic extension element.
Only the extension relation for the chosen valuation remains; the original
regular prolongation and its normalization are the proved modular objects. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar

theorem modular_extension_valuation_normalization
    (hNk : (N : IsLocalRing.ResidueField A) ≠ 0)
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [Algebra.IsAlgebraic FF E] (V : ValuationSubring E)
    (hV : V.comap (algebraMap FF E) = gaussRing A N) {x : E} (hx : x ≠ 0) :
    ∃ c : Qbar, V.valuation (c • x) = 1 := by
  have hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  exact (modularRegularProlongation A N hNQ hNk).exists_smul_valuation_eq_one_of_isIntegral
    V hV hx (Algebra.IsAlgebraic.isAlgebraic x).isIntegral

end
end Dubon2026.SourceFunctionField.GaussReduction
