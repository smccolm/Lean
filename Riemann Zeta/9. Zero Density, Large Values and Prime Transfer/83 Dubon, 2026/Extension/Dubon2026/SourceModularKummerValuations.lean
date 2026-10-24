import Dubon2026.SourceKummerExtendingValuations
import Dubon2026.SourceModularReductionDimension

/-! DUB-17/18 -> Picard torsion injectivity -> original-field power
lifting. A nontrivial prime Kummer cover whose defining Gauss-integral
function reduces to a nonzero prime power has q distinct valuations
extending the actual modular Gauss valuation. Each admits normalization
by actual algebraic constants. Residue-field identification and the genus
comparison for the resulting regular reductions are still required. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open Polynomial IsLocalRing
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "kk" => ResidueField A
local notation "Fb" => modularFunctionFieldCoeff N kk

theorem modular_kummer_extending_valuations
    (hNk : (N : kk) ≠ 0) {q : ℕ} [Fact q.Prime] (hq : (q : kk) ≠ 0)
    (f : gaussRing A N) (hf : ∀ g : FF, g ^ q ≠ (f : FF))
    {w : Fb} (hw0 : w ≠ 0)
    (hw : w ^ q = modularResidueHom A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk f)
    (E : Type*) [Field E] [Algebra FF E] [Algebra Qbar E] [IsScalarTower Qbar FF E]
    [IsSplittingField FF E (X ^ q - C (f : FF))] :
    ∃ V : Fin q → ValuationSubring E, Function.Injective V ∧
      ∀ i, (V i).comap (algebraMap FF E) = gaussRing A N ∧
        ∀ x : E, x ≠ 0 → ∃ c : Qbar, (V i).valuation (c • x) = 1 := by
  exact SourceCurve.RegularProlongation.exists_kummer_extending_valuations
    (modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk) f hf hq hw0 hw E

end
end Dubon2026.SourceFunctionField.GaussReduction
