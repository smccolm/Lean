import Dubon2026.SourceModularTameConstantReductionR2
import Dubon2026.SourceCurveReductionPicardR2

/-! DUB-17/18 -> original Frobenius/inertia -> actual Picard/torsion reduction.
The actual tame modular constant reduction supplies the degree-zero divisor-
class homomorphism, with its literal divisor formula and preservation of
every n-torsion subgroup. No Picard homomorphism is assumed. Torsion
injectivity and compatibility with original arithmetic actions remain
separate necessary obligations. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_picard_reduction_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧ genusFF kk Fb = genusFF Qbar FF ∧
      (∀ D : Divisor.degZero (K := Qbar) (F := FF),
        R.pic0Map (Pic0.mk D) = Pic0.mk (R.degZeroMap D)) ∧
      (∀ (n : ℕ) (z : Pic0 Qbar FF), z ∈ Pic0.torsion n → R.pic0Map z ∈ Pic0.torsion n) := by
  dsimp only
  obtain ⟨R, hR, hg⟩ := exists_modular_constant_reduction_of_five_le A N p hp hNk
  exact ⟨R, hR, hg, R.pic0Map_mk, fun _ _ hz => R.pic0Map_mem_torsion hz⟩

end
end Dubon2026.SourceFunctionField.GaussReduction
