import Dubon2026.SourceCurveReductionPrimeKernel
import Dubon2026.SourceModularTamePowerLifting
import Dubon2026.SourceModularTameKummerPower

/-! DUB-17/18 -> actual prime-to-characteristic Picard torsion reduction.
The prime-order kernel is trivial for the genuine tame modular reduction.
Kummer data, original-field root lifting and the principal divisor witness
are all derived from the actual maps. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem modular_pic0_eq_zero_of_prime_torsion_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0)
    (R : ConstantReduction A FF Fb)
    (hR : R.toRegularProlongation =
      modularRegularProlongation A N (Nat.cast_ne_zero.mpr (NeZero.ne N)) hNk)
    {q : ℕ} [hqp : Fact q.Prime] (hq : (q : kk) ≠ 0)
    (z : Pic0 Qbar FF) (hqz : q • z = 0) (hz : R.pic0Map z = 0) : z = 0 := by
  apply R.pic0_eq_zero_of_power_lifting (coeff_lSpace_zero_eq_range N kk) q hqp.out.pos
    _ z hqz hz
  change ∀ f : R.toRegularProlongation.integers,
    (∀ P : Place Qbar FF, (q : ℤ) ∣ P.ord (f : FF)) →
      ∀ {w : Fb}, w ≠ 0 → w ^ q = R.toRegularProlongation.residue f →
        ∃ g : FF, g ^ q = (f : FF)
  rw [hR]
  exact fun f hdvd _ hw0 hw =>
    modular_exists_power_of_residue_power_of_five_le A N p hp hNk hq f hdvd hw0 hw

end
end Dubon2026.SourceFunctionField.GaussReduction
