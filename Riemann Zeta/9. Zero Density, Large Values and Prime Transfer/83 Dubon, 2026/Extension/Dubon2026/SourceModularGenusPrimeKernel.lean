import Dubon2026.SourceCurveReductionPrimeKernel
import Dubon2026.SourceModularKummerPowerLifting
import Dubon2026.SourceCurveReductionPicardR2
import Dubon2026.SourceModularCoefficientGlobalSpaces

/-! DUB-17/18 -> modular good reduction and invertible Picard torsion.
The actual modular prime-order Picard kernel is trivial under genus equality. Existing original-field Kummer power lifting derives the required roots.
The actual characteristic-three consumer discharges genus equality;
characteristic two and the later arithmetic chain remain required. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem modular_pic0_eq_zero_of_prime_torsion_of_genus_eq
    (hNk : (N : kk) ≠ 0) (hgen : genusFF kk Fb = genusFF Qbar FF)
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
    modular_exists_power_of_residue_power_of_genus_eq A N hNk hq hgen f hdvd hw0 hw

end
end Dubon2026.SourceFunctionField.GaussReduction
