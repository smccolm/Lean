import Dubon2026.SourceModularTamePicardReductionR2
import Dubon2026.SourceCurveReductionKummerPower
import Dubon2026.SourceModularCoefficientGlobalSpaces

/-! DUB-17 Theorem 2.6 / DUB-18 Corollary 8.2 -> symmetric-power
continuation -> automorphy/residual association -> original Frobenius and
inertia -> prime-to-characteristic Picard torsion injectivity. The actual
tame modular constant reduction supplies normalized Kummer data for every
torsion element in its kernel. Its reduced function is proved to be an
actual power; lifting that power to the original field remains necessary. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_kummer_power_data_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧
      genusFF kk Fb = genusFF Qbar FF ∧
      ∀ (z : Pic0 Qbar FF) (m : ℕ), 0 < m → m • z = 0 → R.pic0Map z = 0 →
        ∃ D : Divisor.degZero (K := Qbar) (F := FF), Pic0.mk D = z ∧
          ∃ f : R.integers, R.residue f ≠ 0 ∧
            (∀ P, (m : ℤ) * (D : Divisor Qbar FF) P = P.ord (f : FF)) ∧
            ∃ w : Fb, w ≠ 0 ∧ w ^ m = R.residue f := by
  dsimp only
  obtain ⟨R, hR, hg⟩ := exists_modular_constant_reduction_of_five_le A N p hp hNk
  exact ⟨R, hR, hg, fun z m hm hmz hz =>
    R.exists_residue_power_of_torsion_kernel (coeff_lSpace_zero_eq_range N kk) z m hm hmz hz⟩

end
end Dubon2026.SourceFunctionField.GaussReduction
