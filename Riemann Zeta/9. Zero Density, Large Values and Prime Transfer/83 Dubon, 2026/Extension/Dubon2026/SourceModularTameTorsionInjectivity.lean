import Dubon2026.SourceModularTameTorsionKernel

/-! DUB-17/18 -> actual prime-to-characteristic Picard torsion reduction.
An actual tame modular constant reduction is constructed, and its genuine
Picard map is injective on every torsion subgroup of order invertible in
the residue field. Wild genus equality and arithmetic-action comparison
remain required by the full source contract. -/
namespace Dubon2026.SourceFunctionField.GaussReduction
noncomputable section
open SourceCurve
local notation "Qbar" => AlgebraicClosure ℚ
variable (A : ValuationSubring Qbar) (N : ℕ) [NeZero N]
local notation "kk" => IsLocalRing.ResidueField A
local notation "FF" => modularFunctionFieldCoeff N Qbar
local notation "Fb" => modularFunctionFieldCoeff N kk
attribute [local instance] residueModularAlgebra residueConstantsClosed

theorem exists_modular_picard_torsion_injective_of_five_le
    (p : ℕ) [CharP kk p] (hp : 5 ≤ p) (hNk : (N : kk) ≠ 0) :
    let hNQ : (N : Qbar) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
    ∃ R : ConstantReduction A FF Fb,
      R.toRegularProlongation = modularRegularProlongation A N hNQ hNk ∧
      genusFF kk Fb = genusFF Qbar FF ∧
      ∀ m : ℕ, (m : kk) ≠ 0 →
        Set.InjOn R.pic0Map (↑(Pic0.torsion (K := Qbar) (F := FF) m)) := by
  dsimp only
  obtain ⟨R, hR, hg⟩ := exists_modular_constant_reduction_of_five_le A N p hp hNk
  refine ⟨R, hR, hg, fun m hm x hx y hy hxy => ?_⟩
  apply sub_eq_zero.mp
  apply modular_pic0_eq_zero_of_torsion_of_five_le A N p hp hNk R hR m hm (x - y)
  · rw [nsmul_sub, Pic0.mem_torsion_iff.mp hx, Pic0.mem_torsion_iff.mp hy, sub_self]
  · rw [map_sub, hxy, sub_self]

end
end Dubon2026.SourceFunctionField.GaussReduction
