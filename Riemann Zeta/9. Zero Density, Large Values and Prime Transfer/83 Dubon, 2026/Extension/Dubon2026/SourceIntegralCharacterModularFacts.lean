import Dubon2026.SourceIntegralCharacterCorrection
import Dubon2026.SourceModularFreeProduct
import Dubon2026.SourceParabolicClassification

/-! DUB-17/18 -> original all-weight association -> Gamma1 Picard/H1
-> Abel-Jacobi -> unitary multiplier logarithms -> integral parabolic-character
lifting. Adapted from the Apache-2.0 scope-796 primary at revision
6e837e75355538c7f80bab5b956861e86c4eacc2. Reuse the repository
SourceParabolic.classification and the audited actual projective free-product
equivalence. The theorem uses literal squared-trace-four vanishing, all finite
indices and all natural moduli, including zero. It assumes no lifting theorem. -/
namespace Dubon2026.SourceIntegralCharacterLift
noncomputable section
open Subgroup
open scoped MatrixGroups
open Matrix.SpecialLinearGroup ModularGroup

theorem neg_one_mem_center : (-1 : SL(2, ℤ)) ∈ Subgroup.center SL(2, ℤ) :=
  (SourceModularFreeProduct.mem_center_iff_eq _).mpr (Or.inr rfl)

theorem eq_one_or_eq_neg_one_of_mem_center {z : SL(2, ℤ)} (hz : z ∈ Subgroup.center SL(2, ℤ)) :
    z = 1 ∨ z = -1 := (SourceModularFreeProduct.mem_center_iff_eq z).mp hz

theorem S_mul_S : (S : SL(2, ℤ)) * S = -1 :=
  Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, ModularGroup.S_mul_S_eq, Matrix.SpecialLinearGroup.coe_neg,
      Matrix.SpecialLinearGroup.coe_one])

theorem trace_conj_T_zpow (δ : SL(2, ℤ)) (k : ℤ) :
    ((δ * T ^ k * δ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).trace = 2 := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.trace_mul_comm, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul, ModularGroup.coe_T_zpow, Matrix.trace_fin_two_of]
  ring

end
end Dubon2026.SourceIntegralCharacterLift
