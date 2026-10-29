import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-! DUB-17/18 -> original Gamma1 genus preservation -> finite elliptic
fibers -> integral toric coordinates. Primitive-root characters supply
finite Fourier orthogonality over both the complex and residue fields.
Adapted from Anthropic FLT, Apache-2.0, commit
6e837e75355538c7f80bab5b956861e86c4eacc2,
S_ModularCurve_exists_gamma1_isIntegralQExp_fourier_and_toricPoint_eq_sum.
Native AddChar orthogonality and primitive-root proofs are reused. -/
namespace Dubon2026.SourceFunctionField.GammaOne.ToricFourier
noncomputable section
variable {F : Type*} [Field F] {M : ℕ} [NeZero M] {z : F} (hz : IsPrimitiveRoot z M)

/-- The additive character determined by the prescribed primitive root. -/
def ψ (hz : IsPrimitiveRoot z M) : AddChar (ZMod M) F := AddChar.zmodChar M hz.pow_eq_one

theorem ψ_apply (a : ZMod M) : ψ hz a = z ^ a.val := rfl

theorem ψ_isPrimitive : (ψ hz).IsPrimitive := AddChar.zmodChar_primitive_of_primitive_root M hz

theorem ψ_eq_one_iff (a : ZMod M) : ψ hz a = 1 ↔ a = 0 :=
  (ψ_isPrimitive hz).zmod_char_eq_one_iff M a

theorem sum_ψ_mul (b : ZMod M) : ∑ a : ZMod M, ψ hz (a * b) = if b = 0 then (M : F) else 0 := by
  classical
  rw [AddChar.sum_mulShift b (ψ_isPrimitive hz)]
  split_ifs <;> simp [ZMod.card]

theorem ψ_pow (a : ZMod M) (j : ℕ) : ψ hz a ^ j = ψ hz ((j : ZMod M) * a) := by
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow]

include hz in
theorem natCast_ne_zero : (M : F) ≠ 0 :=
  haveI : NeZero (M : F) := IsPrimitiveRoot.neZero' hz
  NeZero.ne (M : F)

theorem ψ_ne_zero (a : ZMod M) : ψ hz a ≠ 0 := by
  rw [ψ_apply]
  exact pow_ne_zero _ (hz.ne_zero (NeZero.ne M))

theorem ψ_pow_M (a : ZMod M) : ψ hz a ^ M = 1 := by
  rw [ψ_apply, ← pow_mul, mul_comm, pow_mul, hz.pow_eq_one, one_pow]

theorem ψ_ne_one {a : ZMod M} (ha : a ≠ 0) : ψ hz a ≠ 1 := fun h => ha ((ψ_eq_one_iff hz a).mp h)

theorem one_sub_ψ_ne_zero {a : ZMod M} (ha : a ≠ 0) : 1 - ψ hz a ≠ 0 :=
  sub_ne_zero.mpr (ψ_ne_one hz ha).symm

theorem geom_ψ {a : ZMod M} (ha : a ≠ 0) : ∑ j ∈ Finset.range M, ψ hz a ^ j = 0 := by
  rw [geom_sum_eq (ψ_ne_one hz ha) M, ψ_pow_M, sub_self, zero_div]

theorem ψ_pow_sub_one (a : ZMod M) : ψ hz a ^ (M - 1) = (ψ hz a)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  rw [pow_sub_one_mul (NeZero.ne M), ψ_pow_M]

end
end Dubon2026.SourceFunctionField.GammaOne.ToricFourier
