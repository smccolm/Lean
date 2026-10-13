import Dubon2026.LocalFieldIntegerUnitPowerIndex
import Dubon2026.LocalFieldUniformizerProduct
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Original local power index from roots and the scalar ideal quotient

This assembles the proved small-unit calculation with the original
uniformizer direction. It reduces DUB-17's finite-place numerical factor to
the cardinality of the original integer ring modulo the exponent.
-/

namespace Dubon2026
noncomputable section
open scoped ValuativeRel

variable (K : Type) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

omit [IsUniformAddGroup K] in
/-- The actual field and integer-unit power kernels have the same order:
the original free integer valuation direction has no nonzero power torsion. -/
theorem localField_unitPower_kernel_card (n : ℕ) (hn : n ≠ 0) :
    Nat.card (powMonoidHom n : Kˣ →* Kˣ).ker =
      Nat.card (powMonoidHom n : 𝒪[K]ˣ →* 𝒪[K]ˣ).ker := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  let e := localFieldUniformizerProductEquiv K π hπ
  exact Nat.card_congr ((nsmulKernelEquiv e.symm n).trans
    (nsmulKernelFreeProdEquiv ℤ (Additive 𝒪[K]ˣ) n hn)).toEquiv

/-- The exact actual local field-unit power index has its uniformizer,
root-kernel and scalar-ideal factors, all on the original field. -/
theorem localField_unitPower_index_scalar (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (Nat.card (powMonoidHom n : Kˣ →* Kˣ).ker *
        Nat.card (𝒪[K] ⧸ (Ideal.span {(n : 𝒪[K])} : Ideal 𝒪[K]))) := by
  have hn0 : n ≠ 0 := by intro h; exact hn (h ▸ Nat.cast_zero)
  rw [localField_unitPower_index_uniformizer_factor K n,
    localField_integerUnit_power_index K n hn, localField_unitPower_kernel_card K n hn0]

/-- A primitive root supplies the exact root factor in the original local
power-index formula, leaving only the actual integral scalar quotient. -/
theorem localField_unitPower_index_scalar_of_primitiveRoot
    (n : ℕ) (hn : (n : K) ≠ 0) (ζ : K) (hζ : IsPrimitiveRoot ζ n) :
    Nat.card (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      n * (n * Nat.card (𝒪[K] ⧸ (Ideal.span {(n : 𝒪[K])} : Ideal 𝒪[K]))) := by
  rw [localField_unitPower_index_scalar K n hn]
  have hn0 : n ≠ 0 := by intro h; exact hn (h ▸ Nat.cast_zero)
  haveI : NeZero n := ⟨hn0⟩
  have hk : (powMonoidHom n : Kˣ →* Kˣ).ker = rootsOfUnity n K := by ext u; rfl
  rw [hk, Nat.card_eq_fintype_card, hζ.card_rootsOfUnity]

end
end Dubon2026
