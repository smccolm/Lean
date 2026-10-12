import Dubon2026.GaloisUnitCharacterCarryPeriod
import Dubon2026.LocalFieldPeriodRationalInvariant

/-! # The original unramified invariant on every actual character carry cocycle -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup

/-- The actual character value at original arithmetic Frobenius determines
the original rational invariant of its literal base-unit carry cocycle. -/
theorem localFieldPeriodRationalInvariant_characterCarry
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : FiniteDimensional K L := localField_field_module_finite
    localFieldPeriodRationalInvariant K L
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) =
        ↑(((localFieldUnitOrder K (Additive.ofMul u) : ℤ) : ℚ) *
          ((χ (localFieldArithmeticFrobenius K L)).toAdd.val : ℚ) / n) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : IsCyclic Gal(L/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
  let g := localFieldArithmeticFrobenius K L
  have hg := localFieldArithmeticFrobenius_generates K L
  have hz := congrArg (localFieldUnitOrder K)
    (galoisUnitCharacterCarryCocycle_period_mul χ u g hg)
  rw [map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_mul,
    orderOf_eq_card_of_forall_mem_zpowers hg, IsGalois.card_aut_eq_finrank] at hz
  have hq : (n : ℚ) * (localFieldUnitOrder K
      (galoisUnitCyclicPeriodBase g hg (galoisUnitCharacterCarryCocycle χ u)) : ℚ) =
        (Module.finrank K L : ℚ) * ((χ g).toAdd.val : ℚ) *
          (localFieldUnitOrder K (Additive.ofMul u) : ℚ) := by
    exact_mod_cast hz
  rw [localFieldPeriodRationalInvariant_mk]
  congr 1
  apply (div_eq_div_iff (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')
    (Nat.cast_ne_zero.mpr (NeZero.ne n))).mpr
  nlinarith [hq]

/-- The same invariant is integer multiplication of the genuine finite
cyclic invariant by the original base unit's normalized order. -/
theorem localFieldPeriodRationalInvariant_characterCarry_smul
    {n : ℕ} [NeZero n] (χ : Gal(L/K) →* Multiplicative (ZMod n)) (u : Kˣ) :
    letI : FiniteDimensional K L := localField_field_module_finite
    localFieldPeriodRationalInvariant K L
      (Submodule.Quotient.mk (galoisUnitCharacterCarryCocycle χ u)) =
        localFieldUnitOrder K (Additive.ofMul u) •
          rationalCyclicInvariant n (χ (localFieldArithmeticFrobenius K L)).toAdd := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  rw [localFieldPeriodRationalInvariant_characterCarry, rationalCyclicInvariant_apply,
    ← AddCircle.coe_zsmul, zsmul_eq_mul, mul_div_assoc]

end
end Dubon2026
