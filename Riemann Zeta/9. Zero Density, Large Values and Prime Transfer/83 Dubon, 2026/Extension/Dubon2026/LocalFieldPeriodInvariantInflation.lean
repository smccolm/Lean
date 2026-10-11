import Dubon2026.LocalFieldPeriodRationalInvariant
import Dubon2026.GaloisUnitPeriodTower
import Dubon2026.LocalFieldArithmeticFrobeniusRestriction
import Mathlib.Tactic.FieldSimp

/-! # Original unramified rational cocycle-period invariants commute with actual inflation -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K L M : Type) [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra L M] [Algebra K M] [IsScalarTower K L M]
  [IsGalois K L] [IsGalois K M]
  [ValuativeRel K] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[M]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K M)]

attribute [local instance] IsCyclic.commGroup

/-- Actual arithmetic Frobenius restriction, original cocycle period
repetition and the genuine field degree tower law prove exact compatibility
of the original rational period invariant with original continuous H2 inflation. -/
theorem localFieldPeriodRationalInvariant_inflation
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : FiniteDimensional K M := localField_field_module_finite
    localFieldPeriodRationalInvariant K M (finiteGaloisUnitTowerH2Inflation K L M x) =
      localFieldPeriodRationalInvariant K L x := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : FiniteDimensional K M := localField_field_module_finite
  haveI : FiniteDimensional L M := localField_field_module_finite
  haveI : IsCyclic Gal(L/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
  haveI : IsCyclic Gal(M/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K M).isCyclic.mpr inferInstance
  induction x using Submodule.Quotient.induction_on with
  | _ c =>
    rw [finiteGaloisUnitTowerH2Inflation_mk, localFieldPeriodRationalInvariant_mk,
      localFieldPeriodRationalInvariant_mk,
      galoisUnitCyclicPeriodBase_tower K L M
        (localFieldArithmeticFrobenius K L) (localFieldArithmeticFrobenius_generates K L)
        (localFieldArithmeticFrobenius K M) (localFieldArithmeticFrobenius_generates K M)
        (localFieldArithmeticFrobenius_restrict K L M)]
    have hn : (Module.finrank K L : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    have hk : (Module.finrank L M : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    rw [map_nsmul, nsmul_eq_mul]
    congr 1
    rw [Int.cast_mul, Int.cast_natCast, ← Module.finrank_mul_finrank K L M, Nat.cast_mul]
    field_simp

end
end Dubon2026
