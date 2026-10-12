import Dubon2026.LocalFieldCarryInvariantBaseChange
import Dubon2026.LocalFieldH2CarryRepresentatives

/-! # Restriction of every original unramified local H2 invariant -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable (K E L M : Type) [Field K] [Field E] [Field L] [Field M]
  [Algebra K E] [Algebra K L] [Algebra K M] [Algebra E M] [Algebra L M]
  [IsScalarTower K E M] [IsScalarTower K L M] [IsGalois K L] [IsGalois E M]
  [ValuativeRel K] [ValuativeRel E] [ValuativeRel L] [ValuativeRel M]
  [TopologicalSpace K] [TopologicalSpace E] [TopologicalSpace L] [TopologicalSpace M]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField E]
  [IsNonarchimedeanLocalField L] [IsNonarchimedeanLocalField M]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation E)]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [(ValuativeRel.valuation E).HasExtension (ValuativeRel.valuation M)]
  [(ValuativeRel.valuation L).HasExtension (ValuativeRel.valuation M)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]
  [Algebra.FormallyUnramified 𝒪[E] 𝒪[M]]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits E M)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits E M)]

attribute [local instance] IsCyclic.commGroup

/-- For every original unramified H2 class, genuine base change multiplies
the original rational invariant by the actual extension degree of the base.
No unramified hypothesis on E over K is imposed. -/
theorem localFieldPeriodRationalInvariant_baseChange
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional E M := localField_field_module_finite
    localFieldPeriodRationalInvariant E M (finiteGaloisUnitBaseChangeH2 K E L M x) =
      Module.finrank K E • localFieldPeriodRationalInvariant K L x := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : FiniteDimensional E M := localField_field_module_finite
  haveI : NeZero (Nat.card Gal(L/K)) := ⟨Nat.card_pos.ne'⟩
  haveI : IsCyclic Gal(L/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
  obtain ⟨u, rfl⟩ := localFieldH2_exists_carry_representative K L x
  exact localFieldPeriodRationalInvariant_baseChange_characterCarry K E L M
    (galoisUnitGeneratorIndex (localFieldArithmeticFrobenius K L)
      (localFieldArithmeticFrobenius_generates K L)) u

/-- The original base-change class vanishes exactly when multiplication
by the actual base-field degree kills its original rational invariant. -/
theorem finiteGaloisUnitBaseChangeH2_eq_zero_iff
    (x : GaloisUnitContinuousH2 (K := K) (Ω := L)) :
    letI : FiniteDimensional E M := localField_field_module_finite
    finiteGaloisUnitBaseChangeH2 K E L M x = 0 ↔
      Module.finrank K E • localFieldPeriodRationalInvariant K L x = 0 := by
  haveI : FiniteDimensional E M := localField_field_module_finite
  constructor
  · intro hx
    rw [← localFieldPeriodRationalInvariant_baseChange K E L M x, hx, map_zero]
  · intro hx
    apply localFieldPeriodRationalInvariant_injective E M
    rw [map_zero, localFieldPeriodRationalInvariant_baseChange, hx]

end
end Dubon2026
