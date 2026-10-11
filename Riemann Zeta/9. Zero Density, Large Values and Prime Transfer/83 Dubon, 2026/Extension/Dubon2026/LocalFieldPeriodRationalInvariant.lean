import Dubon2026.LocalFieldPeriodH2Equiv
import Dubon2026.RationalCyclicInvariant

/-! # The genuine rational invariant defined by original arithmetic-Frobenius cocycle periods -/

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

/-- The actual original cocycle period, normalized in the rational circle.
Compatibility under inflation is a separate theorem. -/
def localFieldPeriodRationalInvariant :
    GaloisUnitContinuousH2 (K := K) (Ω := L) →ₗ[ℤ] AddCircle (1 : ℚ) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  exact (rationalCyclicInvariant (Module.finrank K L)).toIntLinearMap.comp
    (localFieldPeriodH2Equiv K L).toLinearMap

/-- The rational invariant is the exact original period order divided by
the actual extension degree, with the selected arithmetic Frobenius. -/
theorem localFieldPeriodRationalInvariant_mk
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K L)) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI : IsCyclic Gal(L/K) :=
      (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
    localFieldPeriodRationalInvariant K L (Submodule.Quotient.mk c) =
      ↑((localFieldUnitOrder K (galoisUnitCyclicPeriodBase
        (localFieldArithmeticFrobenius K L) (localFieldArithmeticFrobenius_generates K L) c) : ℚ) /
          Module.finrank K L) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  haveI : IsCyclic Gal(L/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
  change rationalCyclicInvariant (Module.finrank K L)
    (localFieldPeriodH2Equiv K L (Submodule.Quotient.mk c)) = _
  rw [localFieldPeriodH2Equiv_mk, rationalCyclicInvariant_intCast]

/-- The original unramified-stage period invariant is injective. -/
theorem localFieldPeriodRationalInvariant_injective :
    Function.Injective (localFieldPeriodRationalInvariant K L) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  exact (rationalCyclicInvariant_injective (Module.finrank K L)).comp
    (localFieldPeriodH2Equiv K L).injective

/-- Its actual range consists exactly of the rational classes killed by
the genuine original extension degree. -/
theorem localFieldPeriodRationalInvariant_mem_range_iff (x : AddCircle (1 : ℚ)) :
    x ∈ (localFieldPeriodRationalInvariant K L).range ↔ Module.finrank K L • x = 0 := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  rw [← rationalCyclicInvariant_mem_range_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨localFieldPeriodH2Equiv K L y, rfl⟩
  · rintro ⟨j, hj⟩
    obtain ⟨y, rfl⟩ := (localFieldPeriodH2Equiv K L).surjective j
    exact ⟨y, hj⟩

end
end Dubon2026
