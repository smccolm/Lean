import Dubon2026.LocalFieldArithmeticH2Normalization
import Dubon2026.RationalCyclicInvariant

/-! # The genuine rational invariant of original unramified local Galois H2 -/

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

/-- Original continuous H2 mapped into the actual rational circle using the
proved arithmetic Frobenius and normalized valuation. This is a finite
unramified-stage invariant; no general local invariant or tower identity is assumed. -/
def unramifiedLocalRationalH2Invariant :
    GaloisUnitContinuousH2 (K := K) (Ω := L) →ₗ[ℤ] AddCircle (1 : ℚ) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  exact (rationalCyclicInvariant (Module.finrank K L)).toIntLinearMap.comp
    (localFieldArithmeticH2Equiv K L).toLinearMap

/-- The actual base-unit class has invariant its normalized order divided
by the original extension degree, with arithmetic Frobenius fixing the sign. -/
theorem unramifiedLocalRationalH2Invariant_class (u : Additive Kˣ) :
    unramifiedLocalRationalH2Invariant K L (localFieldArithmeticH2Class K L u) =
      ↑((localFieldUnitOrder K u : ℚ) / Module.finrank K L) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  change rationalCyclicInvariant (Module.finrank K L)
    (localFieldArithmeticH2Equiv K L (localFieldArithmeticH2Class K L u)) = _
  rw [localFieldArithmeticH2Equiv_class, rationalCyclicInvariant_intCast]

/-- The actual unramified-stage rational invariant is injective. -/
theorem unramifiedLocalRationalH2Invariant_injective :
    Function.Injective (unramifiedLocalRationalH2Invariant K L) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  exact (rationalCyclicInvariant_injective (Module.finrank K L)).comp
    (localFieldArithmeticH2Equiv K L).injective

/-- Its actual image is precisely the rational classes killed by the original degree. -/
theorem unramifiedLocalRationalH2Invariant_mem_range_iff (x : AddCircle (1 : ℚ)) :
    x ∈ (unramifiedLocalRationalH2Invariant K L).range ↔ Module.finrank K L • x = 0 := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : NeZero (Module.finrank K L) := ⟨Module.finrank_pos.ne'⟩
  rw [← rationalCyclicInvariant_mem_range_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨localFieldArithmeticH2Equiv K L y, rfl⟩
  · rintro ⟨j, hj⟩
    obtain ⟨y, rfl⟩ := (localFieldArithmeticH2Equiv K L).surjective j
    exact ⟨y, hj⟩

end
end Dubon2026
