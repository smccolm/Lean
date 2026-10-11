import Dubon2026.LocalFieldArithmeticFrobenius
import Dubon2026.UnramifiedLocalFieldArithmeticH2

/-! # Original continuous unramified H2 normalized by actual arithmetic Frobenius -/

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

/-- The original continuous cyclic class map formed with the actual
arithmetic Frobenius. Finite-dimensionality and cyclicity are derived. -/
def localFieldArithmeticH2Class : Additive Kˣ →ₗ[ℤ]
    GaloisUnitContinuousH2 (K := K) (Ω := L) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : IsCyclic Gal(L/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
  exact continuousCyclicGaloisUnitH2Class (localFieldArithmeticFrobenius K L)
    (localFieldArithmeticFrobenius_generates K L)

/-- The genuine continuous H2 equivalence uses actual normalized order
and the original arithmetic Frobenius, with all finite and cyclic structures derived. -/
def localFieldArithmeticH2Equiv :
    GaloisUnitContinuousH2 (K := K) (Ω := L) ≃ₗ[ℤ] ZMod (Module.finrank K L) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : IsCyclic Gal(L/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
  exact unramifiedLocalFieldArithmeticH2Equiv (localFieldArithmeticFrobenius K L)
    (localFieldArithmeticFrobenius_generates K L)

/-- The original base-unit class defined using actual arithmetic Frobenius
has exactly its original normalized order modulo the actual extension degree. -/
theorem localFieldArithmeticH2Equiv_class (u : Additive Kˣ) :
    localFieldArithmeticH2Equiv K L (localFieldArithmeticH2Class K L u) =
      (localFieldUnitOrder K u : ZMod (Module.finrank K L)) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  haveI : IsCyclic Gal(L/K) :=
    (unramifiedLocalFieldResidueGaloisEquiv K L).isCyclic.mpr inferInstance
  exact unramifiedLocalFieldArithmeticH2Equiv_class (localFieldArithmeticFrobenius K L)
    (localFieldArithmeticFrobenius_generates K L) u

end
end Dubon2026
