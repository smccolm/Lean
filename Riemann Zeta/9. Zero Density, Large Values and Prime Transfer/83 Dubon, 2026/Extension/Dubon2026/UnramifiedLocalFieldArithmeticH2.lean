import Dubon2026.LocalFieldIntegerAlgebraFinite
import Dubon2026.ContinuousUnramifiedCyclicGaloisH2Order

/-! # Actual unramified local-field norm and cyclic cohomology with derived integer finiteness -/

namespace Dubon2026
noncomputable section

open scoped ValuativeRel

variable {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- The actual unramified field-norm image has the normalized-order criterion,
with original integer-ring finite generation proved internally. -/
theorem unramifiedLocalField_norm_image (u : Kˣ) :
    (∃ v : Lˣ, Units.map (Algebra.norm K (S := L)) v = u) ↔
      (Module.finrank K L : ℤ) ∣ localFieldUnitOrder K (Additive.ofMul u) := by
  haveI : Module.Finite 𝒪[K] 𝒪[L] := localField_integer_module_finite
  exact unramifiedLocalField_mem_normRange_iff_order_dvd u

variable [IsGalois K L] [IsCyclic Gal(L/K)]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K L)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K L)]

attribute [local instance] IsCyclic.commGroup

variable (g : Gal(L/K)) (hg : ∀ x, x ∈ Subgroup.zpowers g)

/-- Actual continuous cyclic Galois H2 is identified by original local order,
deriving finite generation of the actual integer rings from their compactness.
The explicit cyclic generator has not been identified with arithmetic Frobenius. -/
def unramifiedLocalFieldArithmeticH2Equiv :
    GaloisUnitContinuousH2 (K := K) (Ω := L) ≃ₗ[ℤ] ZMod (Module.finrank K L) := by
  haveI : Module.Finite 𝒪[K] 𝒪[L] := localField_integer_module_finite
  exact continuousUnramifiedCyclicGaloisH2OrderEquiv g hg

/-- The original base-unit cohomology class retains exactly its normalized
integer order modulo the extension degree after integer finiteness is derived. -/
theorem unramifiedLocalFieldArithmeticH2Equiv_class (u : Additive Kˣ) :
    unramifiedLocalFieldArithmeticH2Equiv g hg
      (continuousCyclicGaloisUnitH2Class g hg u) =
        (localFieldUnitOrder K u : ZMod (Module.finrank K L)) := by
  haveI : Module.Finite 𝒪[K] 𝒪[L] := localField_integer_module_finite
  exact continuousUnramifiedCyclicGaloisH2OrderEquiv_class g hg u

end
end Dubon2026
