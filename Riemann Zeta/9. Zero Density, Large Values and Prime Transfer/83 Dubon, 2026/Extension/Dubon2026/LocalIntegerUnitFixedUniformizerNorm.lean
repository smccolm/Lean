import Dubon2026.LocalIntegerUnitFixedUniformizerVanishing
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic

/-! # Fixed-uniformizer vanishing supplies actual invariant integer-unit norms

The proved original integer-unit H2 vanishing is converted through the
actual cyclic projection into norm preimages. This is precisely the
local-unit containment needed outside the finite ramification support in
DUB-17's prime-degree norm-index upper-bound argument.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped ValuativeRel
attribute [local instance 1100] Rep.hV2
variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [IsCyclic Gal(L/K)]
attribute [local instance] IsCyclic.commGroup

/-- A fixed original uniformizer supplies actual norm preimages for every invariant original integer unit. -/
theorem localIntegerUnit_norm_preimages_of_fixed_uniformizer
    (π : Lˣ) (hfixed : ∀ σ : Gal(L/K), σ • π = π)
    (hπ : localFieldUnitOrder L (Additive.ofMul π) = 1) :
    letI : FiniteDimensional K L := localField_field_module_finite
    letI := localFieldIntegerUnitMulDistribMulAction K L
    let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x := by
  letI : FiniteDimensional K L := localField_field_module_finite
  letI := localFieldIntegerUnitMulDistribMulAction K L
  let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
  have hz := (localIntegerUnit_first_second_zero_of_fixed_uniformizer K L π hfixed hπ).2
  haveI : Subsingleton (groupCohomology A 2) := ModuleCat.isZero_iff_subsingleton.mp hz
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  change ∀ x : A, x ∈ A.ρ.invariants → ∃ y : A, A.norm.hom y = x
  intro x hx
  let y : LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap := ⟨x, by
    change A.ρ g x - x = 0
    exact sub_eq_zero.mpr (hx g)⟩
  exact (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff A g hg 2 (by decide) y).mp
    (Subsingleton.elim _ 0)

end
end Dubon2026
