import Dubon2026.LocalFieldIntegralSmallUnitCohomology
import Dubon2026.StableSubgroupCohomology
import Dubon2026.CyclicPositiveCohomologyVanishing
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

/-! # Positive cyclic cohomology of actual open local integer units -/

namespace Dubon2026
noncomputable section

open CategoryTheory
open scoped ValuativeRel

attribute [local instance] IsCyclic.commGroup

/-- An actual finite cyclic local extension has a genuine open subgroup of
its original integer units with finite quotient and zero positive cohomology.
The subgroup and all norm and cocycle preimages come from the constructed
normal-lattice filtration of the original extension. -/
theorem localField_exists_cyclic_small_unit_acyclic
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    ∃ V : Subgroup 𝒪[L]ˣ,
      IsOpen (V : Set 𝒪[L]ˣ) ∧ Finite (𝒪[L]ˣ ⧸ V) ∧
      ∃ hstable : ∀ (σ : Gal(L/K)) (v : 𝒪[L]ˣ), v ∈ V → σ • v ∈ V,
        letI := stableSubgroupMulDistribMulAction Gal(L/K) 𝒪[L]ˣ V hstable
        ∀ n : ℕ, 0 < n →
          Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) V) n) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  letI := localFieldIntegerUnitMulDistribMulAction K L
  obtain ⟨V, hopen, hfinite, hstable, hnorm, hcob⟩ :=
    localField_exists_integral_small_unit_norm_and_coboundary K L π hπ
  refine ⟨V, hopen, hfinite, hstable, ?_⟩
  letI := stableSubgroupMulDistribMulAction Gal(L/K) 𝒪[L]ˣ V hstable
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  exact fun n hn => cyclic_positiveCohomology_zero
    (Rep.ofMulDistribMulAction Gal(L/K) V) g hg
    (stableSubgroup_repNorm_preimages Gal(L/K) 𝒪[L]ˣ V hstable hnorm)
    (stableSubgroup_firstCohomology_zero Gal(L/K) 𝒪[L]ˣ V hstable hcob) n hn

end
end Dubon2026
