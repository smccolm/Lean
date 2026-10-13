import Dubon2026.UnramifiedIntegerUnitNormPreimages
import Dubon2026.LocalFieldIntegerUnitCohomologyOrders

/-! # Original positive cohomology of unramified local integer units

The proved invariant norm preimages kill actual H2. Existing finite
equal H1/H2 orders then kill actual H1. The original cyclic periodic
resolution kills all positive degrees. These are precisely the
outside-support local factors in DUB-17's supported-idele calculation.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped ValuativeRel
variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [IsCyclic Gal(L/K)]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
  [Algebra.FormallyUnramified 𝒪[K] 𝒪[L]]

/-- The original integer units of a cyclic unramified local extension have zero original cohomology in every positive degree. -/
theorem unramified_integer_unit_positive_cohomology_zero (n : ℕ) (hn : 0 < n) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ) n) := by
  letI : FiniteDimensional K L := localField_field_module_finite
  letI := localFieldIntegerUnitMulDistribMulAction K L
  letI := IsCyclic.commGroup (α := Gal(L/K))
  let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  have hnorm := unramified_integer_unit_norm_preimages K L
  have hz2 := cyclic_evenCohomology_zero_of_norm_preimages A g hg hnorm 2 (by decide)
  letI : Subsingleton (groupCohomology A 2) := ModuleCat.isZero_iff_subsingleton.mp hz2
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have horders := localField_integer_unit_first_second_cohomology_orders K L π hπ
  have hc1 : Nat.card (groupCohomology A 1) = 1 := horders.2.2.trans Nat.card_unique
  letI : Subsingleton (groupCohomology A 1) := (Nat.card_eq_one_iff_unique.mp hc1).1
  have hz1 : Limits.IsZero (groupCohomology A 1) := ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  exact cyclic_positiveCohomology_zero A g hg hnorm hz1 n hn

end
end Dubon2026
