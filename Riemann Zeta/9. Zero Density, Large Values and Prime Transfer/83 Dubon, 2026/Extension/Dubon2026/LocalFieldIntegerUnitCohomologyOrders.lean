import Dubon2026.LocalFieldCyclicSmallUnitAcyclicity
import Dubon2026.StableSubgroupQuotientCohomology
import Dubon2026.FiniteCyclicCohomologyCardinality

/-! # Finite equal cohomology orders of the original local integer units -/

namespace Dubon2026
noncomputable section

open CategoryTheory
open scoped ValuativeRel

attribute [local instance] IsCyclic.commGroup

/-- The actual first and second cohomology of original integer units in a
finite cyclic local extension are finite and have equal orders. An original
open acyclic subgroup is constructed, its finite quotient computes both
groups, and the periodic resolution proves equality of the two finite orders. -/
theorem localField_integer_unit_first_second_cohomology_orders
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]
    (π : 𝒪[K]) (hπ : Irreducible π) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
    Finite (groupCohomology A 1) ∧ Finite (groupCohomology A 2) ∧
      Nat.card (groupCohomology A 1) = Nat.card (groupCohomology A 2) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  letI := localFieldIntegerUnitMulDistribMulAction K L
  let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
  obtain ⟨V, _, hfinite, hstable, hacyclic⟩ :=
    localField_exists_cyclic_small_unit_acyclic K L π hπ
  let Q := stableSubgroupQuotientRep Gal(L/K) 𝒪[L]ˣ V hstable
  haveI : Finite (𝒪[L]ˣ ⧸ V) := hfinite
  haveI : Finite Q := stableSubgroupQuotientRep_finite Gal(L/K) 𝒪[L]ˣ V hstable
  have e : ∀ n : ℕ, 0 < n → (groupCohomology A n ≅ groupCohomology Q n) := by
    intro n hn
    have hi : IsIso ((groupCohomology.functor ℤ Gal(L/K) n).map
        (stableSubgroupShortComplex Gal(L/K) 𝒪[L]ˣ V hstable).g) :=
      stableSubgroupQuotient_cohomology_isIso Gal(L/K) 𝒪[L]ˣ V hstable n
        (hacyclic n hn) (hacyclic (n + 1) (Nat.zero_lt_succ n))
    exact @asIso _ _ _ _ ((groupCohomology.functor ℤ Gal(L/K) n).map
      (stableSubgroupShortComplex Gal(L/K) 𝒪[L]ˣ V hstable).g) hi
  haveI : Finite (groupCohomology Q 1) := finite_groupCohomology_of_finite_coefficients Q 1
  haveI : Finite (groupCohomology Q 2) := finite_groupCohomology_of_finite_coefficients Q 2
  refine ⟨Finite.of_equiv _ (e 1 (by decide)).symm.toLinearEquiv.toEquiv,
    Finite.of_equiv _ (e 2 (by decide)).symm.toLinearEquiv.toEquiv, ?_⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  calc
    Nat.card (groupCohomology A 1) = Nat.card (groupCohomology Q 1) :=
      Nat.card_congr (e 1 (by decide)).toLinearEquiv.toEquiv
    _ = Nat.card (groupCohomology Q 2) :=
      finite_cyclic_first_second_cohomology_card_eq Q g hg
    _ = Nat.card (groupCohomology A 2) :=
      Nat.card_congr (e 2 (by decide)).symm.toLinearEquiv.toEquiv

end
end Dubon2026
