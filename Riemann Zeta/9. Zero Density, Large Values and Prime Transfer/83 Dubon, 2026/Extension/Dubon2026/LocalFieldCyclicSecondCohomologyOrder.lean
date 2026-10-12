import Dubon2026.LocalFieldUnitValuationSequence
import Dubon2026.LocalFieldIntegerUnitCohomologyOrders
import Dubon2026.CyclicIntegerEvenCohomology
import Dubon2026.ExactCohomologyCardinality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! # The actual cyclic local-field second cohomology has the group order -/

namespace Dubon2026
noncomputable section

open CategoryTheory
open scoped ValuativeRel
attribute [local instance] IsCyclic.commGroup
attribute [local instance 1100] Rep.hV2

/-- For the original multiplicative group of a cyclic local extension,
second cohomology is finite of order equal to the actual Galois group order.
The proof combines the original valuation sequence, Hilbert 90, the finite
equal integer-unit cohomology orders and the actual cyclic integer calculation. -/
theorem localField_cyclic_second_cohomology_order
    (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [IsCyclic Gal(L/K)]
    [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
    [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
    [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)] :
    Finite (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) ∧
      Nat.card (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) = Nat.card Gal(L/K) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  letI := localFieldIntegerUnitMulDistribMulAction K L
  let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
  let B := Rep.ofAlgebraAutOnUnits K L
  let C := Rep.trivial ℤ Gal(L/K) ℤ
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  obtain ⟨hA1, hA2, hA12⟩ := localField_integer_unit_first_second_cohomology_orders K L π hπ
  haveI : Finite (groupCohomology A 1) := hA1
  haveI : Finite (groupCohomology A 2) := hA2
  let eA := Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 3 (by decide) ≪≫
    (Rep.FiniteCyclicGroup.groupCohomologyIsoOdd A g hg 1 (by decide)).symm
  have hA32 : Nat.card (groupCohomology A 3) = Nat.card (groupCohomology A 2) :=
    (Nat.card_congr eA.toLinearEquiv.toEquiv).trans hA12
  have hB1 : Limits.IsZero (groupCohomology B 1) :=
    ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  have hB3 : Limits.IsZero (groupCohomology B 3) :=
    cyclic_oddCohomology_zero_of_first B g hg hB1 3 (by decide)
  have hC1 : Limits.IsZero (groupCohomology C 1) :=
    cyclic_trivial_integer_odd_cohomology_zero Gal(L/K) g hg 1 (by decide)
  obtain ⟨hC2, hCcard⟩ :=
    cyclic_trivial_integer_even_cohomology_order Gal(L/K) g hg 2 (by decide)
  haveI : Finite (groupCohomology C 2) := hC2
  let X := localFieldUnitValuationShortComplex K L
  haveI : Finite (groupCohomology X.X₁ 2) := hA2
  haveI : Finite (groupCohomology X.X₃ 2) := hC2
  obtain ⟨hB2, hcard⟩ := exact_cohomology_four_term_cardinality X
    (localFieldUnitValuationShortComplex_shortExact K L) 1 hC1 hB3
  refine ⟨hB2, ?_⟩
  change Nat.card (groupCohomology B 2) * Nat.card (groupCohomology A 3) =
    Nat.card (groupCohomology A 2) * Nat.card (groupCohomology C 2) at hcard
  rw [hA32, hCcard, ← Nat.card_eq_fintype_card (α := Gal(L/K))] at hcard
  apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := groupCohomology A 2))
  exact (mul_comm _ _).trans hcard

end
end Dubon2026
