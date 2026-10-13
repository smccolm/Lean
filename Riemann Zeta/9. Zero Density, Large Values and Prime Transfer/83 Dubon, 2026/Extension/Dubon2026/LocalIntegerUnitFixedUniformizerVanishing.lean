import Dubon2026.LocalFieldFixedUniformizerSection
import Dubon2026.LocalFieldIntegerUnitCohomologyOrders
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

/-! # An invariant uniformizer kills the required original integer-unit cohomology

The original valuation section makes its H0 connecting map zero. Hilbert90
makes the same map surjective onto integer-unit H1, so H1 vanishes. The
already proved equality of finite H1/H2 orders then kills H2. These are
exactly the outside-support inputs remaining in DUB-17's idele formula.
-/

namespace Dubon2026
noncomputable section
open CategoryTheory
open scoped ValuativeRel
variable (K L : Type) [Field K] [Field L] [Algebra K L] [IsGalois K L]
  [ValuativeRel K] [ValuativeRel L] [TopologicalSpace K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField K] [IsNonarchimedeanLocalField L]
  [(ValuativeRel.valuation K).HasExtension (ValuativeRel.valuation L)]

omit [IsGalois K L] in
/-- An actual invariant unit of order one forces the original integer-unit H1 to vanish. -/
theorem localIntegerUnit_first_zero_of_fixed_uniformizer
    (π : Lˣ) (hfixed : ∀ σ : Gal(L/K), σ • π = π)
    (hπ : localFieldUnitOrder L (Additive.ofMul π) = 1) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ) 1) := by
  haveI : FiniteDimensional K L := localField_field_module_finite
  letI := localFieldIntegerUnitMulDistribMulAction K L
  let X := localFieldUnitValuationShortComplex K L
  let hX := localFieldUnitValuationShortComplex_shortExact K L
  let C := groupCohomology.functor ℤ Gal(L/K) 0
  let s := localFieldFixedUniformizerSection K L π hfixed
  have hs : C.map s ≫ C.map X.g = 𝟙 (C.obj X.X₃) := by
    rw [← C.map_comp, localFieldFixedUniformizerSection_comp K L π hfixed hπ]
    exact C.map_id _
  have hz : C.map X.g ≫ groupCohomology.δ hX 0 1 rfl = 0 :=
    (groupCohomology.mapShortComplex₃ hX (i := 0) rfl).zero
  have hb : Limits.IsZero (groupCohomology X.X₂ 1) := by
    change Limits.IsZero (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 1)
    exact ModuleCat.isZero_iff_subsingleton.mpr inferInstance
  haveI : Epi (groupCohomology.δ hX 0 1 rfl) := groupCohomology.epi_δ_of_isZero hX 0 hb
  apply Limits.IsZero.of_epi_eq_zero (groupCohomology.δ hX 0 1 rfl)
  calc
    groupCohomology.δ hX 0 1 rfl = (C.map s ≫ C.map X.g) ≫ groupCohomology.δ hX 0 1 rfl := by
      rw [hs]
      exact (Category.id_comp _).symm
    _ = C.map s ≫ (C.map X.g ≫ groupCohomology.δ hX 0 1 rfl) := Category.assoc _ _ _
    _ = C.map s ≫ 0 := congrArg (fun t => C.map s ≫ t) hz
    _ = 0 := Limits.comp_zero

/-- The same actual invariant uniformizer kills both required original cyclic integer-unit H1 and H2. -/
theorem localIntegerUnit_first_second_zero_of_fixed_uniformizer
    [IsCyclic Gal(L/K)] (π : Lˣ) (hfixed : ∀ σ : Gal(L/K), σ • π = π)
    (hπ : localFieldUnitOrder L (Additive.ofMul π) = 1) :
    letI := localFieldIntegerUnitMulDistribMulAction K L
    Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ) 1) ∧
      Limits.IsZero (groupCohomology (Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ) 2) := by
  letI := localFieldIntegerUnitMulDistribMulAction K L
  let A := Rep.ofMulDistribMulAction Gal(L/K) 𝒪[L]ˣ
  have hz := localIntegerUnit_first_zero_of_fixed_uniformizer K L π hfixed hπ
  haveI : Subsingleton (groupCohomology A 1) := ModuleCat.isZero_iff_subsingleton.mp hz
  obtain ⟨q, hq⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
  have horders := localField_integer_unit_first_second_cohomology_orders K L q hq
  have hcard : Nat.card (groupCohomology A 2) = 1 := horders.2.2.symm.trans Nat.card_unique
  haveI : Subsingleton (groupCohomology A 2) := (Nat.card_eq_one_iff_unique.mp hcard).1
  exact ⟨hz, ModuleCat.isZero_iff_subsingleton.mpr inferInstance⟩

end
end Dubon2026
