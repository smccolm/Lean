import Dubon2026.ContinuousCocyclePeriodInvariants
import Dubon2026.ContinuousGaloisFiniteFactors
import Dubon2026.ContinuousFiniteFieldGaloisUnitH2
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.FieldTheory.Galois.Profinite

/-! # An actual finite Galois coefficient field for an original continuous unit cocycle -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The original continuous nontrivial Galois unit cocycle has all its original
values in an actual finite Galois subfield. It is constant on the actual fibers
of restriction to that same field. Normal periods and fixed-field duality
construct this field without assuming that the cocycle is a character. -/
theorem continuousGaloisUnitCocycle_exists_finiteField
    (c : continuousRepresentationCocyclesOne (Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      (∀ g : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (c.val g)) : Ωˣ) : Ω) ∈
        F.toIntermediateField) ∧
      (∀ g u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
        c.val (g * u) = c.val g) := by
  obtain ⟨U, hperiod, hfixed⟩ := continuousCocycle_exists_openNormal_periods_and_fixed
    (Rep.ofAlgebraAutOnUnits K Ω) c
  let H : ClosedSubgroup Gal(Ω/K) := ⟨U.toSubgroup, U.isClosed⟩
  let L := IntermediateField.fixedField U.toSubgroup
  have hfix : L.fixingSubgroup = U.toSubgroup :=
    InfiniteGalois.fixingSubgroup_fixedField H
  letI : FiniteDimensional K L := by
    apply (InfiniteGalois.isOpen_iff_finite L).mp
    simpa only [hfix] using U.isOpen
  letI : IsGalois K L := by
    apply (InfiniteGalois.normal_iff_isGalois L).mp
    rw [hfix]
    infer_instance
  let F : FiniteGaloisIntermediateField K Ω := {
    toIntermediateField := L
    finiteDimensional := inferInstance
    isGalois := inferInstance }
  refine ⟨F, ?_, ?_⟩
  · intro g
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    intro u hu
    exact congrArg (fun v : Rep.ofAlgebraAutOnUnits K Ω =>
      ((Additive.toMul (Rep.toAdditive v) : Ωˣ) : Ω)) (hfixed u hu g)
  · intro g u hu
    have hmem : u ∈ L.fixingSubgroup :=
      (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff u F).mpr hu
    rw [hfix] at hmem
    exact hperiod g u hmem

end
end Dubon2026
