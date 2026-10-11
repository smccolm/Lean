import Dubon2026.ContinuousTwoCocyclePeriodInvariants
import Dubon2026.ContinuousGaloisFiniteFactors
import Dubon2026.ContinuousFiniteFieldGaloisUnitH2
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.FieldTheory.Galois.Profinite

/-! # An actual finite Galois coefficient field for an original continuous unit two-cocycle -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- The original jointly continuous nontrivial Galois unit two-cocycle has all its original
values in an actual finite Galois subfield. It is constant on the actual fibers
of restriction to that same field. Normal periods and fixed-field duality
construct this field without assuming that the cocycle is a character. -/
theorem continuousGaloisUnitTwoCocycle_exists_finiteField
    (c : continuousRepresentationCocyclesTwo (Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω,
      (∀ g h : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (c.val (g, h))) : Ωˣ) : Ω) ∈ F.toIntermediateField) ∧
      (∀ g h u v : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 →
        AlgEquiv.restrictNormalHom F v = 1 → c.val (g * u, h * v) = c.val (g, h)) := by
  obtain ⟨U, hperiod, hfixed⟩ := continuousTwoCocycle_exists_openNormal_periods_and_fixed
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
  · intro g h
    apply (IntermediateField.mem_fixedField_iff _ _).mpr
    intro u hu
    exact congrArg (fun v : Rep.ofAlgebraAutOnUnits K Ω =>
      ((Additive.toMul (Rep.toAdditive v) : Ωˣ) : Ω)) (hfixed u hu g h)
  · intro g h u v hu hv
    have hmem : u ∈ L.fixingSubgroup :=
      (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff u F).mpr hu
    rw [hfix] at hmem
    have hmemv : v ∈ L.fixingSubgroup :=
      (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff v F).mpr hv
    rw [hfix] at hmemv
    exact hperiod g h u v hmem hmemv

end
end Dubon2026
