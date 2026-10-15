import Dubon2026.ContinuousGaloisCochainFiniteField

/-! # Finite Galois periods above an existing coefficient stage

This is the period part of the existing unit-cochain descent, applied to
the original discrete class-quotient coefficients. It supplies the finite
Galois stage needed to use class H1 vanishing in the arithmetic colimit.
-/

namespace Dubon2026
noncomputable section

variable {K Ω X : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace X] [DiscreteTopology X]

/-- A continuous discrete-valued function on the original Galois group has finite Galois periods above any prescribed finite coefficient stage. -/
theorem continuousGaloisFunction_exists_finite_periods
    (E : FiniteGaloisIntermediateField K Ω) (b : C(Gal(Ω/K), X)) :
    ∃ F : FiniteGaloisIntermediateField K Ω, E ≤ F ∧
      ∀ g u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → b (g * u) = b g := by
  obtain ⟨U, hU⟩ := compactDiscreteFunction_exists_openNormalPeriods b
  let H : ClosedSubgroup Gal(Ω/K) := ⟨U.toSubgroup, U.isClosed⟩
  let L := IntermediateField.fixedField U.toSubgroup
  have hfix : L.fixingSubgroup = U.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField H
  letI : FiniteDimensional K L := by
    apply (InfiniteGalois.isOpen_iff_finite L).mp
    simpa only [hfix] using U.isOpen
  letI : IsGalois K L := by
    apply (InfiniteGalois.normal_iff_isGalois L).mp
    rw [hfix]
    infer_instance
  let W : FiniteGaloisIntermediateField K Ω := {
    toIntermediateField := L
    finiteDimensional := inferInstance
    isGalois := inferInstance }
  let F := E ⊔ W
  refine ⟨F, le_sup_left, ?_⟩
  intro g u hu
  have hmem : u ∈ F.toIntermediateField.fixingSubgroup :=
    (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff u F).mpr hu
  have hle : W.toIntermediateField ≤ F.toIntermediateField := le_sup_right
  have hw : u ∈ L.fixingSubgroup := IntermediateField.fixingSubgroup_le hle hmem
  rw [hfix] at hw
  exact hU g u hw

end
end Dubon2026
