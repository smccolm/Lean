import Dubon2026.OpenSubgroupContinuousFunctionPeriods
import Dubon2026.ContinuousGaloisCochainFiniteField

/-! # Finite arithmetic periods for original open-subgroup cochains

Ambient open normal periods give an actual finite Galois field above any
prescribed coefficient stage. This keeps open-subgroup class cocycles in
the original arithmetic directed system for the remaining class H1 input
to DUB-17's global duality, without replacing the coefficient model.
-/

namespace Dubon2026
noncomputable section

variable {K Ω X : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace X] [DiscreteTopology X]

/-- An actual open-subgroup cochain has finite Galois periods above any original coefficient stage. -/
theorem continuousGaloisOpenSubgroupFunction_exists_finite_periods
    (H : OpenSubgroup Gal(Ω/K)) (E : FiniteGaloisIntermediateField K Ω) (b : C(H, X)) :
    ∃ F : FiniteGaloisIntermediateField K Ω, E ≤ F ∧
      ∀ g u : H, AlgEquiv.restrictNormalHom F (u : Gal(Ω/K)) = 1 → b (g * u) = b g := by
  obtain ⟨N, _, hN⟩ := openSubgroupContinuousFunction_exists_ambient_periods H b
  let C : ClosedSubgroup Gal(Ω/K) := ⟨N.toSubgroup, N.isClosed⟩
  let L := IntermediateField.fixedField N.toSubgroup
  have hfix : L.fixingSubgroup = N.toSubgroup := InfiniteGalois.fixingSubgroup_fixedField C
  letI : FiniteDimensional K L := by
    apply (InfiniteGalois.isOpen_iff_finite L).mp
    simpa only [hfix] using N.isOpen
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
  have hmem : (u : Gal(Ω/K)) ∈ F.toIntermediateField.fixingSubgroup :=
    (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff (u : Gal(Ω/K)) F).mpr hu
  have hle : W.toIntermediateField ≤ F.toIntermediateField := le_sup_right
  have hw : (u : Gal(Ω/K)) ∈ L.fixingSubgroup := IntermediateField.fixingSubgroup_le hle hmem
  rw [hfix] at hw
  exact hN g u hw

end
end Dubon2026
