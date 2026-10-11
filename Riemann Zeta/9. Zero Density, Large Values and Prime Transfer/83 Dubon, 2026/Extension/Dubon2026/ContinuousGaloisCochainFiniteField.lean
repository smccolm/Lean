import Dubon2026.ContinuousGaloisCocycleFiniteField

/-! # Actual finite coefficient fields and periods of continuous Galois cochains -/

namespace Dubon2026
noncomputable section

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace (Rep.ofAlgebraAutOnUnits K Ω)]
  [DiscreteTopology (Rep.ofAlgebraAutOnUnits K Ω)]

/-- Every original continuous unit cochain has finite coefficient values and
actual finite Galois periods in a field containing any prescribed finite
Galois stage. No cocycle identity is required for this descent of witnesses. -/
theorem continuousGaloisUnitCochain_exists_finiteField
    (E : FiniteGaloisIntermediateField K Ω)
    (b : C(Gal(Ω/K), Rep.ofAlgebraAutOnUnits K Ω)) :
    ∃ F : FiniteGaloisIntermediateField K Ω, E ≤ F ∧
      (∀ g : Gal(Ω/K), ((Additive.toMul (Rep.toAdditive (b g)) : Ωˣ) : Ω) ∈ F.toIntermediateField) ∧
      (∀ g u : Gal(Ω/K), AlgEquiv.restrictNormalHom F u = 1 → b (g * u) = b g) := by
  have hr : (Set.range b).Finite := (isCompact_range b.continuous).finite_of_discrete
  let s : Set Ω := (fun v : Rep.ofAlgebraAutOnUnits K Ω =>
    ((Additive.toMul (Rep.toAdditive v) : Ωˣ) : Ω)) '' Set.range b
  have hs : s.Finite := hr.image _
  letI := hs.fintype
  let V := FiniteGaloisIntermediateField.adjoin K s
  obtain ⟨U, hU⟩ := compactDiscreteFunction_exists_openNormalPeriods b
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
  let W : FiniteGaloisIntermediateField K Ω := {
    toIntermediateField := L
    finiteDimensional := inferInstance
    isGalois := inferInstance }
  let F := E ⊔ (V ⊔ W)
  refine ⟨F, le_sup_left, ?_, ?_⟩
  · intro g
    have hv : ((Additive.toMul (Rep.toAdditive (b g)) : Ωˣ) : Ω) ∈ V.toIntermediateField :=
      FiniteGaloisIntermediateField.subset_adjoin K s ⟨b g, ⟨g, rfl⟩, rfl⟩
    exact (show V.toIntermediateField ≤ F.toIntermediateField from
      le_trans le_sup_left le_sup_right) hv
  · intro g u hu
    have hmem : u ∈ F.toIntermediateField.fixingSubgroup :=
      (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff u F).mpr hu
    have hle : W.toIntermediateField ≤ F.toIntermediateField :=
      le_trans le_sup_right le_sup_right
    have hw : u ∈ L.fixingSubgroup := IntermediateField.fixingSubgroup_le hle hmem
    rw [hfix] at hw
    exact hU g u hw

end
end Dubon2026
