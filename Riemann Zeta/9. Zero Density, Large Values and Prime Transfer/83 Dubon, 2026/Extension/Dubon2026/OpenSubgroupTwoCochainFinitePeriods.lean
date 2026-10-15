import Dubon2026.CompactDiscreteFiniteQuotient
import Dubon2026.ContinuousGaloisCochainFiniteField

/-! # Actual finite Galois periods of open-subgroup two-cochains

The existing common-period theorem on a compact group applies to the
original open subgroup. Its open image contains an ambient open normal
subgroup, hence a finite Galois kernel above the specified stage. This
is the finite-descent input for original class H2 invariant maps in
DUB-17's P-class formation, without higher-degree cochain machinery.
-/

namespace Dubon2026
noncomputable section

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TopologicalSpace A] [DiscreteTopology A]

/-- An actual open-subgroup two-cochain has common ambient normal periods in both variables. -/
theorem openSubgroupTwoFunction_exists_ambient_periods
    (H : OpenSubgroup G) (f : C(H × H, A)) :
    ∃ N : OpenNormalSubgroup G, N.toSubgroup ≤ H.toSubgroup ∧
      ∀ g h u v : H, (u : G) ∈ N → (v : G) ∈ N → f (g * u, h * v) = f (g, h) := by
  letI : IsTopologicalGroup H := inferInstanceAs (IsTopologicalGroup H.toSubgroup)
  letI : CompactSpace H := isCompact_iff_compactSpace.mp H.isClosed.isCompact
  obtain ⟨P, hP⟩ := compactDiscreteTwoFunction_exists_commonPeriods f
  let J : OpenSubgroup G := ⟨P.toSubgroup.map H.toSubgroup.subtype, by
    change IsOpen ((P.toSubgroup.map H.toSubgroup.subtype : Subgroup G) : Set G)
    rw [Subgroup.coe_map]
    exact H.isOpen.isOpenMap_subtype_val _ P.isOpen⟩
  obtain ⟨N, hN⟩ := IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one
    (show IsClopen (J : Set G) from ⟨J.isClosed, J.isOpen⟩) J.one_mem
  have hNP (u : H) (hu : (u : G) ∈ N) : u ∈ P := by
    obtain ⟨v, hv, hvu⟩ := hN hu
    have he : v = u := Subtype.ext hvu
    exact he ▸ hv
  refine ⟨N, ?_, fun g h u v hu hv => hP g h u v (hNP u hu) (hNP v hv)⟩
  intro u hu
  obtain ⟨v, _, rfl⟩ := hN hu
  exact v.property

variable {K Ω X : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
  [TopologicalSpace X] [DiscreteTopology X]

/-- Every original open-subgroup two-cochain has finite Galois periods above the given actual coefficient stage. -/
theorem continuousGaloisOpenSubgroupTwoFunction_exists_finite_periods
    (H : OpenSubgroup Gal(Ω/K)) (E : FiniteGaloisIntermediateField K Ω) (b : C(H × H, X)) :
    ∃ F : FiniteGaloisIntermediateField K Ω, E ≤ F ∧
      ∀ g h u v : H, AlgEquiv.restrictNormalHom F (u : Gal(Ω/K)) = 1 →
        AlgEquiv.restrictNormalHom F (v : Gal(Ω/K)) = 1 → b (g * u, h * v) = b (g, h) := by
  have hPeriods := openSubgroupTwoFunction_exists_ambient_periods H b
  obtain ⟨N, _, hN⟩ := hPeriods
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
  have hker (u : H) (hu : AlgEquiv.restrictNormalHom F (u : Gal(Ω/K)) = 1) : (u : Gal(Ω/K)) ∈ N := by
    have hmem : (u : Gal(Ω/K)) ∈ F.toIntermediateField.fixingSubgroup :=
      (FiniteGaloisIntermediateField.mem_fixingSubgroup_iff (u : Gal(Ω/K)) F).mpr hu
    have hle : W.toIntermediateField ≤ F.toIntermediateField := le_sup_right
    have hw : (u : Gal(Ω/K)) ∈ L.fixingSubgroup := IntermediateField.fixingSubgroup_le hle hmem
    rwa [hfix] at hw
  exact ⟨F, le_sup_left, fun g h u v hu hv => hN g h u v (hker u hu) (hker v hv)⟩

end
end Dubon2026
