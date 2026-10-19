import Dubon2026.ContinuousUnramifiedFiniteInflation
import Dubon2026.FiniteCyclicInflationDimension
import Mathlib.RingTheory.Finiteness.Basic

/-! DUB-17's unramified local dimension bound. Native continuous classes
are covered by literal finite inflation images; finite generation puts
the entire inertia kernel in one such image. Only the actual arithmetic
cyclicity remains to instantiate this bound at the original local group. -/

namespace Dubon2026
noncomputable section
open CategoryTheory

/-- Smaller normal subgroups have larger original first inflation images. -/
theorem firstInflation_range_antitone
    {K G : Type} [Field K] [Group G] (A : Rep K G)
    (N S : Subgroup G) [N.Normal] [S.Normal] (hNS : N ≤ S) :
    (groupCohomology.H1InfRes A S).f.hom.range ≤
      (groupCohomology.H1InfRes A N).f.hom.range := by
  rw [(groupCohomology.H1InfRes_exact A S).moduleCat_range_eq_ker,
    (groupCohomology.H1InfRes_exact A N).moduleCat_range_eq_ker]
  intro x hx
  induction x using groupCohomology.H1_induction_on with
  | h c =>
    change groupCohomology.map S.subtype (𝟙 _) 1 (groupCohomology.H1π A c) = 0 at hx
    change groupCohomology.map N.subtype (𝟙 _) 1 (groupCohomology.H1π A c) = 0
    rw [groupCohomology.H1π_comp_map_apply] at hx ⊢
    obtain ⟨m, hm⟩ := (groupCohomology.H1π_eq_zero_iff _).mp hx
    apply (groupCohomology.H1π_eq_zero_iff _).mpr
    refine ⟨m, funext fun n => ?_⟩
    exact congrFun hm ⟨n.val, hNS n.property⟩

variable {K G : Type} [Field K] [Group G]
  [TopologicalSpace K] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (A : Rep K G) [TopologicalSpace A] [DiscreteTopology A] [ContinuousSMul K A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (I : Subgroup G) [I.Normal]

/-- A finite-dimensional original continuous inertia kernel fits inside
one original finite inflation image; no finite-stage class is supplied. -/
theorem continuous_unramified_kernel_le_finite_inflation
    [FiniteDimensional K (ContinuousRepresentationH1 A hA)] :
    ∃ U : OpenNormalSubgroup G,
      ((continuousRepresentationH1Restriction A hA I.subtype continuous_subtype_val).ker.map
        (continuousH1ToAlgebraic A hA)) ≤
          (groupCohomology.H1InfRes A (I ⊔ U.toSubgroup)).f.hom.range := by
  let P := (continuousRepresentationH1Restriction A hA I.subtype continuous_subtype_val).ker
  let L := (continuousH1ToAlgebraic A hA).comp P.subtype
  let T (U : OpenNormalSubgroup G) : Submodule K (groupCohomology A 1) :=
    (groupCohomology.H1InfRes A (I ⊔ U.toSubgroup)).f.hom.range
  have hd : DirectedOn (· ≤ ·) (Set.range T) := by
    rintro _ ⟨U, rfl⟩ _ ⟨V, rfl⟩
    refine ⟨T (U ⊓ V), ⟨U ⊓ V, rfl⟩, ?_, ?_⟩
    · exact firstInflation_range_antitone A _ _ (sup_le_sup_left inf_le_left I)
    · exact firstInflation_range_antitone A _ _ (sup_le_sup_left inf_le_right I)
  have hcover : L.range ≤ sSup (Set.range T) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨U, hU⟩ := continuous_unramified_class_mem_finite_inflation A hA I x.val x.property
    exact (show T U ≤ sSup (Set.range T) from le_sSup ⟨U, rfl⟩) hU
  have hc := (Submodule.fg_iff_compact L.range).mp (Submodule.fg_range L)
  obtain ⟨U₀, _⟩ := continuous_unramified_class_mem_finite_inflation A hA I 0 (map_zero _)
  obtain ⟨_, ⟨U, rfl⟩, hU⟩ :=
    (CompleteLattice.isCompactElement_iff_le_of_directed_sSup_le _ L.range).mp hc
      (Set.range T) ⟨T U₀, ⟨U₀, rfl⟩⟩ hd hcover
  refine ⟨U, ?_⟩
  simpa only [L, LinearMap.range_comp, Submodule.range_subtype] using hU

/-- Cyclicity of the actual finite inertia quotients gives the upper
bound for the original continuous unramified H1 condition. -/
theorem continuous_unramified_finrank_le_invariants
    [FiniteDimensional K A] [FiniteDimensional K (ContinuousRepresentationH1 A hA)]
    (hcyclic : ∀ U : OpenNormalSubgroup G, IsCyclic (G ⧸ (I ⊔ U.toSubgroup))) :
    Module.finrank K (continuousRepresentationH1Restriction A hA
      I.subtype continuous_subtype_val).ker ≤ Module.finrank K A.ρ.invariants := by
  let P := (continuousRepresentationH1Restriction A hA I.subtype continuous_subtype_val).ker
  obtain ⟨U, hU⟩ := continuous_unramified_kernel_le_finite_inflation A hA I
  let N := I ⊔ U.toSubgroup
  letI : Finite (G ⧸ N) := Subgroup.quotient_finite_of_isOpen N
    (Subgroup.isOpen_mono le_sup_right U.isOpen)
  letI : Fintype (G ⧸ N) := Fintype.ofFinite _
  letI : IsCyclic (G ⧸ N) := hcyclic U
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := G ⧸ N)
  let J : P →ₗ[K] (groupCohomology.H1InfRes A N).f.hom.range :=
    ((continuousH1ToAlgebraic A hA).comp P.subtype).codRestrict _
      (fun x => hU ⟨x.val, x.property, rfl⟩)
  have hJ : Function.Injective J := by
    intro x y h
    apply Subtype.ext
    exact continuousH1ToAlgebraic_injective A hA (congrArg Subtype.val h)
  letI : FiniteDimensional K (A.quotientToInvariants N) :=
    inferInstanceAs (FiniteDimensional K (Representation.invariants (A.ρ.comp N.subtype)))
  haveI : FiniteDimensional K (groupCohomology (A.quotientToInvariants N) 1) := by
    exact Module.Finite.of_surjective (groupCohomology.H1π (A.quotientToInvariants N)).hom
      ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  haveI : Module.Finite K (groupCohomology.H1InfRes A N).X₁ := by
    change Module.Finite K (groupCohomology (A.quotientToInvariants N) 1)
    infer_instance
  haveI : Module.Finite K (groupCohomology.H1InfRes A N).f.hom.range :=
    Module.Finite.range (groupCohomology.H1InfRes A N).f.hom
  exact (LinearMap.finrank_le_finrank_of_injective hJ).trans
    (finite_cyclic_firstInflation_finrank_le A N g hg)

end
end Dubon2026
