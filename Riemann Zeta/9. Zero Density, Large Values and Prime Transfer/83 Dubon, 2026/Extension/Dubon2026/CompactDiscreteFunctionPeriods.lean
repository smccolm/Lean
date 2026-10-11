import Mathlib.Topology.CompactOpen
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-! # Actual open periods of continuous discrete-valued functions on compact groups -/

namespace Dubon2026
noncomputable section

/-- A continuous function from a compact space to a discrete space is an open
point of the genuine compact-open function space. Its finite range gives the cover. -/
theorem compactDiscreteContinuousMap_singleton_open
    {X Y : Type} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] (f : C(X, Y)) :
    IsOpen ({f} : Set C(X, Y)) := by
  have hr : (Set.range f).Finite := (isCompact_range f.continuous).finite_of_discrete
  have he : ({f} : Set C(X, Y)) =
      ⋂ y ∈ Set.range f, {g : C(X, Y) | Set.MapsTo g (f ⁻¹' {y}) {y}} := by
    ext g
    simp only [Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · rintro rfl y _ x hx
      exact hx
    · intro hg
      apply ContinuousMap.ext
      intro x
      exact hg (f x) ⟨x, rfl⟩ rfl
  rw [he]
  apply hr.isOpen_biInter
  intro y _
  exact ContinuousMap.isOpen_setOf_mapsTo
    ((isClosed_singleton.preimage f.continuous).isCompact) (isOpen_discrete _)

variable {G A : Type} [Group G]

/-- The actual right periods of the original function form a subgroup. -/
def functionRightPeriodSubgroup (f : G → A) : Subgroup G where
  carrier := {u | ∀ g, f (g * u) = f g}
  one_mem' := by intro g; rw [mul_one]
  mul_mem' := by
    intro u v hu hv g
    rw [← mul_assoc, hv, hu]
  inv_mem' := by
    intro u hu g
    have he := hu (g * u⁻¹)
    rw [inv_mul_cancel_right] at he
    exact he.symm

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TopologicalSpace A] [DiscreteTopology A]

/-- Compact-open currying proves that the original function's exact period
subgroup is open. No period or finite-quotient factorization is assumed. -/
theorem functionRightPeriodSubgroup_isOpen (f : C(G, A)) :
    IsOpen (functionRightPeriodSubgroup f : Set G) := by
  let shift : G → C(G, A) := fun u =>
    ⟨fun g => f (g * u), f.continuous.comp (continuous_id.mul continuous_const)⟩
  have hc : Continuous shift :=
    ContinuousMap.continuous_of_continuous_uncurry shift
      (f.continuous.comp (continuous_snd.mul continuous_fst))
  have he : (functionRightPeriodSubgroup f : Set G) = shift ⁻¹' {f} := by
    ext u
    change (∀ g, f (g * u) = f g) ↔ shift u = f
    constructor
    · intro hu
      exact ContinuousMap.ext hu
    · intro hu g
      exact DFunLike.congr_fun hu g
  rw [he]
  exact (compactDiscreteContinuousMap_singleton_open f).preimage hc

/-- The pinned open-normal-subgroup theorem gives a genuine common open normal
period subgroup for the same original continuous function. -/
theorem compactDiscreteFunction_exists_openNormalPeriods (f : C(G, A)) :
    ∃ U : OpenNormalSubgroup G, ∀ g u, u ∈ U → f (g * u) = f g := by
  let H : OpenSubgroup G :=
    ⟨functionRightPeriodSubgroup f, functionRightPeriodSubgroup_isOpen f⟩
  have hcl : IsClopen (H : Set G) := ⟨H.isClosed, H.isOpen⟩
  obtain ⟨U, hU⟩ :=
    IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one hcl H.one_mem
  exact ⟨U, fun g u hu => hU hu g⟩

end
end Dubon2026
