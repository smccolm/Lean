import Dubon2026.CosetTraceRepresentativeChange
import Dubon2026.ContinuousCohomologyCorestriction

/-! # Continuous transfer is independent of its original coset representatives

The witness is an actual continuous one-cochain, not merely an algebraic
coboundary. This is the representative comparison needed before the
arithmetic local/global transfer comparison for DUB-17.
-/

namespace Dubon2026
noncomputable section
open scoped BigOperators

variable {R G : Type} [CommRing R] [Group G]
  [TopologicalSpace R] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Rep R G) [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul R A]
  (hA : Continuous (fun z : G × A => A.ρ z.1 z.2))
  (S : Subgroup G) [Fintype (G ⧸ S)] (hS : IsOpen (S : Set G))

include hA hS in
/-- Every change of representatives has a continuous comparison cochain
because the original open subgroup has a discrete finite coset space. -/
theorem cosetRepresentativeHomotopy_continuous (a : G ⧸ S → S)
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype)) :
    Continuous (cosetRepresentativeHomotopy A S a c.val) := by
  letI : DiscreteTopology (G ⧸ S) := QuotientGroup.discreteTopology hS
  have hout : Continuous (fun q : G ⧸ S => q.out) := continuous_of_discreteTopology
  have ha : Continuous a := continuous_of_discreteTopology
  apply continuous_finsetSum
  intro q _
  have haq : Continuous (fun g : G => a (g • q)) :=
    ha.comp (continuous_id.smul continuous_const)
  have ht : Continuous (fun g : G => cosetTransition S g q) :=
    (cosetTransition_continuous S hS).comp (continuous_id.prodMk continuous_const)
  have hchange : Continuous (fun g : G => changedCosetTransition S a g q) :=
    haq.inv.mul ht |>.mul continuous_const
  exact hA.comp ((hout.comp (continuous_id.smul continuous_const)).prodMk
    ((c.property.comp (haq.prodMk hchange)).sub
      (c.property.comp (ht.prodMk continuous_const))))

/-- The changed finite coset sum is a genuine cocycle for the original
group and action, proved by the explicit representative coboundary. -/
def changedCosetTraceCocycle (a : G ⧸ S → S)
    (c : groupCohomology.cocycles₂ (restrictedCoefficientRep A S.subtype)) :
    groupCohomology.cocycles₂ A :=
  ⟨fun z => ∑ q : G ⧸ S, changedCosetTraceTwoTerm A S a c z.1 z.2 q, by
    have he := eq_add_of_sub_eq (changedCosetTraceTwo_sub A S a c)
    rw [he]
    exact (groupCohomology.cocycles₂ A).add_mem
      (groupCohomology.d₁₂_apply_mem_cocycles₂ (A := A) _)
      (cosetTraceTwo_mem_cocycles A S c)⟩

include hA hS in
/-- The original changed trace is jointly continuous; its explicit
coboundary comparison retains a continuous witness. -/
theorem changedCosetTraceCocycle_continuous (a : G ⧸ S → S)
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype)) :
    Continuous (changedCosetTraceCocycle A S a c.val : G × G → A) := by
  change Continuous (fun z : G × G => ∑ q : G ⧸ S, changedCosetTraceTwoTerm A S a c.val z.1 z.2 q)
  rw [eq_add_of_sub_eq (changedCosetTraceTwo_sub A S a c.val)]
  exact (representationOneDifferential_continuous A hA _
    (cosetRepresentativeHomotopy_continuous A hA S hS a c)).add
    (cosetTraceTwo_continuous A hA S hS c.val c.property)

/-- The actual continuous cocycle obtained from the changed representatives. -/
def continuousChangedCosetTraceCocycle (a : G ⧸ S → S)
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype)) :
    continuousRepresentationCocyclesTwo A :=
  ⟨changedCosetTraceCocycle A S a c.val, changedCosetTraceCocycle_continuous A hA S hS a c⟩

/-- The original continuous corestriction class is unchanged by arbitrary
changes of the coset representatives inside the original subgroup. -/
theorem continuousChangedCosetTraceCocycle_class (a : G ⧸ S → S)
    (c : continuousRepresentationCocyclesTwo (restrictedCoefficientRep A S.subtype)) :
    (Submodule.Quotient.mk (continuousChangedCosetTraceCocycle A hA S hS a c) :
      ContinuousRepresentationH2 A hA) =
      continuousRepresentationH2Corestriction A hA S hS (Submodule.Quotient.mk c) := by
  rw [continuousRepresentationH2Corestriction_mk]
  apply (continuousRepresentationH2_eq_iff A hA _ _).mpr
  refine ⟨⟨cosetRepresentativeHomotopy A S a c.val,
    cosetRepresentativeHomotopy_continuous A hA S hS a c⟩, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact (changedCosetTraceTwo_sub A S a c.val).symm

end
end Dubon2026
