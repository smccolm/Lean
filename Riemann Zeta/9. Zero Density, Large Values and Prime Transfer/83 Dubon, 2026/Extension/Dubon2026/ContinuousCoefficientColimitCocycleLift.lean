import Dubon2026.CompactCoefficientColimitLift
import Dubon2026.ContinuousRepresentationCocycles

/-! # Original continuous one-cocycles lift to a coefficient stage

Compactness makes the original cochain and its cocycle defect finite.
The actual direct-limit relations kill all defects at one larger stage.
This is the needed descent edge from arithmetic class-colimit H1 to the
already proved finite class-quotient H1; finite Galois factorization remains
the next step, without a new general cohomology-colimit framework.
-/

namespace Dubon2026
noncomputable section
attribute [local instance 1100] Rep.hV2

variable {R G ι : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [Preorder ι] [DecidableEq ι] [Nonempty ι] [IsDirectedOrder ι]
  (A : ι → Rep.{0} R G) (f : ∀ i j, i ≤ j → (A i ⟶ A j))
  [DirectedSystem (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap)]
  [∀ i, TopologicalSpace (A i)] [∀ i, DiscreteTopology (A i)]
  [TopologicalSpace (coefficientRepresentationColimit A f)]
  [DiscreteTopology (coefficientRepresentationColimit A f)]

/-- The original coefficient structure used in this comparison. -/
local instance colimitCocycleStageSMul (i : ι) : @ContinuousSMul R (A i) (A i).hV2.toSMul
    inferInstance inferInstance := by
  letI : SMul R (A i) := (A i).hV2.toSMul
  exact ⟨continuous_of_discreteTopology⟩
/-- The original coefficient structure used in this comparison. -/
local instance colimitCocycleTargetSMul : @ContinuousSMul R (coefficientRepresentationColimit A f)
    (coefficientRepresentationColimit A f).hV2.toSMul inferInstance inferInstance := by
  letI : SMul R (coefficientRepresentationColimit A f) :=
    (coefficientRepresentationColimit A f).hV2.toSMul
  exact ⟨continuous_of_discreteTopology⟩

/-- Every original continuous one-cocycle in the discrete coefficient colimit is the literal image of a continuous cocycle at one stage. -/
theorem continuousCoefficientColimitOneCocycle_exists_lift
    (hA : ∀ i, Continuous (fun z : G × A i => (A i).ρ z.1 z.2))
    (c : continuousRepresentationCocyclesOne (coefficientRepresentationColimit A f)) :
    ∃ i, ∃ b : continuousRepresentationCocyclesOne (A i),
      ∀ g, (coefficientRepresentationColimitOf A f i).hom (b.val g) = c.val g := by
  classical
  have hc : Continuous (fun g : G => c.val g) := c.property
  obtain ⟨i, b, hb, hbc⟩ := @compactCoefficientColimit_exists_lift R ι
    _ _ _ _ _ (fun i => A i) (fun i => (A i).hV1) (fun i => (A i).hV2)
    (fun i j h => (f i j h).hom.toLinearMap)
    (inferInstance : TopologicalSpace (coefficientRepresentationColimit A f))
    (inferInstance : DiscreteTopology (coefficientRepresentationColimit A f))
    (fun i => (inferInstance : TopologicalSpace (A i)))
    (fun i => (inferInstance : DiscreteTopology (A i))) G
    (inferInstance : TopologicalSpace G) (inferInstance : CompactSpace G)
    (fun g => c.val g) hc
  have hbc' (g : G) : (coefficientRepresentationColimitOf A f i).hom (b g) = c.val g := hbc g
  let d : G × G → A i := fun z => (A i).ρ z.1 (b z.2) - b (z.1 * z.2) + b z.1
  have hd : Continuous d := ((hA i).comp (continuous_fst.prodMk (hb.comp continuous_snd))).sub
    (hb.comp (continuous_fst.mul continuous_snd)) |>.add (hb.comp continuous_fst)
  have hr : (Set.range d).Finite := (isCompact_range hd).finite_of_discrete
  have hz (x : A i) (hx : x ∈ hr.toFinset) : Module.DirectLimit.of R ι (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i x = 0 := by
    obtain ⟨⟨g, h⟩, rfl⟩ := hr.mem_toFinset.mp hx
    change (coefficientRepresentationColimitOf A f i).hom
      ((A i).ρ g (b h) - b (g * h) + b g) = 0
    rw [map_add, map_sub, Rep.hom_comm_apply]
    rw [hbc', hbc', hbc']
    exact (groupCohomology.mem_cocycles₁_def _).mp c.val.property g h
  obtain ⟨j, hij, hj⟩ := coefficientColimit_finite_zero_detected (fun i => A i) (fun i j h => (f i j h).hom.toLinearMap) i hr.toFinset hz
  let b' : G → A j := fun g => (f i j hij).hom (b g)
  have hb' : b' ∈ groupCohomology.cocycles₁ (A j) := by
    apply (groupCohomology.mem_cocycles₁_def _).mpr
    intro g h
    have he := hj (d (g, h)) (hr.mem_toFinset.mpr (Set.mem_range_self (g, h)))
    change (f i j hij).hom ((A i).ρ g (b h) - b (g * h) + b g) = 0 at he
    rw [map_add, map_sub, Rep.hom_comm_apply] at he
    exact he
  have hbcont : Continuous b' :=
    (continuous_of_discreteTopology : Continuous (fun z : A i => (f i j hij).hom z)).comp hb
  refine ⟨j, ⟨⟨b', hb'⟩, hbcont⟩, ?_⟩
  intro g
  exact (Module.DirectLimit.of_f (f := fun i j h => (f i j h).hom.toLinearMap)
    (hij := hij) (x := b g)).trans (hbc g)

end
end Dubon2026
